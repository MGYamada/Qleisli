import QleisliKernel.Qirf.RuntimeCertifiedComputed
import QleisliKernel.Qirf.RuntimePureInterval
import QleisliKernel.Raw.Workspace
import QleisliKernel.Raw.WorkspaceResources

/-! Read the workspace body and logical map from the checked original source.
Bind them to the literal Raw interval and its ordered live ports.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeWorkspace
open QleisliKernel Finite SourceTypes SourceRuntimeContext
open Semantics.Exact

structure Original {sources caller} (event : WorkspaceEvent sources caller)
    (events : List (Event sources caller)) where
  layout : Semantics.FiniteCarrier.Layout
  layoutRead : RuntimeInterval.Computed (FiniteCarrier.read event.input.basis) layout
  fullCarrier : layout.labels = List.range (2^layout.bits)
  logical : RuntimeComputedUse.Action
  logicalRead : RuntimeInterval.Computed
    (RuntimeCertifiedComputed.logicalAction event.logical layout.labels.length) logical
  identity : Matrix
  identityRead : RuntimeInterval.Computed
    (lift (arithmetic (Exact.Matrix.identity (2^(layout.bits+1))))) identity
  body : RuntimeComputedUse.Action
  bodyRead : RuntimeInterval.Computed
    (RuntimeComputedUse.sourceAction sources true (SourceTrace.sourceFuel sources)
      [event.input,event.scratch] [event.dataOut,event.scratchOut] identity events) body

def readOriginal {sources caller} (event : WorkspaceEvent sources caller)
    (events : List (Event sources caller)) : WorkM (Original event events) := do
  let layout ← NaturalAffine.witness (FiniteCarrier.read event.input.basis)
  guard (layout.val.bits < 6) .limit
  if full : layout.val.labels = List.range (2^layout.val.bits) then
    let logical ← NaturalAffine.witness
      (RuntimeCertifiedComputed.logicalAction event.logical layout.val.labels.length)
    exactWork (Exact.charge ((2^(layout.val.bits+1)+1)^2))
    let identity ← NaturalAffine.witness (lift (arithmetic (Exact.Matrix.identity (2^(layout.val.bits+1)))))
    let body ← NaturalAffine.witness (RuntimeComputedUse.sourceAction sources true (SourceTrace.sourceFuel sources)
      [event.input,event.scratch] [event.dataOut,event.scratchOut] identity.val events)
    return ⟨layout.val,by with_reducible exact layout.property,full,
      logical.val,by with_reducible exact logical.property,
      identity.val,by with_reducible exact identity.property,body.val,
      by with_reducible exact body.property⟩
  else throw .request

def Original.rows {sources caller} {event : WorkspaceEvent sources caller} {events : List (Event sources caller)}
    (original : Original event events) : List (String × String) :=
  event.naturals.sourceRows ++ event.body.staticRows ++ original.logical.rows ++ original.body.rows

structure Equation {sources caller} {event : WorkspaceEvent sources caller}
    {events : List (Event sources caller)} (original : Original event events)
    (dependencies : List Semantics.Finite.Dependency) (steps : List Semantics.Finite.Step) where
  actual : Matrix
  checked : RuntimeInterval.Computed
    (Raw.Workspace.checkOriginal dependencies (!event.fresh) original.layout.bits steps
      original.logical.matrix original.body.matrix) actual

/-- Check the exact equation of the supplied physical body and its equality
to the independently interpreted original source in the same work budget. -/
def checkSteps {sources caller} {event : WorkspaceEvent sources caller}
    {events : List (Event sources caller)} (original : Original event events)
    (dependencies : List Semantics.Finite.Dependency) (steps : List Semantics.Finite.Step) :
    WorkM (Equation original dependencies steps) := do
  let actual ← NaturalAffine.witness
    (Raw.Workspace.checkOriginal dependencies (!event.fresh) original.layout.bits steps
      original.logical.matrix original.body.matrix)
  return ⟨actual.val,by with_reducible exact actual.property⟩

theorem Equation.originalBody {sources caller} {event : WorkspaceEvent sources caller}
    {events : List (Event sources caller)} {original : Original event events} {dependencies steps}
    (equation : Equation original dependencies steps) : equation.actual = original.body.matrix := by
  obtain ⟨work,left,ok⟩ := equation.checked
  exact (Raw.Workspace.checkOriginal_bound _ _ _ _ _ _ _ work left ok).1

open RuntimeStructuralAction (SourceState)
open RuntimePrimitiveSource (PortAt readPort)

structure Packet where
  dataOut : Nat
  scratchOut : Option Nat
  steps : List Semantics.Finite.Step
  logicalSteps : Option (List Semantics.Finite.Step)

/-- The clean packet uses the existing zero-table allocation and release.
The dirty packet keeps the two existing owners, data on the low axes. -/
def packet (fresh : Bool) (bits : Nat) (data : Nat) (scratch : Option Nat)
    (operations : List Semantics.Observation.Op) : WorkM Packet := do
  match fresh,scratch,operations with
  | true,none,[.pure (.certifiedCompute input output [_] table steps logical)] =>
    guard (input == data && table == List.replicate (2^bits) 0) .request
    return ⟨output,none,steps,some logical⟩
  | false,some scratch,[.pure (.join input auxiliary joined),
      .pure (.applyUnitary applied packed steps),.pure (.split split output returned leftBits)] =>
    guard (input == data && auxiliary == scratch && applied == joined && split == packed && leftBits == bits) .request
    return ⟨output,some returned,steps,none⟩
  | _,_,_ => throw .request

def outputTokens (data : Nat) (scratch : Option Nat) : List Nat := data :: scratch.toList

private def continued {sources caller} (event : WorkspaceEvent sources caller) (before : SourceState)
    (dataOut : Semantics.Raw.Port) (scratchOut : Option Semantics.Raw.Port) : SourceState :=
  let bindings := before.bindings.map fun binding =>
    if binding.owner == event.input then ⟨event.dataOut,dataOut⟩ else
    match scratchOut with
    | some port => if binding.owner == event.scratch then ⟨event.scratchOut,port⟩ else binding
    | none => binding
  ⟨bindings,before.issued ++ (if event.fresh then [event.scratch] else []) ++ event.body.allocated,
    event.body.nextOrdinal⟩

private def validInput {sources caller} (event : WorkspaceEvent sources caller) (before : SourceState)
    (input : Semantics.Raw.Port) (scratch : Option Semantics.Raw.Port) (bits : Nat) : Bool :=
  event.nextOrdinal == before.nextOrdinal && event.input != event.scratch && input.bits == bits &&
    (if event.fresh then event.scratch.ordinal == before.nextOrdinal && !before.issued.contains event.scratch
      else scratch.any (fun port => port.bits == 1))

def checkLogical (dependencies : List Semantics.Finite.Dependency) (bits : Nat)
    (expected : Matrix) (emitted : Packet) : WorkM Unit := do
  if let some steps := emitted.logicalSteps then
    let logical ← circuitMatrix dependencies (Raw.circuit bits steps)
    exactWork (Exact.charge (logical.entries.length+expected.entries.length+1))
    guard (logical == expected) .equation

/-- The external operator seen by the caller, in written data/scratch order. -/
def callerAction (fresh : Bool) (bits : Nat) (logical : Matrix) : WorkM Matrix :=
  if fresh then pure logical else Raw.promote (bits+1) (List.range bits) logical

def inputOwners {sources caller} (event : WorkspaceEvent sources caller) : List RuntimeOwnerMap.Owner :=
  if event.fresh then [event.input] else [event.input,event.scratch]

def outputOwners {sources caller} (event : WorkspaceEvent sources caller) : List RuntimeOwnerMap.Owner :=
  if event.fresh then [event.dataOut] else [event.dataOut,event.scratchOut]

def carrierOwners (bindings : RuntimeOwnerMap.Map) : List Semantics.CarrierInterface.Owner :=
  bindings.map fun binding => ⟨binding.port,binding.owner.basis⟩

structure Literal {sources caller dependencies program block start count}
    {event : WorkspaceEvent sources caller} {events : List (Event sources caller)}
    (original : Original event events)
    (interval : @RuntimeInterval.Checked dependencies program block start count) (before : SourceState) where
  frame : RuntimeOwnerMap.Checked (before.bindings.map (·.owner)) interval.before
  sameFrame : frame.bindings = before.bindings
  input : PortAt event.input before.bindings
  scratch : Option (PortAt event.scratch before.bindings)
  sourceInputs : validInput event before input.port (scratch.map (·.port)) original.layout.bits = true
  emitted : Packet
  emittedRead : RuntimeInterval.Computed (packet event.fresh original.layout.bits input.port.token
    ((scratch.map (·.port)).map (·.token)) ((block.operations.drop start).take count)) emitted
  operations : List Semantics.Raw.Op
  originalOperations : (block.operations.drop start).take count = operations.map Semantics.Observation.Op.pure
  selected : PureInterval.ports interval.before (outputTokens input.port.token ((scratch.map (·.port)).map (·.token))) =
    some (input.port :: (scratch.map (·.port)).toList)
  dataOut : Semantics.Raw.Port
  scratchOut : Option Semantics.Raw.Port
  returned : PureInterval.ports interval.after (outputTokens emitted.dataOut emitted.scratchOut) =
    some (dataOut :: scratchOut.toList)
  wires : dataOut.wires = input.port.wires ∧ scratchOut.map (·.wires) = (scratch.map (·.port)).map (·.wires)
  spectators : PureInterval.spectators interval.before (outputTokens input.port.token ((scratch.map (·.port)).map (·.token))) =
    PureInterval.spectators interval.after (outputTokens emitted.dataOut emitted.scratchOut)
  after : RuntimeOwnerMap.Checked ((continued event before dataOut scratchOut).bindings.map (·.owner)) interval.after
  afterBindings : after.bindings = (continued event before dataOut scratchOut).bindings
  equation : Equation original dependencies emitted.steps
  logical : RuntimeInterval.Computed
    (checkLogical dependencies original.layout.bits original.logical.matrix emitted) ()

structure CallerMap {sources caller dependencies program block start count}
    {event : WorkspaceEvent sources caller} {events : List (Event sources caller)}
    {original : Original event events} {interval : @RuntimeInterval.Checked dependencies program block start count}
    {before : SourceState} (literal : Literal original interval before) where
  selected : RuntimeOwnerMap.Map
  returned : RuntimeOwnerMap.Map
  spectators : RuntimeOwnerMap.Map
  orderedInput : selected.map (·.owner) = inputOwners event
  orderedOutput : returned.map (·.owner) = outputOwners event
  inputPartition : (selected ++ spectators).Perm literal.frame.bindings
  outputPartition : (returned ++ spectators).Perm literal.after.bindings
  native : RuntimePureInterval.Literal block start count
    (selected.map (·.port.token)) (returned.map (·.port.token)) .unitary
  nativeInterval : native.interval = interval
  entryPorts : native.selected = selected.map (·.port)
  returnPorts : native.returned = returned.map (·.port)
  inputCode : Matrix
  outputCode : Matrix
  inputRead : RuntimeInterval.Computed (Carrier.ownerCode (carrierOwners selected)) inputCode
  outputRead : RuntimeInterval.Computed (Carrier.ownerCode (carrierOwners returned)) outputCode
  physical : Matrix
  physicalRead : RuntimeInterval.Computed (Raw.ProtectedEvaluation.reconstruct dependencies
    (RuntimePureInterval.fragment native.selected native.operations (returned.map (·.port.token)))) physical
  logical : Matrix
  logicalRead : RuntimeInterval.Computed (callerAction event.fresh original.layout.bits original.logical.matrix) logical
  action : CodeSpace.Map inputCode outputCode physical
  equation : action.logical = logical
  receiptSlots : Qirf.Slots
  resources : Raw.WorkspaceResources.Checked (Qirf.before receiptSlots) interval.before.quantum.reference
    interval.after.quantum.reference literal.operations

def Literal.continuation {sources caller dependencies program block start count event events original interval before}
    (literal : @Literal sources caller dependencies program block start count event events original interval before) :
    SourceState := continued event before literal.dataOut literal.scratchOut

private def exitPorts (returned : List Semantics.Raw.Port) : Option (Semantics.Raw.Port × Option Semantics.Raw.Port) :=
  match returned with
  | [data] => some (data,none)
  | [data,scratch] => some (data,some scratch)
  | _ => none

def readLiteral {sources caller dependencies program block start count}
    {event : WorkspaceEvent sources caller} {events : List (Event sources caller)}
    (original : Original event events)
    (interval : @RuntimeInterval.Checked dependencies program block start count) (before : SourceState) :
    WorkM (Literal original interval before) := do
  exactWork (Exact.charge (64*(Raw.OwnerFlow.fields before.issued + before.bindings.length +
    block.operations.length + 2^original.layout.bits + 1)))
  let frame ← RuntimeOwnerMap.checkBindings (before.bindings.map (·.owner)) interval.before before.bindings
  let input ← readPort event.input before.bindings
  let scratch ← if event.fresh then pure none else some <$> readPort event.scratch before.bindings
  let scratchPort := scratch.map (·.port)
  let inputTokens := outputTokens input.port.token (scratchPort.map (·.token))
  let operations := (block.operations.drop start).take count
  if sourceInputs : validInput event before input.port scratchPort original.layout.bits = true then
    let emitted ← NaturalAffine.witness
      (packet event.fresh original.layout.bits input.port.token (scratchPort.map (·.token)) operations)
    let outputs := outputTokens emitted.val.dataOut emitted.val.scratchOut
    let some ports := PureInterval.ports interval.after outputs | throw .request
    let some (dataOut,scratchOut) := exitPorts ports | throw .request
    match originalOps : Sector.pureOps operations with
    | none => throw .request
    | some pureOps =>
      if ports : PureInterval.ports interval.before inputTokens = some (input.port :: scratchPort.toList) ∧
          PureInterval.ports interval.after outputs = some (dataOut :: scratchOut.toList) ∧
          (dataOut.wires = input.port.wires ∧ scratchOut.map (·.wires) = scratchPort.map (·.wires)) ∧
          PureInterval.spectators interval.before inputTokens = PureInterval.spectators interval.after outputs then
        let next := continued event before dataOut scratchOut
        let after ← RuntimeOwnerMap.checkBindings (next.bindings.map (·.owner)) interval.after next.bindings
        let equation ← checkSteps original dependencies emitted.val.steps
        let logical ← NaturalAffine.witness
          (checkLogical dependencies original.layout.bits original.logical.matrix emitted.val)
        have logicalUnit : logical.val = () := Subsingleton.elim _ _
        return ⟨frame.val,frame.property,input,scratch,sourceInputs,emitted.val,
          by with_reducible exact emitted.property,pureOps,Sector.pureOps_bound _ _ originalOps,
          ports.1,dataOut,scratchOut,ports.2.1,ports.2.2.1,ports.2.2.2,after.val,after.property,equation,
          by rw [← logicalUnit]; with_reducible exact logical.property⟩
      else throw .request
  else throw .request

def readCallerMap {sources caller dependencies program block start count}
    {event : WorkspaceEvent sources caller} {events : List (Event sources caller)}
    {original : Original event events} {interval : @RuntimeInterval.Checked dependencies program block start count}
    {before : SourceState} (literal : Literal original interval before)
    (receiptSlots : Qirf.Slots) : WorkM (CallerMap literal) := do
  let selected ← RuntimeOwnerMap.order (inputOwners event) literal.frame.bindings
  let returned ← RuntimeOwnerMap.order (outputOwners event) literal.after.bindings
  exactWork (Exact.charge (64*(literal.frame.bindings.length+literal.after.bindings.length+1)^2))
  let spectators := literal.frame.bindings.filter (fun binding => !(inputOwners event).contains binding.owner)
  if owners : selected.map (·.owner) = inputOwners event ∧ returned.map (·.owner) = outputOwners event ∧
      (selected ++ spectators).Perm literal.frame.bindings ∧ (returned ++ spectators).Perm literal.after.bindings then
    let native ← RuntimePureInterval.readLiteral interval (selected.map (·.port.token)) (returned.map (·.port.token)) .unitary
    if ports : native.val.selected = selected.map (·.port) ∧ native.val.returned = returned.map (·.port) then
      let input ← NaturalAffine.witness (Carrier.ownerCode (carrierOwners selected))
      let output ← NaturalAffine.witness (Carrier.ownerCode (carrierOwners returned))
      let physical ← NaturalAffine.witness (Raw.ProtectedEvaluation.reconstruct dependencies
        (RuntimePureInterval.fragment native.val.selected native.val.operations (returned.map (·.port.token))))
      let logical ← NaturalAffine.witness (callerAction event.fresh original.layout.bits original.logical.matrix)
      let action ← CodeSpace.readMap input.val output.val physical.val
      exactWork (Exact.charge (action.logical.entries.length+logical.val.entries.length+1))
      if equation : action.logical = logical.val then
        exactWork (Exact.charge (8*(receiptSlots.size+1)))
        let resources ← Raw.WorkspaceResources.read (Qirf.before receiptSlots) interval.before.quantum.reference
          interval.after.quantum.reference literal.operations
        return ⟨selected,returned,spectators,owners.1,owners.2.1,owners.2.2.1,owners.2.2.2,
          native.val,native.property,ports.1,ports.2,input.val,output.val,
          by with_reducible exact input.property,by with_reducible exact output.property,
          physical.val,by with_reducible exact physical.property,logical.val,
          by with_reducible exact logical.property,action,equation,receiptSlots,resources⟩
      else throw .equation
    else throw .request
  else throw .request

end QleisliKernel.Qirf.RuntimeWorkspace
