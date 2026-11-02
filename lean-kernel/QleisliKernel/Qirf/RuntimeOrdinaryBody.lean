import QleisliKernel.Qirf.RuntimeOrdinarySSA
import QleisliKernel.Qirf.RuntimeObservationAction
import QleisliKernel.Qirf.RuntimeStructuralAction
import QleisliKernel.SourceTypes.SourceRuntimeTrace

/-! Ordinary and observing handlers for the common original runtime body loop.
The caller retains the one checked body/root/block and owns event iteration.
Canonical callee quantum roles stay local to the genuine framed call subject;
only source expressions cross the complete original call path here. These
handlers create no root, dispatcher, matrix or accepted handle. Complete input,
hidden-history, branch and final-storage gates remain required by the loop.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeOrdinaryBody
open QleisliKernel QleisliKernel.Finite QleisliKernel.SourceTypes
open RuntimeOrdinarySSA
abbrev SourceState := RuntimeStructuralAction.SourceState
abbrev Position := SourceSequence.Position

/-- Each edge retains the original instantiated event and a fresh exact callee
body read. No emitted module name, numeric width or wire alias builds an edge. -/
inductive CallPath (sources : Sources) (rootOwner rootName : String) : String → String → Type where
  | root {signature : SourceRuntimeContext.Signature sources rootOwner rootName}
      (body : SourceRuntimeTrace.Body signature) : CallPath sources rootOwner rootName rootOwner rootName
  | named {caller : String} (event : SourceRuntimeContext.NamedEvent sources caller)
      (body : SourceRuntimeTrace.Body event.target.signature)
      (original : RuntimeInterval.Computed (SourceRuntimeTrace.readNamedBody event) body)
      (parent : CallPath sources rootOwner rootName caller event.target.callerName) :
      CallPath sources rootOwner rootName event.target.resolution.moduleName event.target.resolution.declaration.name

def callSite {sources caller} (event : SourceRuntimeContext.NamedEvent sources caller) :
    Semantics.SourceOrdinary.Site := ⟨caller,event.target.callerName,event.call.calleeOffset⟩

def CallPath.transport {sources rootOwner rootName owner name}
    (path : CallPath sources rootOwner rootName owner name) (expression : Expression) : Except String Expression :=
  match path with
  | .root _ => pure expression
  | .named event _ _ parent => do
    let lifted ← SourceRuntimeValues.expressionTransport
      (callSite event) event.ownerMap
      (event.arguments.flatMap SourceRuntimeValues.ordinary) expression
    parent.transport lifted

def CallPath.fields {sources rootOwner rootName owner name} : CallPath sources rootOwner rootName owner name → Nat
  | .root _ => 0
  | .named event _ _ parent => parent.fields+1+
      event.target.callerName.utf8ByteSize+event.target.resolution.moduleName.utf8ByteSize+
      (event.arguments.map SourceRuntimeValues.valueFields).sum+Raw.OwnerFlow.fields event.ownerMap

structure Measurement where
  origin : Semantics.SourceOrdinary.Site
  calls : List Semantics.SourceOrdinary.Site
  owner : Semantics.SourceOwners.Owner
  output : Nat

def Measurement.expression (measurement : Measurement) : Expression :=
  .measured measurement.origin measurement.calls measurement.owner

structure State where
  table : Table := []
  measurements : List Measurement := []

/-- Ordinary root inputs and every checked measurement use the same actual
history. Undefined inactive measurements remain undefined; choose evaluates
only its actual source arm. No default value or outcome subset is supplied. -/
def valuation (inputs : List Nat) (measurements : List Measurement) (values : Values) : Valuation :=
  { inputs := fun ordinal => inputs[ordinal]?
    basisInputs := fun _ => none
    measured := fun origin calls owner => do
      let measured ← measurements.find? fun entry =>
        decide (entry.origin = origin ∧ entry.calls = calls ∧ entry.owner = owner)
      let bit ← Semantics.OrdinaryValue.lookup values measured.output
      return bitValue bit }

def visibleIds (native : Raw.Observation.State) : List Nat :=
  native.classical.filterMap fun (id,scope) => if native.active.contains scope then some id else none

def visibleTable (native : Raw.Observation.State) (ssa : State) : Table :=
  ssa.table.filter fun binding => Raw.Observation.visible native binding.1

structure Visible (native : Raw.Observation.State) (before : State) where
  table : Table
  original : table = visibleTable native before
  complete : table.map Prod.fst = visibleIds native
  distinct : (table.map Prod.fst).Nodup

def Visible.ssa {native before} (visible : Visible native before) : State :=
  {before with table := visible.table}

theorem Visible.measurements {native before} (visible : Visible native before) :
    visible.ssa.measurements = before.measurements := rfl

/-- A named scope receives every currently visible actual SSA input and its
original symbolic expression. Inaccessible identities are not scope inputs;
the measurement-key environment remains intact for transported expressions. -/
def readVisible (native : Raw.Observation.State) (before : State) : WorkM (Visible native before) := do
  exactWork (Exact.charge (32*(native.classical.length+native.active.length+before.table.length+1)^2+
    32*(before.table.map fun binding => SourceRuntimeValues.expressionFields binding.2).sum))
  let table := visibleTable native before
  if complete : table.map Prod.fst = visibleIds native then
    if distinct : (table.map Prod.fst).Nodup then
      return ⟨table,rfl,complete,distinct⟩
    else throw .request
  else throw .request

structure Gap {dependencies program} (block : RuntimeInterval.Block dependencies program)
    (start count : Nat) (before : SourceState) (ssa : State) where
  checked : RuntimeOrdinarySSA.Gap block start count ssa.table
  beforeFrame : RuntimeOwnerMap.Checked (before.bindings.map (·.owner)) checked.interval.before
  beforeRead : RuntimeInterval.Computed
    (RuntimeOwnerMap.check (before.bindings.map (·.owner)) checked.interval.before before.bindings) beforeFrame
  afterFrame : RuntimeOwnerMap.Checked (before.bindings.map (·.owner)) checked.interval.after
  afterRead : RuntimeInterval.Computed
    (RuntimeOwnerMap.check (before.bindings.map (·.owner)) checked.interval.after before.bindings) afterFrame
  quantum : checked.interval.after.quantum = checked.interval.before.quantum
  observe : checked.interval.after.observe = checked.interval.before.observe

def Gap.after {dependencies program block start count before ssa}
    (_gap : @Gap dependencies program block start count before ssa) : SourceState := before

def Gap.ssa {dependencies program block start count before ssa}
    (gap : @Gap dependencies program block start count before ssa) : State :=
  {ssa with table := gap.checked.after}

theorem Gap.sameSource {dependencies program block start count before ssa}
    (gap : @Gap dependencies program block start count before ssa) : gap.after = before := rfl

/-- Consume the entire literal classical-only gap and bind the identical full
quantum frame on both ends, including issuance, phase flag and Unit owners. -/
def readGap {dependencies program} (block : RuntimeInterval.Block dependencies program)
    (start count : Nat) (before : SourceState) (ssa : State) : WorkM (Gap block start count before ssa) := do
  exactWork (Exact.charge (32*(Raw.OwnerFlow.fields before.issued+
    Raw.OwnerFlow.fields (before.bindings.map (·.owner))+block.operations.length+1)))
  let checked ← RuntimeOrdinarySSA.readGap block start count ssa.table
  let beforeFrame ← NaturalAffine.witness
    (RuntimeOwnerMap.check (before.bindings.map (·.owner)) checked.interval.before before.bindings)
  let afterFrame ← NaturalAffine.witness
    (RuntimeOwnerMap.check (before.bindings.map (·.owner)) checked.interval.after before.bindings)
  exactWork (Exact.charge (32*(checked.interval.before.quantum.seenTokens.length+
    checked.interval.before.quantum.seenWires.length+checked.interval.after.quantum.seenTokens.length+
    checked.interval.after.quantum.seenWires.length+1)))
  if unchanged : checked.interval.after.quantum = checked.interval.before.quantum ∧
      checked.interval.after.observe = checked.interval.before.observe then
    return ⟨checked,beforeFrame.val,by with_reducible exact beforeFrame.property,
      afterFrame.val,by with_reducible exact afterFrame.property,unchanged.1,unchanged.2⟩
  else throw .request

def extendObservation {sources rootOwner rootName caller functionName dependencies program event block position previous}
    (path : CallPath sources rootOwner rootName caller functionName)
    (checked : @RuntimeObservationAction.Checked sources caller dependencies program functionName event block position previous)
    (ssa : State) : WorkM State := do
  match checked.measurement with
  | none => return ssa
  | some (source,output) =>
    exactWork (Exact.charge (32*(path.fields+SourceRuntimeValues.expressionFields source+
      SourceRuntimeValues.expressionSize source+ssa.table.length+
      (ssa.measurements.map fun entry => SourceRuntimeValues.expressionFields entry.expression).sum+1)))
    let expression ← lift ((path.transport source).mapError fun _ => .request)
    match expression with
    | .measured origin calls owner =>
      guard (!ssa.measurements.any fun entry =>
        decide (entry.origin = origin ∧ entry.calls = calls ∧ entry.owner = owner)) .request
      guard (RuntimeOrdinarySSA.lookup ssa.table output).isNone .request
      let measurement : Measurement := ⟨origin,calls,owner,output⟩
      return ⟨ssa.table ++ [(output,measurement.expression)],ssa.measurements ++ [measurement]⟩
    | _ => throw .request

structure Observation {sources rootOwner rootName caller functionName dependencies program}
    (path : CallPath sources rootOwner rootName caller functionName)
    (event : SourceRuntimeContext.PrimitiveEvent sources caller)
    (block : RuntimeInterval.Block dependencies program) (position : Position)
    (before : SourceState) (ssa : State) where
  checked : RuntimeObservationAction.Checked functionName event block position before.bindings
  nextOrdinal : event.nextOrdinal = before.nextOrdinal
  issued : before.issued.map (·.ordinal) = List.range before.nextOrdinal
  liveIssued : before.bindings.all (fun binding => before.issued.contains binding.owner) = true
  consumedIssued : before.issued.contains checked.operand = true
  ordinary : State
  ordinaryRead : RuntimeInterval.Computed (extendObservation path checked ssa) ordinary

def Observation.after {sources rootOwner rootName caller functionName dependencies program path event block position before ssa}
    (observation : @Observation sources rootOwner rootName caller functionName dependencies program
      path event block position before ssa) : SourceState :=
  {before with bindings := observation.checked.after.bindings}

def Observation.retired {sources rootOwner rootName caller functionName dependencies program path event block position before ssa}
    (_observation : @Observation sources rootOwner rootName caller functionName dependencies program
      path event block position before ssa) : List Semantics.SourceOwners.Owner := event.consumed

theorem Observation.issuedUnchanged {sources rootOwner rootName caller functionName dependencies program
    path event block position before ssa}
    (observation : @Observation sources rootOwner rootName caller functionName dependencies program
      path event block position before ssa) :
    observation.after.issued = before.issued ∧ observation.after.nextOrdinal = before.nextOrdinal := ⟨rfl,rfl⟩

/-- This handler applies to the genuine canonical body frame. A named caller
must separately frame its spectators and transport the complete returned,
issued and retired roles through the original event.ownerMap. -/
def readObservation {sources rootOwner rootName caller functionName dependencies program}
    (path : CallPath sources rootOwner rootName caller functionName)
    (event : SourceRuntimeContext.PrimitiveEvent sources caller)
    (block : RuntimeInterval.Block dependencies program) (position : Position)
    (before : SourceState) (ssa : State) : WorkM (Observation path event block position before ssa) := do
  exactWork (Exact.charge (32*(Raw.OwnerFlow.fields before.issued+
    Raw.OwnerFlow.fields (before.bindings.map (·.owner))+before.nextOrdinal+1)))
  let checked ← RuntimeObservationAction.check functionName event block position before.bindings
  if histories : event.nextOrdinal = before.nextOrdinal ∧
      before.issued.map (·.ordinal) = List.range before.nextOrdinal ∧
      before.bindings.all (fun binding => before.issued.contains binding.owner) = true ∧
      before.issued.contains checked.operand = true then
    let ordinary ← NaturalAffine.witness (extendObservation path checked ssa)
    return ⟨checked,histories.1,histories.2.1,histories.2.2.1,histories.2.2.2,
      ordinary.val,by with_reducible exact ordinary.property⟩
  else throw .request

end QleisliKernel.Qirf.RuntimeOrdinaryBody
