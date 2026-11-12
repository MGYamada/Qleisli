import QleisliKernel.Qirf.SourceMeaningOrdinary
import QleisliKernel.Qirf.RuntimePrimitiveSource

/-! Reconstruct the physical predicate table from the original total
ordinary body and the exact nominal carrier. The separate use-body and
cleanup checks still determine whether a computed operation is valid.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeComputedPredicate
open QleisliKernel Finite SourceTypes

private def readTable {sources caller} (event : SourceRuntimeContext.ComputedEvent sources caller)
    (body : SourceRuntimeTrace.Body event.predicate.target.signature)
    (layout : Semantics.FiniteCarrier.Layout) : WorkM (List Nat) := do
  let [parameter] := body.checked.summary.parameterValues | throw .request
  let [(basis,.input 0)] := SourceRuntimeValues.ordinary parameter | throw .request
  exactWork (Exact.charge (32*(Raw.OwnerFlow.fields [⟨0,basis⟩,⟨0,event.input.basis⟩]+1)))
  guard (basis == event.input.basis) .request
  let length := 2^layout.bits
  let value := body.checked.summary.value
  exactWork (Exact.charge (32*(length+layout.labels.length*(SourceRuntimeValues.valueFields value+1)+1)))
  let entries ← layout.labels.zipIdx.foldlM (init := Array.replicate length 0) fun entries (label,ordinal) => do
    let assigned := SourceMeaningOrdinary.valuation [(0,ordinal)]
    let result ← lift ((SourceRuntimeOrdinary.extract assigned value).mapError fun _ => .request)
    let [.ordinary [.bit] result] := result | throw .request
    if valid : label < entries.size then
      return entries.set label result valid
    else throw .request
  return entries.toList

structure Source {sources caller} (event : SourceRuntimeContext.ComputedEvent sources caller) where
  body : SourceRuntimeTrace.Body event.predicate.target.signature
  original : RuntimeInterval.Computed (SourceRuntimeTrace.readComputedPredicateBody event) body
  layout : Semantics.FiniteCarrier.Layout
  originalLayout : RuntimeInterval.Computed (FiniteCarrier.read event.input.basis) layout
  table : List Nat
  computed : RuntimeInterval.Computed (readTable event body layout) table

/-- Only the canonical logical codes are evaluated. The physical table has a
fixed zero value at each padding code. -/
def readSource {sources caller} (event : SourceRuntimeContext.ComputedEvent sources caller) :
    WorkM (Source event) := do
  let body ← NaturalAffine.witness (SourceRuntimeTrace.readComputedPredicateBody event)
  let layout ← NaturalAffine.witness (FiniteCarrier.read event.input.basis)
  let table ← NaturalAffine.witness (readTable event body.val layout.val)
  return ⟨body.val,by with_reducible exact body.property,layout.val,by with_reducible exact layout.property,
    table.val,by with_reducible exact table.property⟩

def checkTable {sources caller} {event : SourceRuntimeContext.ComputedEvent sources caller}
    (original : Source event) (table : List Nat) : WorkM (PLift (table = original.table)) := do
  exactWork (Exact.charge (8*(table.length+original.table.length+1)))
  if same : table = original.table then return ⟨same⟩
  else throw .equation


open RuntimeStructuralAction (SourceState)
open RuntimePrimitiveSource (PortAt readPort)

def continued {sources caller} (event : SourceRuntimeContext.ComputedEvent sources caller)
    (before : SourceState) (output : Semantics.Raw.Port) : SourceState :=
  ⟨before.bindings.map (fun binding => if binding.owner == event.input then ⟨event.input,output⟩ else binding),
    before.issued ++ [event.initial.auxiliary],event.initial.nextOrdinal⟩

structure ProtectedInterval {sources caller dependencies program block start count}
    (event : SourceRuntimeContext.ComputedEvent sources caller) (source : Source event)
    (interval : @RuntimeInterval.Checked dependencies program block start count) (before : SourceState) where
  protectedScope : event.written.parts.logical = none
  sourceOwner : event.returned.data = event.input ∧ event.nextOrdinal = before.nextOrdinal ∧
    event.initial.auxiliary ∉ before.issued
  frame : RuntimeOwnerMap.Checked (before.bindings.map (·.owner)) interval.before
  sameFrame : frame.bindings = before.bindings
  input : PortAt event.input before.bindings
  output : Semantics.Raw.Port
  auxiliary : Nat
  table : List Nat
  uses : List Semantics.Raw.Use
  literal : (block.operations.drop start).take count =
    [.pure (.computeUseUncompute input.port.token output.token [] [auxiliary] table uses)]
  outputRead : PureInterval.ports interval.after [output.token] = some [output]
  wires : output.wires = input.port.wires
  exactTable : table = source.table
  width : input.port.bits = source.layout.bits
  spectators : PureInterval.spectators interval.before [input.port.token] =
    PureInterval.spectators interval.after [output.token]
  after : RuntimeOwnerMap.Checked ((continued event before output).bindings.map (·.owner)) interval.after
  afterBindings : after.bindings = (continued event before output).bindings

/-- Bind the original predicate and data owner to one actual protected Raw
instruction. The original use-body equation remains a separate obligation. -/
def readProtectedInterval {sources caller dependencies program block start count}
    (event : SourceRuntimeContext.ComputedEvent sources caller) (source : Source event)
    (interval : @RuntimeInterval.Checked dependencies program block start count) (before : SourceState) :
    WorkM (ProtectedInterval event source interval before) := do
  exactWork (Exact.charge (64*(Raw.OwnerFlow.fields (event.input :: event.initial.auxiliary ::
    event.returned.data :: before.issued) + block.operations.length+before.bindings.length+1)))
  if protectedScope : event.written.parts.logical = none then
    if sourceOwner : event.returned.data = event.input ∧ event.nextOrdinal = before.nextOrdinal ∧
        event.initial.auxiliary ∉ before.issued then
      let frame ← RuntimeOwnerMap.checkBindings (before.bindings.map (·.owner)) interval.before before.bindings
      let input ← readPort event.input before.bindings
      match literal : (block.operations.drop start).take count with
      | [.pure (.computeUseUncompute inputToken outputToken [] [auxiliary] table uses)] =>
        match returned : PureInterval.ports interval.after [outputToken] with
        | some [output] =>
          if ports : inputToken = input.port.token ∧ outputToken = output.token ∧ output.wires = input.port.wires then
            let tableRead ← checkTable source table
            if width : input.port.bits = source.layout.bits then
              if spectators : PureInterval.spectators interval.before [input.port.token] =
                  PureInterval.spectators interval.after [output.token] then
                let next := continued event before output
                let after ← RuntimeOwnerMap.checkBindings (next.bindings.map (·.owner)) interval.after next.bindings
                return ⟨protectedScope,sourceOwner,frame.val,frame.property,input,output,auxiliary,table,uses,
                  by simpa only [ports.1,ports.2.1] using literal,
                  by simpa only [ports.2.1] using returned,ports.2.2,tableRead.down,width,spectators,
                  after.val,after.property⟩
              else throw .request
            else throw .request
          else throw .request
        | _ => throw .request
      | _ => throw .request
    else throw .request
  else throw .request


def ProtectedInterval.operation {sources caller dependencies program block start count event source interval before}
    (checked : @ProtectedInterval sources caller dependencies program block start count event source interval before) :
    Semantics.Raw.Op :=
  .computeUseUncompute checked.input.port.token checked.output.token [] [checked.auxiliary] checked.table checked.uses

/-- The dispatch premise for the protected clean square comes from the
already-checked literal interval. -/
theorem ProtectedInterval.dispatch {sources caller dependencies program block start count event source interval before}
    (checked : @ProtectedInterval sources caller dependencies program block start count event source interval before) :
    ∃ next, Raw.dispatch (dependencies.map (·.signature)) interval.before.quantum checked.operation = .ok next := by
  obtain ⟨work,left,read⟩ := interval.intervalRead
  rw [checked.literal] at read
  change (Raw.Observation.checkOps dependencies block.fuel interval.before [.pure checked.operation]).run work =
    (.ok interval.after,left) at read
  cases fuel : block.fuel with
  | zero =>
    rw [fuel] at read
    change ((Except.error Error.limit : Except Error RuntimeInterval.State),work) = (.ok interval.after,left) at read
    cases read
  | succ depth =>
    rw [fuel] at read
    change ((do
      let next ← [Semantics.Observation.Op.pure checked.operation].foldlM
        (Raw.Observation.checkStep dependencies (Raw.Observation.checkOps dependencies depth)) interval.before
      guard (Raw.stateValid next.quantum && Raw.Observation.history interval.before next)
      return next : WorkM RuntimeInterval.State).run work) = (.ok interval.after,left) at read
    obtain ⟨_,_,step,_⟩ := Finite.bind_success _ _ _ _ _ read
    simp only [List.foldlM_cons,List.foldlM_nil,bind_pure] at step
    unfold Raw.Observation.checkStep at step
    obtain ⟨_,_,_,rest⟩ := Finite.bind_success _ _ _ _ _ step
    obtain ⟨_,_,_,rest⟩ := Finite.bind_success _ _ _ _ _ rest
    obtain ⟨_,_,pureStep,_⟩ := Finite.bind_success _ _ _ _ _ rest
    unfold Raw.Observation.checkAction at pureStep
    obtain ⟨_,_,_,rest⟩ := Finite.bind_success _ _ _ _ _ pureStep
    obtain ⟨_,_,lifted,_⟩ := Finite.bind_success _ _ _ _ _ rest
    have native := (Finite.lift_success _ _ _ _ lifted).1
    unfold Raw.step at native
    obtain ⟨_,_,rest⟩ := Finite.except_bind_success _ _ _ native
    obtain ⟨dispatched,dispatch,_⟩ := Finite.except_bind_success _ _ _ rest
    exact ⟨dispatched,dispatch⟩

end QleisliKernel.Qirf.RuntimeComputedPredicate
