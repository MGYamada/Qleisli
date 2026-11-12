import QleisliKernel.Qirf.RuntimeComputedPredicate

/-! Compare a protected one-Bit use with the exact action of the original
scoped body, including its scalar phase and resolved forward calls.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeComputedUse
open QleisliKernel Finite SourceTypes SourceRuntimeContext SourceRuntimeValues
open Semantics.Exact
abbrev Owner := Semantics.SourceOwners.Owner
abbrev Rows := List (String × String)

structure Action where
  matrix : Matrix
  rows : Rows

private def identity : Matrix := ⟨2,2,[Scalar.one,Scalar.zero,Scalar.zero,Scalar.one]⟩

private def primitive (kind : Semantics.PrimitiveOperator.Kind) (basis : Semantics.FiniteCarrier.Basis)
    (rows : Rows) : WorkM Action := do
  let some matrix := Semantics.PrimitiveOperator.meaning kind basis | throw .request
  return ⟨matrix,rows⟩

private def ownerOnly (owner : Owner) (value : Value) : Bool := value == [.owner owner]

private def sourceAction (sources : Sources) :
    Nat → {caller : String} → Owner → List (Event sources caller) → WorkM Action
  | 0,_,_,_ => throw .limit
  | fuel+1,_,owner,events => do
    exactWork (Exact.charge (16*(events.length+1)))
    events.foldlM (init := ⟨identity,[]⟩) fun before event => do
      let action ← match event with
        | .phase phase => do
          guard (phase.operand == owner) .request
          primitive (.phase phase.application.coefficient.exponent) owner.basis
            (CallName.sourceRows phase.application.candidate ++ phase.naturals.sourceRows)
        | .primitive call => do
          guard (call.arguments == [[.owner owner]] && ownerOnly owner call.value &&
            call.allocated.isEmpty && call.consumed.isEmpty) .request
          let kind ← RuntimePrimitiveSource.readKind call.kind
          primitive kind.val owner.basis (CallName.sourceRows call.candidate)
        | .named call => do
          guard (call.arguments == [[.owner owner]] && ownerOnly owner call.value &&
            call.allocated.isEmpty && call.consumed.isEmpty && call.effect == .unitary &&
            call.target.signature.arguments.operations.isEmpty &&
            !call.target.signature.operations.hasMeaningRequirements) .request
          let child ← SourceRuntimeTrace.readNamedSource call
          let [[.owner childOwner]] := child.summary.parameterValues | throw .request
          guard (childOwner.basis == owner.basis && ownerOnly childOwner child.summary.value &&
            child.summary.allocated.isEmpty && child.summary.consumed.isEmpty &&
            child.summary.inferredEffect == .unitary) .request
          let action ← sourceAction sources fuel childOwner child.events
          return {action with rows := call.target.sourceRows ++ child.summary.staticRows ++ action.rows}
        | .staticConditional conditional _ => do
          let selected ← SourceRuntimeTrace.readStaticSource conditional
          guard (selected.result.allocated.isEmpty && selected.result.consumed.isEmpty &&
            inferredEffect selected.result.events == .unitary) .request
          let action ← sourceAction sources fuel owner selected.result.events
          return {action with rows := conditional.naturals.sourceRows ++ selected.result.staticRows ++ action.rows}
        | _ => throw .request
      exactWork (Exact.charge (8*(before.rows.length+action.rows.length+1)))
      return ⟨← exactWork (Exact.Matrix.composeWork action.matrix before.matrix),before.rows ++ action.rows⟩

private def sourceBody {sources caller} {event : ComputedEvent sources caller}
    (body : SourceRuntimeTrace.ComputedBody event) : WorkM Action := do
  let owner := event.initial.auxiliary
  guard (owner.basis == [.bit] && ownerOnly owner body.result.value && body.result.allocated.isEmpty &&
    body.result.consumed.isEmpty && inferredEffect body.result.events == .unitary) .request
  let action ← sourceAction sources (SourceTrace.sourceFuel sources) owner body.result.events
  return {action with rows := body.result.staticRows ++ action.rows}

private def auxiliaryBit : Semantics.Raw.ProtectedBit := ⟨.ancilla,0⟩

private def auxiliaryOnly : Semantics.Raw.Use → Bool
  | .protectedGate bit gate => bit == auxiliaryBit && (gate == .z || gate == .t)
  | .phase controls _ => controls.all (·.bit == auxiliaryBit)
  | .targetGate .. => false

/-- Compare the actual Raw uses on both possible auxiliary values. The
source label is irrelevant because these uses can only inspect the auxiliary. -/
private def rawAction (uses : List Semantics.Raw.Use) : WorkM Matrix := do
  exactWork (Exact.charge (16*((uses.map fun use => match use with
    | .protectedGate .. => 1
    | .phase controls _ | .targetGate controls .. => controls.length+1).sum+1)))
  guard (uses.all auxiliaryOnly) .request
  let initial := fun _ => pure Scalar.one
  let zero ← Raw.ProtectedEvaluation.run 0 0 uses initial 0
  let one ← Raw.ProtectedEvaluation.run 0 1 uses initial 0
  return ⟨2,2,[zero,Scalar.zero,Scalar.zero,one]⟩

structure Prepared {sources caller} (event : ComputedEvent sources caller) where
  predicate : RuntimeComputedPredicate.Source event
  body : SourceRuntimeTrace.ComputedBody event
  originalBody : RuntimeInterval.Computed (SourceRuntimeTrace.readComputedSource event) body
  action : Action
  originalAction : RuntimeInterval.Computed (sourceBody body) action

def Prepared.rows {sources caller} {event : ComputedEvent sources caller} (prepared : Prepared event) : Rows :=
  event.naturals.sourceRows ++ event.predicate.target.sourceRows ++
    prepared.predicate.body.checked.summary.staticRows ++ prepared.action.rows

/-- Read the original predicate and use once, before the final checked Raw
graph is available. Their exact identities remain available for that check. -/
def prepare {sources caller} (event : ComputedEvent sources caller) : WorkM (Prepared event) := do
  guard (event.written.parts.logical.isNone) .request
  let predicate ← RuntimeComputedPredicate.readSource event
  let body ← NaturalAffine.witness (SourceRuntimeTrace.readComputedSource event)
  let action ← NaturalAffine.witness (sourceBody body.val)
  return ⟨predicate,body.val,by with_reducible exact body.property,action.val,by with_reducible exact action.property⟩

structure Checked {sources caller dependencies program block start count}
    {event : ComputedEvent sources caller} (prepared : Prepared event)
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (before : RuntimeStructuralAction.SourceState) where
  literal : RuntimeComputedPredicate.ProtectedInterval event prepared.predicate interval before
  emitted : Matrix
  literalAction : RuntimeInterval.Computed (rawAction literal.uses) emitted
  equation : emitted = prepared.action.matrix

def read {sources caller dependencies program block start count}
    {event : ComputedEvent sources caller} (prepared : Prepared event)
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (before : RuntimeStructuralAction.SourceState) : WorkM (Checked prepared interval before) := do
  let literal ← RuntimeComputedPredicate.readProtectedInterval event prepared.predicate interval before
  let emitted ← NaturalAffine.witness (rawAction literal.uses)
  exactWork (Exact.charge (prepared.action.matrix.entries.length+emitted.val.entries.length+1))
  if equation : emitted.val = prepared.action.matrix then
    return ⟨literal,emitted.val,by with_reducible exact emitted.property,equation⟩
  else throw .equation

end QleisliKernel.Qirf.RuntimeComputedUse
