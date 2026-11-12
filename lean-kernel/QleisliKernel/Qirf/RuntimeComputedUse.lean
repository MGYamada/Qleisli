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

def primitive (kind : Semantics.PrimitiveOperator.Kind) (basis : Semantics.FiniteCarrier.Basis)
    (rows : Rows) : WorkM Action := do
  let layout ← FiniteCarrier.read basis
  exactWork (Exact.charge ((layout.labels.length+1)^2))
  let some matrix := Semantics.PrimitiveOperator.meaning kind basis | throw .request
  return ⟨matrix,rows⟩

def ownerOnly (owner : Owner) (value : Value) : Bool := value == [.owner owner]

private def ownerAction (owners : List Owner) (operand : Owner) (action : Action) : WorkM Action := do
  if owners == [operand] then return action
  let matrices ← owners.mapM fun owner => do
    if owner == operand then return action.matrix
    let layout ← FiniteCarrier.read owner.basis
    exactWork (Exact.charge ((layout.labels.length+1)^2))
    lift (arithmetic (Exact.Matrix.identity layout.labels.length))
  let result ← matrices.foldlM (init := ⟨1,1,[Scalar.one]⟩) fun before next =>
    exactWork (Exact.Matrix.tensorWork before next)
  return {action with matrix := result}

def sourceAction (sources : Sources) :
    Nat → {caller : String} → List Owner → Matrix → List (Event sources caller) → WorkM Action :=
  Nat.rec (fun {_} _ _ _ => throw .limit) (fun _ next {_} owners identity events => do
    exactWork (Exact.charge (16*(events.length+1)))
    events.foldlM (init := ⟨identity,[]⟩) fun before event => do
      let action ← match event with
        | .phase phase => do
          guard (owners.contains phase.operand) .request
          let action ← primitive (.phase phase.application.coefficient.exponent) phase.operand.basis
            (CallName.sourceRows phase.application.candidate ++ phase.naturals.sourceRows)
          ownerAction owners phase.operand action
        | .primitive call => do
          let [[.owner operand]] := call.arguments | throw .request
          guard (owners.contains operand && ownerOnly operand call.value &&
            call.allocated.isEmpty && call.consumed.isEmpty) .request
          let kind ← RuntimePrimitiveSource.readKind call.kind
          let action ← primitive kind.val operand.basis (CallName.sourceRows call.candidate)
          ownerAction owners operand action
        | .named call => do
          let [[.owner operand]] := call.arguments | throw .request
          guard (owners.contains operand && ownerOnly operand call.value &&
            call.allocated.isEmpty && call.consumed.isEmpty && call.effect == .unitary &&
            call.target.signature.arguments.operations.isEmpty &&
            !call.target.signature.operations.hasMeaningRequirements) .request
          let child ← SourceRuntimeTrace.readNamedSource call
          let [[.owner childOwner]] := child.summary.parameterValues | throw .request
          guard (childOwner.basis == operand.basis && ownerOnly childOwner child.summary.value &&
            child.summary.allocated.isEmpty && child.summary.consumed.isEmpty &&
            child.summary.inferredEffect == .unitary) .request
          let layout ← FiniteCarrier.read operand.basis
          exactWork (Exact.charge ((layout.labels.length+1)^2))
          let localIdentity ← lift (arithmetic (Exact.Matrix.identity layout.labels.length))
          let action ← next [childOwner] localIdentity child.events
          ownerAction owners operand {action with rows := call.target.sourceRows ++ child.summary.staticRows ++ action.rows}
        | .staticConditional conditional _ => do
          let selected ← SourceRuntimeTrace.readStaticSource conditional
          guard (selected.result.allocated.isEmpty && selected.result.consumed.isEmpty &&
            inferredEffect selected.result.events == .unitary) .request
          let action ← next owners identity selected.result.events
          return {action with rows := conditional.selection.naturals.sourceRows ++ selected.result.staticRows ++ action.rows}
        | _ => throw .request
      exactWork (Exact.charge (8*(before.rows.length+action.rows.length+1)))
      return ⟨← exactWork (Exact.Matrix.composeWork action.matrix before.matrix),before.rows ++ action.rows⟩)

private def sourceBody {sources caller} {event : ComputedEvent sources caller}
    (body : SourceRuntimeTrace.ComputedBody event) : WorkM Action := do
  let owner := event.initial.auxiliary
  guard (owner.basis == [.bit] && ownerOnly owner body.result.value && body.result.allocated.isEmpty &&
    body.result.consumed.isEmpty && inferredEffect body.result.events == .unitary) .request
  let action ← sourceAction sources (SourceTrace.sourceFuel sources) [owner]
    ⟨2,2,[Scalar.one,Scalar.zero,Scalar.zero,Scalar.one]⟩ body.result.events
  return {action with rows := body.result.staticRows ++ action.rows}

private def auxiliaryBit : Semantics.Raw.ProtectedBit := ⟨.ancilla,0⟩

private def auxiliaryOnly : Semantics.Raw.Use → Bool
  | .protectedGate bit gate => bit == auxiliaryBit && (gate == .z || gate == .t)
  | .phase controls _ => controls.all (·.bit == auxiliaryBit)
  | .targetGate .. => false

private theorem controls_independent (source ancilla : Nat) (controls : List Semantics.Raw.ProtectedControl)
    (only : controls.all (·.bit == auxiliaryBit) = true) :
    Semantics.Protected.enabled source ancilla controls = Semantics.Protected.enabled 0 ancilla controls := by
  induction controls with
  | nil => rfl
  | cons control rest tail =>
    have tested := Bool.and_eq_true_iff.mp only
    have same := beq_iff_eq.mp tested.1
    change (Semantics.Protected.value source ancilla control.bit == control.whenOne &&
        Semantics.Protected.enabled source ancilla rest) =
      (Semantics.Protected.value 0 ancilla control.bit == control.whenOne &&
        Semantics.Protected.enabled 0 ancilla rest)
    rw [same,tail tested.2]
    rfl

private theorem use_independent (source ancilla : Nat) (operation : Semantics.Raw.Use)
    (only : auxiliaryOnly operation = true) :
    Raw.ProtectedEvaluation.use source ancilla operation = Raw.ProtectedEvaluation.use 0 ancilla operation := by
  cases operation with
  | protectedGate bit gate =>
    have tested := Bool.and_eq_true_iff.mp only
    have same := beq_iff_eq.mp tested.1
    subst bit
    rfl
  | targetGate controls target gate => contradiction
  | phase controls phase =>
    funext state label
    simp only [Raw.ProtectedEvaluation.use,controls_independent source ancilla controls only]

theorem run_independent (source ancilla : Nat) (uses : List Semantics.Raw.Use)
    (only : uses.all auxiliaryOnly = true) (initial : Raw.ProtectedEvaluation.State) :
    Raw.ProtectedEvaluation.run source ancilla uses initial = Raw.ProtectedEvaluation.run 0 ancilla uses initial := by
  induction uses generalizing initial with
  | nil => simp only [Raw.ProtectedEvaluation.run,List.foldl_nil]
  | cons first rest tail =>
    have tested := Bool.and_eq_true_iff.mp only
    change Raw.ProtectedEvaluation.run source ancilla rest (Raw.ProtectedEvaluation.use source ancilla first initial) =
      Raw.ProtectedEvaluation.run 0 ancilla rest (Raw.ProtectedEvaluation.use 0 ancilla first initial)
    rw [use_independent source ancilla first tested.1]
    exact tail tested.2 _

def factor (source ancilla : Nat) (uses : List Semantics.Raw.Use) : WorkM Scalar :=
  Raw.ProtectedEvaluation.run source ancilla uses (fun _ => pure Scalar.one) 0

structure RawAction (uses : List Semantics.Raw.Use) where
  auxiliary : uses.all auxiliaryOnly = true
  zero : Scalar
  one : Scalar
  zeroRead : RuntimeInterval.Computed (factor 0 0 uses) zero
  oneRead : RuntimeInterval.Computed (factor 0 1 uses) one

def RawAction.matrix {uses} (action : RawAction uses) : Matrix :=
  ⟨2,2,[action.zero,Scalar.zero,Scalar.zero,action.one]⟩

theorem RawAction.factors {uses} (action : RawAction uses) (source : Nat) :
    RuntimeInterval.Computed (factor source 0 uses) action.zero ∧
    RuntimeInterval.Computed (factor source 1 uses) action.one := by
  unfold factor
  rw [run_independent source 0 uses action.auxiliary,run_independent source 1 uses action.auxiliary]
  exact ⟨action.zeroRead,action.oneRead⟩


theorem RawAction.noTarget {uses} (action : RawAction uses)
    (controls : List Semantics.Raw.ProtectedControl) (target : Nat) (gate : Semantics.Raw.Gate) :
    Semantics.Raw.Use.targetGate controls target gate ∉ uses := by
  intro present
  have checked := List.all_eq_true.mp action.auxiliary _ present
  contradiction

/-- Compare the actual Raw uses on both possible auxiliary values. The
source label is irrelevant because these uses can only inspect the auxiliary. -/
private def rawAction (uses : List Semantics.Raw.Use) : WorkM (RawAction uses) := do
  exactWork (Exact.charge (16*((uses.map fun use => match use with
    | .protectedGate .. => 1
    | .phase controls _ | .targetGate controls .. => controls.length+1).sum+1)))
  if only : uses.all auxiliaryOnly = true then
    let zero ← NaturalAffine.witness (factor 0 0 uses)
    let one ← NaturalAffine.witness (factor 0 1 uses)
    return ⟨only,zero.val,one.val,by with_reducible exact zero.property,by with_reducible exact one.property⟩
  else throw .request

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
  emitted : RawAction literal.uses
  literalAction : RuntimeInterval.Computed (rawAction literal.uses) emitted
  equation : emitted.matrix = prepared.action.matrix

def read {sources caller dependencies program block start count}
    {event : ComputedEvent sources caller} (prepared : Prepared event)
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (before : RuntimeStructuralAction.SourceState) : WorkM (Checked prepared interval before) := do
  let literal ← RuntimeComputedPredicate.readProtectedInterval event prepared.predicate interval before
  let emitted ← NaturalAffine.witness (rawAction literal.uses)
  exactWork (Exact.charge (prepared.action.matrix.entries.length+emitted.val.matrix.entries.length+1))
  if equation : emitted.val.matrix = prepared.action.matrix then
    return ⟨literal,emitted.val,by with_reducible exact emitted.property,equation⟩
  else throw .equation

#print axioms RawAction.factors
end QleisliKernel.Qirf.RuntimeComputedUse
