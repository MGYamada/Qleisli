import QleisliKernel.Qirf.RuntimeComputedPredicate
import QleisliKernel.Qirf.OperationIRMeaning

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

private def rearrange (before after : List Owner) (matrix : Matrix) : WorkM Matrix := do
  if before == after then return matrix
  exactWork (Exact.charge (SourceTrace.Meter.permutationWork before after))
  guard (decide (before.Perm after) && decide ((before.map (·.ordinal)).Nodup)) .request
  let fields ← before.mapM fun owner => do
    let layout ← FiniteCarrier.read owner.basis
    pure (owner,layout.labels.length)
  let dimension := fields.foldl (fun size field => size*field.2) 1
  guard (dimension == matrix.rows) .request
  exactWork (Exact.charge (16*(fields.length+1)^2*(dimension+1) + matrix.rows*matrix.cols))
  let ordered ← after.mapM fun owner => lift (readOption (fields.lookup owner))
  let entries := matrix.entries.toArray
  let rows ← (List.range dimension).flatMapM fun row => do
    let (_,digits) := (after.zip ordered).foldl (fun (remaining,digits) (owner,card) =>
      (remaining/card,(owner,remaining%card)::digits)) (row,[])
    let original ← fields.foldrM (fun (owner,card) rest => do
      let digit ← lift (readOption (digits.lookup owner))
      pure (digit + card*rest)) 0
    (List.range matrix.cols).mapM fun column => lift (readOption entries[original*matrix.cols+column]?)
  lift (arithmetic (Exact.Matrix.make matrix.rows matrix.cols rows))

private def applyGroup (owners operands returned : List Owner) (localAction before : Action) :
    WorkM (List Owner × Action) := do
  exactWork (Exact.charge (16*(Raw.OwnerFlow.fields (owners ++ operands ++ returned)+1)^2))
  guard (decide ((returned ++ owners.filter (fun owner => !operands.contains owner)).Nodup)) .request
  let rest := owners.filter (fun owner => !operands.contains owner)
  let ordered := operands ++ rest
  let beforeMatrix ← rearrange owners ordered before.matrix
  let whole ← rest.foldlM (init := localAction.matrix) fun matrix owner => do
    let layout ← FiniteCarrier.read owner.basis
    exactWork (Exact.charge ((layout.labels.length+1)^2))
    let identity ← lift (arithmetic (Exact.Matrix.identity layout.labels.length))
    exactWork (Exact.Matrix.tensorWork matrix identity)
  let matrix ← exactWork (Exact.Matrix.composeWork whole beforeMatrix)
  let result := returned ++ rest
  exactWork (Exact.charge (8*(before.rows.length+localAction.rows.length+1)))
  return (result,⟨matrix,before.rows ++ localAction.rows⟩)

private def unary (owners : List Owner) (operand : Owner) (localAction before : Action) : WorkM Action := do
  let whole ← ownerAction owners operand localAction
  let matrix ← exactWork (Exact.Matrix.composeWork whole.matrix before.matrix)
  exactWork (Exact.charge (8*(before.rows.length+whole.rows.length+1)))
  return ⟨matrix,before.rows ++ whole.rows⟩

private def registerAction {sources caller} (event : RegisterEvent sources caller) : WorkM Action := do
  let [width,index] := event.application.arguments.map (·.value) | throw .request
  guard (width ≤ 6 && index < width) .limit
  let axes ← match event.kind with
    | .takeBit => pure (index :: (List.range width).erase index)
    | .putBit =>
      let remainder := (List.range (width-1)).map (·+1)
      pure (remainder.take index ++ [0] ++ remainder.drop index)
    | _ => throw .request
  exactWork (Exact.charge (8*(width+1)*(2^width+1)))
  let table := (List.range (2^width)).map (Semantics.Finite.gather · axes)
  let matrix ← Raw.mapping width width table
  return ⟨matrix,(Event.registerPrimitive event).staticRows⟩

private structure CallKey where
  caller : String
  owner : String
  name : String
  deriving DecidableEq

private def callKey {sources caller scope tokens} (target : SourceRuntimeContext.Target sources caller scope tokens) : CallKey :=
  ⟨caller,target.resolution.moduleName,target.resolution.declaration.name⟩

private def callKeyWork (key : CallKey) : Nat :=
  key.caller.utf8ByteSize + key.owner.utf8ByteSize + key.name.utf8ByteSize + 1

/-- Evaluate original gates and explicit pair regrouping. A split keeps the
components adjacent and first-fast. A join first orders its written inputs. -/
def sourceAction (sources : Sources) (workspace : Bool) :
    Nat → {caller : String} → List Owner → List Owner → Matrix → List (Event sources caller) → WorkM Action :=
  Nat.rec (fun {_} _ _ _ _ => throw .limit) (fun _ next {_} initial output identity events => do
    exactWork (Exact.charge (16*(events.length+1)))
    let (owners,action,_) ← events.foldlM
        (init := (initial,⟨identity,[]⟩,([] : List (CallKey × Action)))) fun (owners,before,cache) event => do
      exactWork (Exact.charge (8*(Raw.OwnerFlow.fields owners+1)))
      match event with
      | .phase phase => do
        guard (owners.contains phase.operand) .request
        let action ← primitive (.phase phase.application.coefficient.exponent) phase.operand.basis
          (CallName.sourceRows phase.application.candidate ++ phase.naturals.sourceRows)
        return (owners,← unary owners phase.operand action before,cache)
      | .primitive call => do
        let rows := CallName.sourceRows call.candidate
        exactWork (Exact.charge (8*(before.rows.length+rows.length+1)))
        match call.kind,call.arguments,call.value with
        | .split,[[.owner operand]],[.tuple 2,.owner left,.owner right] =>
          guard (owners.contains operand && RuntimeStructuralAction.sourceShape call .split &&
            !owners.contains left && !owners.contains right && left != right) .request
          return (owners.flatMap (fun owner => if owner == operand then [left,right] else [owner]),
            {before with rows := before.rows ++ rows},cache)
        | .join,[[.owner left],[.owner right]],[.owner joined] =>
          guard (owners.contains left && owners.contains right && RuntimeStructuralAction.sourceShape call .join &&
            !owners.contains joined) .request
          let rest := owners.filter (fun owner => owner != left && owner != right)
          let matrix ← rearrange owners (left::right::rest) before.matrix
          return (joined::rest,⟨matrix,before.rows ++ rows⟩,cache)
        | _,[[.owner operand]],[.owner returned] =>
          guard (owners.contains operand && returned == operand &&
            call.allocated.isEmpty && call.consumed.isEmpty) .request
          let kind ← RuntimePrimitiveSource.readKind call.kind
          let action ← primitive kind.val operand.basis rows
          return (owners,← unary owners operand action before,cache)
        | _,_,_ => throw .request
      | .registerPrimitive event => do
        guard (event.consumed.all owners.contains) .request
        let (owners,action) ← applyGroup owners event.consumed event.allocated (← registerAction event) before
        return (owners,action,cache)
      | .named call => do
        let operands := call.arguments.flatMap valueOwners
        let returned := valueOwners call.value
        unless workspace do
          let [[.owner _]] := call.arguments | throw .request
          let [.owner _] := call.value | throw .request
        guard (!operands.isEmpty && operands.map (·.basis) == returned.map (·.basis) &&
          (call.arguments.flatMap ordinary).isEmpty && (ordinary call.value).isEmpty &&
          call.effect == .unitary &&
          call.target.signature.arguments.operations.isEmpty &&
          !call.target.signature.operations.hasMeaningRequirements) .request
        let key := callKey call.target
        -- The cache belongs to this original event list and source table. Only
        -- closed calls reuse an already reconstructed action. The current call
        -- still supplies its own effect, typed operands, return order and rows.
        let cacheable := workspace && decide (call.target.signature.arguments = {})
        exactWork (Exact.charge ((cache.length+1)*callKeyWork key +
          (cache.map fun entry => callKeyWork entry.1).sum))
        let (localAction,cache) ← (show WorkM (Action × List (CallKey × Action)) from
          match if cacheable then cache.lookup key else none with
        | some action => pure (action,cache)
        | none => do
          let child ← SourceRuntimeTrace.readNamedSource call
          unless workspace do
            let [[.owner _]] := child.summary.parameterValues | throw .request
            let [.owner _] := child.summary.value | throw .request
          let childInputs := child.summary.parameterValues.flatMap valueOwners
          let childOutputs := valueOwners child.summary.value
          guard ((child.summary.parameterValues.flatMap ordinary).isEmpty &&
            (ordinary child.summary.value).isEmpty && child.summary.inferredEffect == .unitary &&
            childInputs.map (·.basis) == operands.map (·.basis) &&
            childOutputs.map (·.basis) == returned.map (·.basis)) .request
          let dimension ← operands.foldlM (init := 1) fun size operand => do
            let layout ← FiniteCarrier.read operand.basis
            return size * layout.labels.length
          guard (Exact.matrixValid dimension dimension) .limit
          exactWork (Exact.charge ((dimension+1)^2))
          let localIdentity ← lift (arithmetic (Exact.Matrix.identity dimension))
          let action ← next childInputs childOutputs localIdentity child.events
          let action := {action with rows := child.summary.staticRows ++ action.rows}
          return (action,if cacheable then (key,action)::cache else cache))
        let localAction := {localAction with rows := call.target.sourceRows ++ localAction.rows}
        match operands,returned with
        | [operand],[output] =>
          guard (owners.contains operand && (output == operand || !owners.contains output)) .request
          return (owners.map (fun owner => if owner == operand then output else owner),
            ← unary owners operand localAction before,cache)
        | _,_ =>
          let (owners,action) ← applyGroup owners operands returned localAction before
          return (owners,action,cache)
      | .transform call => do
        guard workspace .request
        let .controlled := call.written.access | throw .request
        let [[.owner control],[.owner operand]] := call.arguments | throw .request
        let [.tuple 2,.owner controlOut,.owner returned] := call.value | throw .request
        guard (control == controlOut && control.basis == [.bit] && returned.basis == operand.basis &&
          call.target.signature.arguments.operations.isEmpty &&
          !call.target.signature.operations.hasMeaningRequirements) .request
        let child ← SourceRuntimeTrace.readTransformSource call
        let [[.owner childInput]] := child.summary.parameterValues | throw .request
        let [.owner childOutput] := child.summary.value | throw .request
        guard (child.summary.inferredEffect == .unitary && childInput.basis == operand.basis &&
          childOutput.basis == operand.basis && call.copies ≤ 4096) .request
        let layout ← FiniteCarrier.read operand.basis
        exactWork (Exact.charge ((layout.labels.length+1)^2))
        let localIdentity ← lift (arithmetic (Exact.Matrix.identity layout.labels.length))
        let action ← next [childInput] [childOutput] localIdentity child.events
        let repeated ← if call.copies == 1 then pure action.matrix
          else OperationIRMeaning.power action.matrix call.copies
        let controlled ← OperationIRMeaning.controlled repeated
        let (owners,action) ← applyGroup owners [control,operand] [controlOut,returned]
          ⟨controlled,call.target.sourceRows ++ child.summary.staticRows ++
            call.counts.flatMap (·.checked.rows) ++ action.rows⟩ before
        return (owners,action,cache)
      | .staticConditional conditional _ => do
        let selected ← SourceRuntimeTrace.readStaticSource conditional
        guard (selected.result.allocated.isEmpty && selected.result.consumed.isEmpty &&
          inferredEffect selected.result.events == .unitary) .request
        let action ← next owners owners before.matrix selected.result.events
        return (owners,{action with rows := before.rows ++ conditional.selection.naturals.sourceRows ++
          selected.result.staticRows ++ action.rows},cache)
      | _ => throw .request
    let matrix ← rearrange owners output action.matrix
    return {action with matrix})

private def sourceBody {sources caller} {event : ComputedEvent sources caller}
    (body : SourceRuntimeTrace.ComputedBody event) : WorkM Action := do
  let owner := event.initial.auxiliary
  guard (owner.basis == [.bit] && ownerOnly owner body.result.value && body.result.allocated.isEmpty &&
    body.result.consumed.isEmpty && inferredEffect body.result.events == .unitary) .request
  let action ← sourceAction sources false (SourceTrace.sourceFuel sources) [owner] [owner]
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
