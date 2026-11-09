import Qleisli.RuntimeLiteralHistory
import Mathlib.Data.List.Forall2

/-! The ordered source outcomes of a literal observation. Carrier dimensions
and coefficients come from the original basis trees. The checked Raw history
is compared to these independently formed source operators.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeLiteralHistory
open QleisliKernel QleisliKernel.Qirf
open QleisliKernel.Semantics.Observation (Event readOps)
open Qleisli.Semantics.ObservingAction (History run)
open RuntimeForestCode (Frame OwnerCodes)
open RuntimeOwnerMap (Binding Map Owner byOwner)
open RuntimeOwnerCodeReindex (dimensionAt lookup_cons lookup_nil)
open Qleisli.RuntimeOriginalBranchJoin (RepresentsOperator)
open Qleisli.RuntimeOriginalObservation (original_before_bindings outcomeJoint outcomeJointLayout)

/-- Dimensions of the source owners in their complete original order. -/
def sourceDimension (bindings : Map) (binding : Binding) : Nat :=
  if binding ∈ bindings then (Semantics.FiniteCarrier.dimension binding.owner.basis).getD 0 else 0

theorem dimensionAt_source {bindings : Map} (owners : OwnerCodes bindings) (wanted : Binding) :
    dimensionAt owners wanted = sourceDimension bindings wanted := by
  induction owners with
  | nil => simp [dimensionAt, lookup_nil, sourceDimension]
  | @cons binding bindings first rest ih =>
    by_cases same : binding = wanted
    · subst wanted
      simp [dimensionAt, lookup_cons, sourceDimension, Semantics.FiniteCarrier.dimension, first.reference.1]
    · simp only [dimensionAt, lookup_cons, dif_neg same]
      change dimensionAt rest wanted = _
      rw [ih]
      simp [sourceDimension, Ne.symm same]

/-- Evaluate the source operand's erasure in the ordered source coordinates.
Each result retains its outcome and its operator on every reference column. -/
noncomputable def sourceErasure (operand : Owner) (spectators : List Owner) (incoming : Map)
    (joint : Nat → Nat → ℂ) :
    Option (List (Nat × (Nat → Nat → ℂ))) := do
  let layout ← Semantics.FiniteCarrier.layout operand.basis
  let selected ← (operand :: spectators).mapM (byOwner incoming)
  let reordered := fun logical col =>
    joint (Qleisli.MixedRadix.recode selected incoming (sourceDimension incoming) logical) col
  return (List.range (2^layout.bits)).map fun outcome => (outcome, outcomeJointLayout layout outcome reordered)

/-- The actual observation interval has exactly the ordered source outcome
family. Start from the incoming source frame and retain every finite output
row, arbitrary reference columns and visible SSA agreement. -/
theorem observation_source_history {sources rootOwner rootName caller functionName dependencies program
    path event block position before ssa roles}
    (observation : @RuntimeOrdinaryBody.Observation sources rootOwner rootName caller functionName dependencies
      program path event block position before ssa)
    {source : RuntimeOwnerMap.Checked roles observation.checked.interval.before}
    (bindings : source.bindings = before.bindings)
    (input : Frame source) (inputs : List Nat) (history : History) (joint : Nat → Nat → ℂ)
    (agrees : Agrees inputs observation.checked.interval.before ssa history)
    (represented : RepresentsOperator input history joint)
    {events : List Event} {results : List History}
    (read : readOps block.fuel observation.checked.interval.before.quantum.reference
      ((block.operations.drop position.start).take position.count) =
        some (observation.checked.interval.after.quantum.reference,events))
    (executed : run dependencies block.fuel events history = some results) :
    event.value = RuntimeObservationAction.result functionName event observation.checked.operand
      observation.checked.measured ∧
    ∃ output : Frame observation.checked.after, ∃ expected,
      sourceErasure observation.checked.operand (RuntimeObservationAction.spectators event) source.bindings joint =
        some expected ∧
      List.Forall₂ (fun sourceResult result =>
        result.values = (match observation.checked.measured with
          | none => history.values
          | some id => history.values ++ [(id,sourceResult.1 == 1)]) ∧
        result.hidden = history.hidden ++ [sourceResult.1] ∧
        Agrees inputs observation.checked.interval.after observation.ordinary result ∧
        RepresentsOperator output result sourceResult.2) expected results := by
  let reordered := fun logical col =>
    joint (Qleisli.MixedRadix.recode observation.checked.before.bindings source.bindings
      (dimensionAt input.owners) logical) col
  obtain ⟨ordered, orderedRepresents⟩ := observation_entry observation bindings input history joint represented
  obtain ⟨sourceValue, code, output, branch, same, facts⟩ :=
    observation_history observation ordered inputs history reordered agrees orderedRepresents read executed
  have layout : Semantics.FiniteCarrier.layout observation.checked.operand.basis = some code.layout := by
    rw [← observation.checked.originalOwner]
    exact code.reference.1
  have selection : (observation.checked.operand :: RuntimeObservationAction.spectators event).mapM
      (byOwner source.bindings) = some observation.checked.before.bindings := by
    rw [bindings]
    exact original_before_bindings observation.checked
  have dimensions := funext (dimensionAt_source input.owners)
  have bits := code.reference.2.2
  refine ⟨sourceValue, output, (List.range (2^code.layout.bits)).map (fun outcome =>
    (outcome, outcomeJoint code outcome reordered)), ?_, ?_⟩
  · simp [sourceErasure, layout, selection, ← dimensions, reordered, outcomeJoint]
  · rw [same, bits, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    apply List.forall₂_same.2
    intro outcome member
    exact facts outcome (by simpa only [bits] using List.mem_range.mp member)

#print axioms observation_source_history
end Qleisli.RuntimeLiteralHistory
