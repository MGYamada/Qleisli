import QleisliKernel.Qirf.EngineeringOpenQasmGate
import Qleisli.EngineeringPureComposition
import Qleisli.FiniteMatrixAction

/-! Exact actions and phase-sensitive engineering bounds for original literal
OpenQASM gate definitions. Each resource limit covers the same decoded word
that supplies the operator comparison.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.NativeEngineeringOpenQasmGate

open QleisliKernel.Qirf.EngineeringOpenQasmGate
open QleisliKernel.Semantics.Finite (width)
open QleisliKernel.Qirf.RuntimeInterval (Computed)
open Qleisli.Semantics.Exact (action rational)
open Qleisli.EngineeringPureComposition (matrixAt portMatrix operator liftLeft gap_operator IsometricPair)

open scoped BigOperators

private theorem range_sum (n : Nat) (f : Nat → ℂ) :
    ((List.range n).map f).sum = ∑ index : Fin n, f index := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    rw [Fin.sum_univ_castSucc]
    simpa only [Fin.val_castSucc, Fin.val_last] using congrArg (fun value => value + f n) ih

private theorem action_dimensions {body} (actual : CheckedAction body) :
    actual.matrix.rows = 2^width body.basis ∧ actual.matrix.cols = 2^width body.basis := by
  obtain ⟨work,left,ran⟩ := actual.read
  obtain ⟨rows,cols,_⟩ := Qleisli.Finite.circuitMatrix_pull [] body actual.matrix work left ran
  exact ⟨rows,cols⟩

private theorem action_gram {ports instructions} (actual : CheckedAction (circuit ports instructions)) :
    (portMatrix ports.basis ports.basis actual.matrix).conjTranspose *
      portMatrix ports.basis ports.basis actual.matrix = 1 := by
  classical
  obtain ⟨rows,cols⟩ := action_dimensions actual
  obtain ⟨work,left,ran⟩ := actual.isometry
  have gram := (Qleisli.Exact.isometry_gram _ _ _ ran).2
  rw [rows,cols] at gram
  ext row col
  have checked := gram row col row.isLt col.isLt
  rw [range_sum] at checked
  simpa only [portMatrix, matrixAt, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, Fin.ext_iff] using checked

theorem slice_ideal {ports instructions ideal epsilon}
    (checked : CheckedSlice ports instructions ideal epsilon) :
    Qleisli.NativeEngineeringPure.LeafMeaning ideal ports.basis ports.basis checked.intended := by
  obtain ⟨work,left,ran⟩ := checked.idealRead
  exact Qleisli.NativeEngineeringPure.leaf_meaning _ _ _ _ work left ran

private theorem slice_bound {ports instructions ideal epsilon}
    (checked : CheckedSlice ports instructions ideal epsilon) :
    0 ≤ (rational epsilon : ℝ) ∧
    ‖operator (portMatrix ports.basis ports.basis checked.actual.matrix -
      portMatrix ports.basis ports.basis ideal.required)‖ ≤ (rational epsilon : ℝ) := by
  obtain ⟨work,left,ran⟩ := checked.boundRead
  have bound := Qleisli.EngineeringPure.checkMatrices_bound _ _ _ _ _ _ ran
  obtain ⟨rows,cols⟩ := action_dimensions checked.actual
  rw [(slice_ideal checked).equation] at bound
  refine ⟨bound.2.2.1,?_⟩
  have inequality := bound.2.2.2
  rw [← gap_operator,rows,cols] at inequality
  exact inequality

private theorem slice_gram {ports instructions ideal epsilon}
    (checked : CheckedSlice ports instructions ideal epsilon) :
    IsometricPair (portMatrix ports.basis ports.basis checked.actual.matrix)
      (portMatrix ports.basis ports.basis ideal.required) := by
  have meaning := slice_ideal checked
  have gram := Qleisli.EngineeringPureComposition.leaf_gram _ _ _ _ meaning
  rw [meaning.rows,meaning.cols] at gram
  exact ⟨action_gram checked.actual,gram⟩

/-- Applied in order, both checked slice matrices give exactly the action of
every instruction of the decoded target body, on arbitrary joint amplitudes. -/
theorem sequential_literal_action {R : Type} {request : SequentialRequest}
    (checked : CheckedSequential request) (joint : Nat → R → ℂ)
    (row : Nat) (reference : R) (inside : row < checked.second.actual.matrix.rows) :
    action checked.second.actual.matrix
      (fun middle spectator => action checked.first.actual.matrix joint middle spectator) row reference =
    Qleisli.Semantics.RawAction.circuit []
      (circuit checked.target.block.ports checked.target.block.instructions).steps
      (fun input => joint input reference) row := by
  let first := circuit checked.target.block.ports (checked.target.block.instructions.take request.split)
  let second := circuit checked.target.block.ports (checked.target.block.instructions.drop request.split)
  obtain ⟨startFirst,leftFirst,ranFirst⟩ := checked.first.actual.read
  obtain ⟨startSecond,leftSecond,ranSecond⟩ := checked.second.actual.read
  have firstRows := (action_dimensions checked.first.actual).1
  have secondRows := (action_dimensions checked.second.actual).1
  have valid := (QleisliKernel.Finite.circuitMatrix_columns []
    second checked.second.actual.matrix startSecond leftSecond ranSecond).1
  have stepsValid : second.steps.all (QleisliKernel.Finite.stepValid [] (width second.basis)) = true := by
    simp only [QleisliKernel.Finite.circuitValid, Bool.and_eq_true] at valid
    tauto
  rw [Qleisli.Finite.circuitMatrix_action _ _ _ _ _ ranSecond _ _ _ inside]
  have assembled :
      (circuit checked.target.block.ports checked.target.block.instructions).steps =
        first.steps ++ second.steps := by
    change checked.target.block.instructions.map _ =
      (checked.target.block.instructions.take request.split).map _ ++
      (checked.target.block.instructions.drop request.split).map _
    rw [← List.map_append, List.take_append_drop]
  rw [assembled]
  have compose : ∀ input,
      Qleisli.Semantics.RawAction.circuit [] (first.steps ++ second.steps) input =
        Qleisli.Semantics.RawAction.circuit [] second.steps
          (Qleisli.Semantics.RawAction.circuit [] first.steps input) := by
    intro input
    simp only [Qleisli.Semantics.RawAction.circuit, List.foldl_append]
  rw [compose]
  · apply Qleisli.Finite.rawCircuit_congr [] (width second.basis) second.steps _ _ stepsValid
    · intro middle within
      apply Qleisli.Finite.circuitMatrix_action _ _ _ _ _ ranFirst
      rw [firstRows]
      exact within
    · rw [secondRows] at inside
      exact inside

/-- The literal target gate word determines the two checked slices. Their exact
actions retain that order, while the independent original ideal bodies determine
the two ideal matrices and the request fixes the sum of their budgets. -/
theorem sequential_reference_bound {R : Type} [Fintype R] {request : SequentialRequest}
    (checked : CheckedSequential request) :
    let basis := checked.target.block.ports.basis
    let view := portMatrix basis basis
    decode request.bytes = some checked.target.block ∧
    checked.target.block.counts.within request.limits = true ∧
    ‖operator (liftLeft (R := R) (view checked.second.actual.matrix * view checked.first.actual.matrix -
      view request.second.required * view request.first.required))‖ ≤ (rational request.totalBudget : ℝ) := by
  have first := slice_bound checked.first
  have second := slice_bound checked.second
  have sum := Qleisli.Exact.coefficient_add_preserves _ _ _ checked.sum
  have realSum : (rational request.totalBudget : ℝ) =
      (rational request.firstBudget : ℝ) + (rational request.secondBudget : ℝ) := by
    exact_mod_cast sum
  refine ⟨checked.target.read,checked.target.within,?_⟩
  dsimp only
  rw [realSum]
  exact Qleisli.EngineeringPureComposition.sequential_reference_bound _ _ _ _
    (slice_gram checked.first) (slice_gram checked.second) _ _ first.1 second.1 first.2 second.2

/-- The matrix used in the controlled comparison gives the literal ordered
action of the decoded target on each joint input, with phase retained. -/
theorem controlled_literal_action {R : Type} {request : ControlledRequest}
    (checked : CheckedControlled request) (joint : Nat → R → ℂ)
    (row : Nat) (reference : R) (inside : row < checked.actual.matrix.rows) :
    action checked.actual.matrix joint row reference =
    Qleisli.Semantics.RawAction.circuit []
      (circuit checked.target.block.ports checked.target.block.instructions).steps
      (fun input => joint input reference) row := by
  obtain ⟨work,left,ran⟩ := checked.actual.read
  exact Qleisli.Finite.circuitMatrix_action _ _ _ _ _ ran _ _ _ inside

/-- The count and phase-sensitive bound concern the very same decoded open
two-port target. The independently checked one-port ideal supplies the exact
controlled lift in the declared low-control-bit order. -/
theorem controlled_reference_bound {R : Type} [Fintype R] {request : ControlledRequest}
    (checked : CheckedControlled request) :
    decode request.bytes = some checked.target.block ∧
    checked.target.block.counts.within request.limits = true ∧
    Qleisli.NativeEngineeringPure.LeafMeaning request.ideal Ports.one.basis Ports.one.basis checked.ideal ∧
    Computed (QleisliKernel.Qirf.OperationIRMeaning.controlled request.ideal.required) checked.controlled ∧
    ‖operator (liftLeft (R := R)
      (matrixAt checked.actual.matrix.rows checked.actual.matrix.cols checked.actual.matrix -
       matrixAt checked.actual.matrix.rows checked.actual.matrix.cols checked.controlled))‖ ≤
      (rational request.epsilon : ℝ) := by
  obtain ⟨startIdeal,leftIdeal,idealRead⟩ := checked.idealRead
  have ideal := Qleisli.NativeEngineeringPure.leaf_meaning _ _ _ _ startIdeal leftIdeal idealRead
  obtain ⟨work,left,ran⟩ := checked.boundRead
  have bound := Qleisli.EngineeringPure.checkMatrices_bound _ _ _ _ _ _ ran
  have controlled := checked.controlledRead
  rw [ideal.equation] at controlled
  refine ⟨checked.target.read,checked.target.within,ideal,controlled,?_⟩
  exact Qleisli.EngineeringPureComposition.liftLeft_bound _ _ bound.2.2.1
    (by rw [gap_operator]; exact bound.2.2.2)

#print axioms sequential_literal_action
#print axioms sequential_reference_bound
#print axioms controlled_literal_action
#print axioms controlled_reference_bound

end Qleisli.NativeEngineeringOpenQasmGate
