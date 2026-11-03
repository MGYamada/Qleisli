import Qleisli.RuntimeFiniteSectorAction

/-! Exact original logical target slices for arbitrary retained finite carriers.
Transposition uses the actual mixed-radix cardinality and original target
binding, preserving every other digit and zero-width owner. Finite total-complex
sums may be reindexed; no bounded execution, physical availability or capability
is inferred from these identities.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeFiniteTargetLogical
open QleisliKernel QleisliKernel.Qirf
open RuntimeOwnerMap (Binding)
open RuntimeForestCode RuntimeOwnerCodeReindex
open Qleisli.Semantics.Exact Qleisli.RuntimeForestProduct
open Qleisli.MixedRadix Qleisli.RuntimeForestRegroup Qleisli.RuntimeFiniteTargetFibre

def swapDigit (first second digit : Nat) : Nat :=
  if digit = first then second else if digit = second then first else digit

theorem swapDigit_involution (first second digit : Nat) :
    swapDigit first second (swapDigit first second digit) = digit := by
  by_cases atFirst : digit = first
  · subst digit
    by_cases same : first = second
    · subst second
      simp [swapDigit]
    · simp [swapDigit,Ne.symm same]
  · by_cases atSecond : digit = second
    · subst digit
      simp [swapDigit,atFirst]
    · simp [swapDigit,atFirst,atSecond]

theorem swapDigit_eq_second (first second digit : Nat) :
    swapDigit first second digit = second ↔ digit = first := by
  have reverse : swapDigit first second second = first := by
    by_cases same : second = first
    · subst second
      simp [swapDigit]
    · simp [swapDigit,same]
  constructor
  · intro equal
    have undone := congrArg (swapDigit first second) equal
    rwa [swapDigit_involution,reverse] at undone
  · intro equal
    subst digit
    exact if_pos rfl

theorem swapDigit_bound (size first second digit : Nat)
    (firstBound : first < size) (secondBound : second < size) (digitBound : digit < size) :
    swapDigit first second digit < size := by
  unfold swapDigit
  split
  · exact secondBound
  · split
    · exact firstBound
    · exact digitBound

/-- The same original logical target is transposed; no physical code label or
wire stride is used as a logical ordinal. -/
def transpose {roles state checked} (code : @Frame roles state checked) (target : Binding)
    (first second logical : Nat) : Nat :=
  RuntimeTargetDigit.update code target logical
    (swapDigit first second (decode checked.bindings (dimensionAt code.owners) logical target))

theorem transpose_domain {roles state checked} (code : @Frame roles state checked)
    (target : Binding) (member : target ∈ checked.bindings) (first second logical : Nat)
    (firstBound : first < dimensionAt code.owners target) (secondBound : second < dimensionAt code.owners target)
    (bound : logical < code.code.dimension) :
    transpose code target first second logical < code.code.dimension ∧
      transpose code target first second (transpose code target first second logical) = logical ∧
      ∀ binding ∈ checked.bindings,
        decode checked.bindings (dimensionAt code.owners) (transpose code target first second logical) binding =
          if binding = target then
            swapDigit first second (decode checked.bindings (dimensionAt code.owners) logical target)
          else decode checked.bindings (dimensionAt code.owners) logical binding := by
  let digit := decode checked.bindings (dimensionAt code.owners) logical target
  let swapped := swapDigit first second digit
  have fullBound : logical < volume checked.bindings (dimensionAt code.owners) := by
    rw [frame_volume code]
    exact bound
  have digitBound : digit < dimensionAt code.owners target :=
    decode_bound checked.bindings _ logical (cards_positive code.owners) fullBound target member
  have small : swapped < dimensionAt code.owners target :=
    swapDigit_bound _ first second digit firstBound secondBound digitBound
  have changed := RuntimeTargetDigit.update_digits code target logical swapped bound small
  have read : decode checked.bindings (dimensionAt code.owners)
      (transpose code target first second logical) target = swapped := by
    exact (changed.2 target member).trans (if_pos rfl)
  have inverse : transpose code target first second (transpose code target first second logical) = logical := by
    calc
      _ = RuntimeTargetDigit.update code target (transpose code target first second logical) digit := by
        change RuntimeTargetDigit.update code target (transpose code target first second logical)
          (swapDigit first second (decode checked.bindings (dimensionAt code.owners)
            (transpose code target first second logical) target)) = _
        rw [read]
        exact congrArg (RuntimeTargetDigit.update code target (transpose code target first second logical))
          (swapDigit_involution first second digit)
      _ = RuntimeTargetDigit.update code target logical digit :=
        Qleisli.RuntimeMultiwayGram.update_twice code target logical swapped digit bound small
      _ = logical := Qleisli.RuntimeTargetScatter.update_self code target logical bound
  exact ⟨changed.1,inverse,changed.2⟩

/-- Reindex an entire original target-digit slice by a proved transposition.
Each complete caller index is retained, including all nominal spectators. -/
theorem slice_reindex {roles state checked} (code : @Frame roles state checked)
    (target : Binding) (member : target ∈ checked.bindings) (first second : Nat)
    (firstBound : first < dimensionAt code.owners target) (secondBound : second < dimensionAt code.owners target)
    (values : Nat → ℂ) :
    ((List.range code.code.dimension).map fun logical =>
      if decode checked.bindings (dimensionAt code.owners) logical target = first then
        values (RuntimeTargetDigit.update code target logical second) else 0).sum =
      ((List.range code.code.dimension).map fun logical =>
        if decode checked.bindings (dimensionAt code.owners) logical target = second then values logical else 0).sum := by
  let digit := fun logical => decode checked.bindings (dimensionAt code.owners) logical target
  let swap := transpose code target first second
  let term := fun logical => if digit logical = second then values logical else 0
  have domain := transpose_domain code target member first second
  have permutation := Qleisli.RuntimeTargetScatter.involution_range code.code.dimension swap
    (fun logical bound => (domain logical firstBound secondBound bound).1)
    (fun logical bound => (domain logical firstBound secondBound bound).2.1)
  calc
    _ = ((List.range code.code.dimension).map fun logical => term (swap logical)).sum := by
      apply Qleisli.Exact.sum_map_congr
      intro logical present
      have changed := domain logical firstBound secondBound (List.mem_range.mp present)
      have read : digit (swap logical) = swapDigit first second (digit logical) :=
        (changed.2.2 target member).trans (if_pos rfl)
      by_cases selected : digit logical = first
      · have write : swap logical = RuntimeTargetDigit.update code target logical second := by
          change RuntimeTargetDigit.update code target logical (swapDigit first second (digit logical)) = _
          rw [selected]
          simp [swapDigit]
        have swapped : digit (swap logical) = second := by
          rw [read,selected]
          exact if_pos rfl
        change (if digit logical = first then _ else 0) = if digit (swap logical) = second then _ else 0
        rw [if_pos selected,if_pos swapped,write]
      · have absent : digit (swap logical) ≠ second := by
          rw [read]
          exact fun equal => selected ((swapDigit_eq_second first second (digit logical)).mp equal)
        change (if digit logical = first then _ else 0) = if digit (swap logical) = second then _ else 0
        rw [if_neg selected,if_neg absent]
    _ = _ := by
      simpa only [List.map_map,Function.comp_def] using (permutation.map term).sum_eq

/-- Updating the target logical digit preserves every other original owner
factor, including nominal and zero-width spectators. -/
theorem spectator_update {roles state checked} (code : @Frame roles state checked)
    (target : Binding) (physical logical replacement : Nat)
    (bound : logical < code.code.dimension) (small : replacement < dimensionAt code.owners target) :
    spectatorCoefficient code target physical (RuntimeTargetDigit.update code target logical replacement) =
      spectatorCoefficient code target physical logical := by
  have unique : checked.bindings.Nodup :=
    List.Pairwise.of_map (fun binding : Binding => binding.port.token)
      (fun _ _ different same => different (congrArg (fun binding : Binding => binding.port.token) same))
      checked.tokensDistinct
  have changed := RuntimeTargetDigit.update_digits code target logical replacement bound small
  unfold spectatorCoefficient
  apply congrArg List.prod
  apply List.map_congr_left
  intro binding present
  have retained := unique.mem_erase_iff.mp present
  rw [(changed.2 binding retained.2).trans (if_neg retained.1)]

/-- Transport the complete target fibre to another valid original digit.
Spectator coefficients are transported by the same actual update, not supplied
as an invariant of an arbitrary physical encoding. -/
theorem fibre_update {Reference : Type} {roles state checked} (code : @Frame roles state checked)
    (target : Binding) (member : target ∈ checked.bindings) (first second : Nat)
    (firstBound : first < dimensionAt code.owners target) (secondBound : second < dimensionAt code.owners target)
    (joint : Nat → Reference → ℂ) (physical : Nat) (reference : Reference) :
    targetFibre code target physical
        (fun logical ref => joint (RuntimeTargetDigit.update code target logical second) ref) first reference =
      targetFibre code target physical joint second reference := by
  unfold targetFibre
  calc
    _ = ((List.range code.code.dimension).map fun logical =>
        if decode checked.bindings (dimensionAt code.owners) logical target = first then
          spectatorCoefficient code target physical (RuntimeTargetDigit.update code target logical second) *
            joint (RuntimeTargetDigit.update code target logical second) reference
        else 0).sum := by
      apply Qleisli.Exact.sum_map_congr
      intro logical present
      rw [spectator_update code target physical logical second (List.mem_range.mp present) secondBound]
    _ = _ := slice_reindex code target member first second firstBound secondBound
      (fun logical => spectatorCoefficient code target physical logical * joint logical reference)

/-- One exact matrix acts at the same original logical target digit. This is
the per-arm expression used by the complete original-ordinal source action. -/
noncomputable def targetAction {Reference : Type} {roles state checked} (code : @Frame roles state checked)
    (target : Binding) (matrix : QleisliKernel.Semantics.Exact.Matrix)
    (joint : Nat → Reference → ℂ) (logical : Nat) (reference : Reference) : ℂ :=
  action matrix (fun col => joint (RuntimeTargetDigit.update code target logical col))
    (decode checked.bindings (dimensionAt code.owners) logical target) reference

/-- Original target update action commutes with taking the actual complete
logical fibre. Only the genuine target cardinality bounds matrix columns. -/
theorem fibre_action {Reference : Type} {roles state checked} (code : @Frame roles state checked)
    (target : Binding) (member : target ∈ checked.bindings) (matrix : QleisliKernel.Semantics.Exact.Matrix)
    (columns : matrix.cols = dimensionAt code.owners target)
    (joint : Nat → Reference → ℂ) (physical row : Nat) (reference : Reference)
    (rowBound : row < dimensionAt code.owners target) :
    targetFibre code target physical (targetAction code target matrix joint) row reference =
      action matrix (targetFibre code target physical joint) row reference := by
  let digit := fun logical => decode checked.bindings (dimensionAt code.owners) logical target
  have one (logical : Nat) :
      (if digit logical = row then spectatorCoefficient code target physical logical *
          targetAction code target matrix joint logical reference else 0) =
        ((List.range matrix.cols).map fun col => entry matrix row col *
          (if digit logical = row then spectatorCoefficient code target physical logical *
            joint (RuntimeTargetDigit.update code target logical col) reference else 0)).sum := by
    by_cases selected : digit logical = row
    · rw [if_pos selected]
      unfold targetAction
      change spectatorCoefficient code target physical logical *
        action matrix (fun col => joint (RuntimeTargetDigit.update code target logical col)) (digit logical) reference = _
      rw [selected]
      unfold action
      simp only [if_true,← List.sum_map_mul_left]
      apply Qleisli.Exact.sum_map_congr
      intro col _present
      ring
    · simp [selected]
  calc
    _ = ((List.range code.code.dimension).map fun logical =>
        ((List.range matrix.cols).map fun col => entry matrix row col *
          (if digit logical = row then spectatorCoefficient code target physical logical *
            joint (RuntimeTargetDigit.update code target logical col) reference else 0)).sum).sum := by
      unfold targetFibre
      apply Qleisli.Exact.sum_map_congr
      intro logical _present
      exact one logical
    _ = ((List.range matrix.cols).map fun col =>
        ((List.range code.code.dimension).map fun logical => entry matrix row col *
          (if digit logical = row then spectatorCoefficient code target physical logical *
            joint (RuntimeTargetDigit.update code target logical col) reference else 0)).sum).sum :=
      Qleisli.Exact.sum_swap _ _ _
    _ = _ := by
      change _ = ((List.range matrix.cols).map fun col =>
        entry matrix row col * targetFibre code target physical joint col reference).sum
      apply Qleisli.Exact.sum_map_congr
      intro col present
      rw [List.sum_map_mul_left]
      apply congrArg (fun value : ℂ => entry matrix row col * value)
      exact fibre_update code target member row col rowBound
        (by rw [← columns]; exact List.mem_range.mp present) joint physical reference

/-- Intertwining with the actual complete sparse code retains the target's
rectangular encoding, rather than assuming physical rows are logical digits. -/
theorem target_action_code {Reference : Type} {roles state checked} (code : @Frame roles state checked)
    (target : Binding) (member : target ∈ checked.bindings) (actual : OwnerCode target)
    (matrix : QleisliKernel.Semantics.Exact.Matrix) (columns : matrix.cols = dimensionAt code.owners target)
    (joint : Nat → Reference → ℂ) (physical : Nat) (reference : Reference) :
    referenceAction code (targetAction code target matrix joint) physical reference =
      action (QleisliKernel.Semantics.FiniteCarrier.encoding actual.layout)
        (fun row ref => action matrix (targetFibre code target physical joint) row ref)
        (QleisliKernel.Semantics.Finite.gather physical (target.port.wires.map state.quantum.frame.idxOf)) reference := by
  rw [fibre_code_action code target member actual (targetAction code target matrix joint) physical reference]
  change ((List.range actual.layout.labels.length).map fun row =>
    entry (QleisliKernel.Semantics.FiniteCarrier.encoding actual.layout)
      (QleisliKernel.Semantics.Finite.gather physical (target.port.wires.map state.quantum.frame.idxOf)) row *
        targetFibre code target physical (targetAction code target matrix joint) row reference).sum =
    ((List.range actual.layout.labels.length).map fun row =>
      entry (QleisliKernel.Semantics.FiniteCarrier.encoding actual.layout)
        (QleisliKernel.Semantics.Finite.gather physical (target.port.wires.map state.quantum.frame.idxOf)) row *
          action matrix (targetFibre code target physical joint) row reference).sum
  apply Qleisli.Exact.sum_map_congr
  intro row present
  have small : row < dimensionAt code.owners target := by
    rw [dimensionAt_eq code.owners target member actual]
    exact List.mem_range.mp present
  rw [fibre_action code target member matrix columns joint physical row reference small]

#print axioms transpose_domain
#print axioms slice_reindex
#print axioms fibre_update
#print axioms fibre_action
#print axioms target_action_code

end Qleisli.RuntimeFiniteTargetLogical
