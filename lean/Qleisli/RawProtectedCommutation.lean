import Qleisli.RawProtectedEvaluation

/-! A first bounded proof component for issue #303: adjacent literal phase uses
commute in the existing protected semantics. This defines no ctrl/borrow access
contract, grants no optimizer permission and admits no new guarantee.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Raw.ProtectedCommutation
open QleisliKernel.Semantics.Raw QleisliKernel.Semantics.Exact
open Qleisli.Semantics.Protected Qleisli.Semantics.Exact

/-- Two literal protected phases commute on every full physical amplitude,
including shared controls, all auxiliary inputs and an arbitrary reference. -/
theorem phase_use_commute {R : Type} (first second : List ProtectedControl)
    (p q : Phase) (ψ : Physical R) :
    physicalUse (.phase second q) (physicalUse (.phase first p) ψ) =
      physicalUse (.phase first p) (physicalUse (.phase second q) ψ) := by
  funext source ancilla target reference
  simp only [physicalUse]
  ring

/-- Only the adjacent phases move. Every original prefix/suffix operation and
coordinate is retained; no well-typedness or access permission is inferred. -/
theorem run_adjacent_phase_swap {R : Type} (before after : List Use)
    (first second : List ProtectedControl) (p q : Phase) (ψ : Physical R) :
    run (before ++ .phase first p :: .phase second q :: after) ψ =
      run (before ++ .phase second q :: .phase first p :: after) ψ := by
  simp only [run,List.foldl_append,List.foldl_cons]
  rw [phase_use_commute first second p q]

/-- The unchanged original compute/use/uncompute presentation retains every
physical coefficient, rather than replacing the use body with a logical flag. -/
theorem coefficient_adjacent_phase_swap (sourceBits : Nat) (function : List Nat)
    (before after : List Use) (first second : List ProtectedControl) (p q : Phase)
    (dimension index : Nat) :
    Qleisli.Semantics.ProtectedMatrix.coefficient sourceBits function
      (before ++ .phase first p :: .phase second q :: after) dimension index =
    Qleisli.Semantics.ProtectedMatrix.coefficient sourceBits function
      (before ++ .phase second q :: .phase first p :: after) dimension index := by
  dsimp only [Qleisli.Semantics.ProtectedMatrix.coefficient]
  rw [run_adjacent_phase_swap]

private theorem interpreted_entries {α β γ : Type} (f : α → γ) (g : β → γ)
    {inputs : List α} {values : List β}
    (related : List.Forall₂ (fun input value => g value = f input) inputs values) :
    values.map g = inputs.map f := by
  induction related with
  | nil => rfl
  | cons head tail ih => simp [head,ih]

/-- Both original bounded matrix evaluations must succeed. Their dimensions
and all row-major complex coefficients then agree exactly. The theorem makes
no claim that swapping preserves acceptance, failure, or remaining work. -/
theorem checked_matrix_phase_swap (sourceBits dataBits ancillaBits : Nat)
    (function : List Nat) (before after : List Use)
    (first second : List ProtectedControl) (p q : Phase)
    (original swapped : Matrix) (work left otherWork otherLeft : Nat)
    (originalOk : (QleisliKernel.Raw.ProtectedEvaluation.matrix sourceBits dataBits ancillaBits function
      (before ++ .phase first p :: .phase second q :: after)).run work = (.ok original,left))
    (swappedOk : (QleisliKernel.Raw.ProtectedEvaluation.matrix sourceBits dataBits ancillaBits function
      (before ++ .phase second q :: .phase first p :: after)).run otherWork = (.ok swapped,otherLeft)) :
    original.rows = swapped.rows ∧ original.cols = swapped.cols ∧
      original.entries.map scalar = swapped.entries.map scalar := by
  obtain ⟨originalRows,originalCols,originalEntries⟩ :=
    Qleisli.Raw.ProtectedEvaluation.matrix_meaning _ _ _ _ _ _ _ _ originalOk
  obtain ⟨swappedRows,swappedCols,swappedEntries⟩ :=
    Qleisli.Raw.ProtectedEvaluation.matrix_meaning _ _ _ _ _ _ _ _ swappedOk
  refine ⟨originalRows.trans swappedRows.symm,originalCols.trans swappedCols.symm,?_⟩
  rw [interpreted_entries _ _ originalEntries,interpreted_entries _ _ swappedEntries]
  apply List.map_congr_left
  intro index _
  exact coefficient_adjacent_phase_swap _ _ _ _ _ _ _ _ _ _


private theorem scalar_default (value : Option Scalar) :
    (value.map scalar).getD 0 = scalar (value.getD Scalar.zero) := by
  cases value <;> simp [Qleisli.Exact.scalar_zero_meaning]

/-- Arbitrary joint/reference amplitudes have the same action after both
successful checks; no normalization, separability or equality of work is used. -/
theorem checked_matrix_phase_swap_action {R : Type}
    (sourceBits dataBits ancillaBits : Nat) (function : List Nat) (before after : List Use)
    (first second : List ProtectedControl) (p q : Phase)
    (original swapped : Matrix) (work left otherWork otherLeft : Nat)
    (originalOk : (QleisliKernel.Raw.ProtectedEvaluation.matrix sourceBits dataBits ancillaBits function
      (before ++ .phase first p :: .phase second q :: after)).run work = (.ok original,left))
    (swappedOk : (QleisliKernel.Raw.ProtectedEvaluation.matrix sourceBits dataBits ancillaBits function
      (before ++ .phase second q :: .phase first p :: after)).run otherWork = (.ok swapped,otherLeft))
    (joint : Nat → R → ℂ) (row : Nat) (reference : R) :
    action original joint row reference = action swapped joint row reference := by
  obtain ⟨_,cols,entries⟩ := checked_matrix_phase_swap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ originalOk swappedOk
  have coeff (column : Nat) : entry original row column = entry swapped row column := by
    have point := congrArg (fun values : List ℂ => values[row*original.cols+column]?.getD 0) entries
    simpa [entry,Matrix.entry,List.getElem?_map,scalar_default,cols] using point
  simp only [action,cols]
  apply congrArg List.sum
  apply List.map_congr_left
  intro column _
  rw [coeff]

end Qleisli.Raw.ProtectedCommutation
