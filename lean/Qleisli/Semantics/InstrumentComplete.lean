import Qleisli.Semantics.Instrument
import Mathlib.LinearAlgebra.Matrix.Trace

/-! Completeness of independently specified unitary/preparation/readout slices.
These are finite matrix laws. The actual checker bridge must establish the
unitary, injective zero-input embedding and complete outcome/residual indexing.
No acceptance code or proposed proof metadata is imported here.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.Semantics.Instrument
open scoped BigOperators Matrix

/-- Select the initialized input columns and partition every output row into
its classical measurement outcome and its retained quantum coordinates. -/
def sliced {I J K Y O : Type} (operator : Matrix K J ℂ)
    (embed : I → J) (rows : (Y × O) ≃ K) (outcome : Y) : Matrix O I ℂ :=
  fun output input => operator (rows (outcome,output)) (embed input)

/-- Including every outcome preserves the full input Gram matrix. Neither the
input nor the retained system is assumed to be a computational basis state. -/
theorem sliced_complete {I J K Y O : Type}
    [Fintype J] [Fintype K] [Fintype Y] [Fintype O] [DecidableEq I] [DecidableEq J]
    (operator : Matrix K J ℂ) (isometry : operatorᴴ * operator = 1)
    (embed : I → J) (injective : Function.Injective embed) (rows : (Y × O) ≃ K) :
    ∑ y, (sliced operator embed rows y)ᴴ * sliced operator embed rows y = 1 := by
  ext i j
  simp only [Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,sliced,Matrix.one_apply]
  have combined : (∑ y, ∑ output, star (operator (rows (y,output)) (embed i)) *
      operator (rows (y,output)) (embed j)) =
      ∑ k, star (operator k (embed i)) * operator k (embed j) := by
    calc
      _ = ∑ pair : Y × O, star (operator (rows pair) (embed i)) *
          operator (rows pair) (embed j) :=
        (Fintype.sum_prod_type (fun pair : Y × O =>
          star (operator (rows pair) (embed i)) * operator (rows pair) (embed j))).symm
      _ = _ := rows.sum_comp (fun k => star (operator k (embed i)) * operator k (embed j))
  rw [combined]
  have entry := congrFun (congrFun isometry (embed i)) (embed j)
  simpa [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply,injective.eq_iff] using entry

theorem withReference_mul {I M O Reference : Type} [Fintype M] [Fintype Reference]
    [DecidableEq Reference] (A : Matrix O M ℂ) (B : Matrix M I ℂ) :
    withReference (Reference := Reference) (A * B) = withReference A * withReference B := by
  ext ⟨i,r⟩ ⟨j,s⟩
  by_cases same : r = s
  · subst s
    simp [withReference,Matrix.mul_apply,Fintype.sum_prod_type]
  · simp [withReference,Matrix.mul_apply,Fintype.sum_prod_type,same]

theorem withReference_conj {I O Reference : Type} [DecidableEq Reference]
    (A : Matrix O I ℂ) :
    withReference (Reference := Reference) Aᴴ = (withReference A)ᴴ := by
  ext ⟨i,r⟩ ⟨j,s⟩
  by_cases same : r = s
  · subst s
    simp [withReference,Matrix.conjTranspose_apply]
  · simp [withReference,Matrix.conjTranspose_apply,same,Ne.symm same]

theorem withReference_one {I Reference : Type} [DecidableEq I] [DecidableEq Reference] :
    withReference (Reference := Reference) (1 : Matrix I I ℂ) = 1 := by
  ext ⟨i,r⟩ ⟨j,s⟩
  by_cases same : r = s <;> simp [withReference,Matrix.one_apply,Prod.ext_iff,same]

theorem withReference_sum {I O Y Reference : Type} [Fintype Y] [DecidableEq Reference]
    (A : Y → Matrix O I ℂ) :
    withReference (Reference := Reference) (∑ y, A y) = ∑ y, withReference (A y) := by
  ext ⟨i,r⟩ ⟨j,s⟩
  by_cases same : r = s <;> simp [withReference,Matrix.sum_apply,same]

/-- Completeness remains valid after extending each rectangular branch by the
identity on an arbitrary finite reference system. -/
theorem complete_withReference {I O Y Reference : Type}
    [Fintype O] [Fintype Y] [Fintype Reference] [DecidableEq I] [DecidableEq Reference]
    (A : Y → Matrix O I ℂ) (complete : ∑ y, (A y)ᴴ * A y = 1) :
    ∑ y, (withReference (Reference := Reference) (A y))ᴴ * withReference (A y) = 1 := by
  simp only [← withReference_conj,← withReference_mul,← withReference_sum,
    complete,withReference_one]

/-- Summing every unnormalized branch preserves the input/reference trace.
Arbitrary coherences are retained; positivity or product-state assumptions are
unnecessary for this algebraic identity. -/
theorem complete_trace {I O Y Reference : Type}
    [Fintype I] [Fintype O] [Fintype Y] [Fintype Reference]
    [DecidableEq I] [DecidableEq Reference]
    (A : Y → Matrix O I ℂ) (complete : ∑ y, (A y)ᴴ * A y = 1)
    (rho : Matrix (I × Reference) (I × Reference) ℂ) :
    ∑ y, Matrix.trace (density (A y) rho) = Matrix.trace rho := by
  have joint := complete_withReference (Reference := Reference) A complete
  calc
    _ = ∑ y, Matrix.trace ((withReference (A y))ᴴ * withReference (A y) * rho) :=
      Finset.sum_congr rfl (fun y _ => Matrix.trace_mul_cycle _ _ _)
    _ = _ := by
      rw [← Matrix.trace_sum,← Matrix.sum_mul,joint,Matrix.one_mul]

end Qleisli.Semantics.Instrument
