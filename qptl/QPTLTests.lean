/-
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
-/
import QPTL
import Mathlib.Tactic.NormNum

namespace QPTLTests
open CategoryTheory MonoidalCategory QPTL
open scoped QPTL Matrix

section Abstract
variable {C : Type*} [Category C] [DaggerCategory C] {X Y Z : C}

example (f : X ⟶ Y) (g : Y ⟶ Z) (hf : IsUnitary f) (hg : IsUnitary g) :
    IsUnitary (f ≫ g)† := by qptl

example (f : X ⟶ Y) (_hf : IsIsometry f) (hu : IsUnitary f) : IsUnitary f := by
  fail_if_success (clear hu; qptl)
  exact hu

example (f : X ⟶ Y) (g : Y ⟶ Z) : ((f ≫ g)†)† = f ≫ g := by qptl

variable [MonoidalCategory C] [DaggerMonoidalCategory C]

example (f : X ⟶ Y) (g : Y ⟶ Z) (hf : IsIsometry f) (hg : IsUnitary g) (R : C) :
    IsIsometry ((f ≫ g) ⊗ₘ 𝟙 R) := by qptl

/-- A joint state may be entangled with the untouched register. -/
example {A B P Q S R : C} {f : A ⟶ B} {i : A ⟶ P} {o : B ⟶ Q} {g : P ⟶ Q}
    (sq : CommSq f i o g) (joint : S ⟶ A ⊗ R) :
    joint ≫ ((f ⊗ₘ 𝟙 R) ≫ (o ⊗ₘ 𝟙 R)) = joint ≫ ((i ⊗ₘ 𝟙 R) ≫ (g ⊗ₘ 𝟙 R)) := by
  have idSquare : CommSq (𝟙 R) (𝟙 R) (𝟙 R) (𝟙 R) := ⟨rfl⟩
  exact congrArg (joint ≫ ·) (tensor_square sq idSquare).w
end Abstract

section Concrete
open QPTL.FiniteMatrix

/-- The normalized first basis vector as a rectangular matrix. -/
private noncomputable def prepare : basis Unit ⟶ basis Bool :=
  ofMatrix (fun b _ => if b then 0 else 1)

example : IsIsometry prepare := by
  apply (isometry_iff _).2
  ext i j
  cases i
  cases j
  simp [prepare, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_eq_single false]
  · simp
  · intro b _ hb
    cases b <;> simp_all
  · simp

example : ¬ IsUnitary prepare := by
  intro h
  have entry := congrArg (fun m : Matrix Bool Bool ℂ => m true true) ((unitary_iff _).mp h).2
  simp [prepare, Matrix.mul_apply, Matrix.conjTranspose_apply] at entry

private def signed : Bool → Matrix Unit Unit ℂ := fun b _ _ => if b then -1 else 1

/-- The minus on just one coherent summand changes the operator. -/
example : Matrix.blockDiagonal' signed ≠ 1 := by
  intro same
  have entry := congrArg (fun m : Matrix (Σ _ : Bool, Unit) (Σ _ : Bool, Unit) ℂ =>
    m ⟨true, ()⟩ ⟨true, ()⟩) same
  norm_num [signed, Matrix.one_apply] at entry
end Concrete

#print axioms QPTL.isometry_of_square
#print axioms QPTL.tensor_square
#print axioms QPTL.FiniteMatrix.directSum_isometry
end QPTLTests
