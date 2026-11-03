/-
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
-/
import QPTL.Dagger
import Mathlib.CategoryTheory.Preadditive.Mat
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Block

/-! Finite-dimensional complex amplitudes in a chosen orthonormal basis. -/

namespace QPTL.FiniteMatrix
open CategoryTheory Opposite
open scoped Matrix Classical

noncomputable section

/-- Opposite of mathlib's row-oriented matrix category. A morphism from A to B
has rows indexed by B and columns indexed by A, so composition acts on columns. -/
abbrev Space := (Mat ℂ)ᵒᵖ

/-- An object with the given finite orthonormal basis. -/
abbrev basis (A : Type) [Finite A] : Space := op (FintypeCat.of A : Mat ℂ)

attribute [local instance] FintypeCat.fintype

instance : DaggerCategory Space where
  dagger f := Quiver.Hom.op f.unop.conjTranspose
  dagger_id _ := Quiver.Hom.unop_inj Matrix.conjTranspose_one
  dagger_comp f g := Quiver.Hom.unop_inj (Matrix.conjTranspose_mul g.unop f.unop)
  dagger_dagger f := Quiver.Hom.unop_inj (Matrix.conjTranspose_conjTranspose f.unop)

/-- The array of a morphism in the chosen input and output bases. -/
abbrev matrix {A B : Space} (f : A ⟶ B) : Matrix B.unop A.unop ℂ := f.unop

/-- Regard a rectangular matrix as a morphism between its two spaces. -/
def ofMatrix {A B : Space} (m : Matrix B.unop A.unop ℂ) : A ⟶ B :=
  Quiver.Hom.op (show B.unop ⟶ A.unop from m)

@[simp] theorem matrix_ofMatrix {A B : Space} (m : Matrix B.unop A.unop ℂ) :
    matrix (ofMatrix m) = m := rfl

/-- The categorical isometry condition is the usual column Gram equation. -/
theorem isometry_iff {A B : Space} (f : A ⟶ B) :
    IsIsometry f ↔ (matrix f)ᴴ * matrix f = 1 :=
  ⟨fun h => congrArg Quiver.Hom.unop h, fun h => Quiver.Hom.unop_inj h⟩

/-- Both Gram equations in the column convention. -/
theorem unitary_iff {A B : Space} (f : A ⟶ B) :
    IsUnitary f ↔ (matrix f)ᴴ * matrix f = 1 ∧ matrix f * (matrix f)ᴴ = 1 :=
  ⟨fun h => ⟨(isometry_iff f).1 h.isometry, congrArg Quiver.Hom.unop h.coisometry⟩,
    fun h => ⟨(isometry_iff f).2 h.1, Quiver.Hom.unop_inj h.2⟩⟩

/-- A coherent direct sum of rectangular isometries is an isometry.
The summands may have different input and output dimensions for each label. -/
theorem directSum_isometry {L : Type*} [Fintype L] [DecidableEq L] {A B : L → Type*}
    [∀ b, Fintype (A b)] [∀ b, Fintype (B b)] [∀ b, DecidableEq (A b)]
    (op : ∀ b, Matrix (B b) (A b) ℂ) (h : ∀ b, (op b)ᴴ * op b = 1) :
    (Matrix.blockDiagonal' op)ᴴ * Matrix.blockDiagonal' op = 1 := by
  rw [Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul]
  simpa only [h] using (Matrix.blockDiagonal'_one (m' := A) (α := ℂ))

end
end QPTL.FiniteMatrix
