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


/-- The two unitary equations of a coherent sum follow from the equations
of its original summands, with the input and output labels fixed. -/
theorem directSum_unitary {L : Type*} [Fintype L] [DecidableEq L] {A B : L → Type*}
    [∀ b, Fintype (A b)] [∀ b, Fintype (B b)]
    [∀ b, DecidableEq (A b)] [∀ b, DecidableEq (B b)]
    (op : ∀ b, Matrix (B b) (A b) ℂ)
    (h : ∀ b, (op b)ᴴ * op b = 1 ∧ op b * (op b)ᴴ = 1) :
    (Matrix.blockDiagonal' op)ᴴ * Matrix.blockDiagonal' op = 1 ∧
      Matrix.blockDiagonal' op * (Matrix.blockDiagonal' op)ᴴ = 1 := by
  refine ⟨directSum_isometry op (fun b => (h b).1), ?_⟩
  rw [Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul]
  simpa only [fun b => (h b).2] using (Matrix.blockDiagonal'_one (m' := B) (α := ℂ))

/-- Exact per-label equations compose into a single commuting square for
a coherent selection. The source encodings can have different dimensions
from the physical spaces, including unused physical basis coordinates. -/
theorem directSum_intertwines {L : Type*} [Fintype L] [DecidableEq L] {A B P Q : L → Type*}
    [∀ b, Fintype (B b)] [∀ b, Fintype (P b)]
    (logical : ∀ b, Matrix (B b) (A b) ℂ) (physical : ∀ b, Matrix (Q b) (P b) ℂ)
    (encodeIn : ∀ b, Matrix (P b) (A b) ℂ) (encodeOut : ∀ b, Matrix (Q b) (B b) ℂ)
    (square : ∀ b, physical b * encodeIn b = encodeOut b * logical b) :
    Matrix.blockDiagonal' physical * Matrix.blockDiagonal' encodeIn =
      Matrix.blockDiagonal' encodeOut * Matrix.blockDiagonal' logical := by
  rw [← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
  exact congrArg Matrix.blockDiagonal' (funext square)

/-- The original pre- and post-operations transport a coherent selection
through the encodings in the order in which the caller executes them. -/
theorem directSum_intertwines_comp {L : Type*} [Fintype L] [DecidableEq L]
    {A B P Q : L → Type*} [∀ b, Fintype (A b)] [∀ b, Fintype (B b)]
    [∀ b, Fintype (P b)] [∀ b, Fintype (Q b)]
    {X Y U V : Type*} [Fintype U] [Fintype Y]
    (logical : ∀ b, Matrix (B b) (A b) ℂ) (physical : ∀ b, Matrix (Q b) (P b) ℂ)
    (encodeIn : ∀ b, Matrix (P b) (A b) ℂ) (encodeOut : ∀ b, Matrix (Q b) (B b) ℂ)
    (preLogical : Matrix (Σ b, A b) X ℂ) (prePhysical : Matrix (Σ b, P b) U ℂ)
    (postLogical : Matrix Y (Σ b, B b) ℂ) (postPhysical : Matrix V (Σ b, Q b) ℂ)
    (encodeStart : Matrix U X ℂ) (encodeEnd : Matrix V Y ℂ)
    (pre : prePhysical * encodeStart = Matrix.blockDiagonal' encodeIn * preLogical)
    (arms : ∀ b, physical b * encodeIn b = encodeOut b * logical b)
    (post : postPhysical * Matrix.blockDiagonal' encodeOut = encodeEnd * postLogical) :
    (postPhysical * Matrix.blockDiagonal' physical * prePhysical) * encodeStart =
      encodeEnd * (postLogical * Matrix.blockDiagonal' logical * preLogical) := by
  have selection := directSum_intertwines logical physical encodeIn encodeOut arms
  simp only [Matrix.mul_assoc]
  rw [pre, ← Matrix.mul_assoc (Matrix.blockDiagonal' physical), selection]
  rw [Matrix.mul_assoc (Matrix.blockDiagonal' encodeOut)]
  rw [← Matrix.mul_assoc postPhysical, post]
  simp only [Matrix.mul_assoc]

/-- Each output coordinate uses its original label's input amplitudes.
The joint input can carry arbitrary correlations with a reference. -/
theorem directSum_action {L : Type*} [Fintype L] [DecidableEq L] {A B : L → Type*}
    [∀ b, Fintype (A b)] {R : Type*}
    (op : ∀ b, Matrix (B b) (A b) ℂ) (joint : (Σ b, A b) → R → ℂ)
    (label : L) (output : B label) (reference : R) :
    (Matrix.blockDiagonal' op *ᵥ (fun input => joint input reference)) ⟨label, output⟩ =
      (op label *ᵥ (fun input => joint ⟨label, input⟩ reference)) output := by
  simp only [Matrix.mulVec, dotProduct, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  rw [Fintype.sum_eq_single label]
  · simp
  · intro other different
    exact Finset.sum_eq_zero fun input _ => by
      rw [Matrix.blockDiagonal'_apply_ne op output input different.symm, zero_mul]

end
end QPTL.FiniteMatrix
