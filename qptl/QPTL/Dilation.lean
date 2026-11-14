/-
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
-/
import QPTL.Tensor

/-! Exact recovery of an encoded dilation on the image of its logical map. -/

namespace QPTL
open CategoryTheory MonoidalCategory

universe v u
variable {C : Type u} [Category.{v} C] [DaggerCategory C]

/-- The logical image operator fixes every output of an isometry. -/
theorem IsIsometry.image_fixes {A B : C} {f : A ⟶ B} (isometry : IsIsometry f) :
    f ≫ (f† ≫ f) = f := by
  rw [← Category.assoc, isometry, Category.id_comp]

/-- An implementation inverse recovers the input encoding on states produced by
the dilation. The exact square identifies which output encoding is recovered. -/
theorem dilation_recover {A B P Q : C} {logical : A ⟶ B}
    {encodeIn : A ⟶ P} {encodeOut : B ⟶ Q} {physical : P ⟶ Q}
    (square : CommSq logical encodeIn encodeOut physical) (unitary : IsUnitary physical) :
    logical ≫ (encodeOut ≫ physical†) = encodeIn := by
  rw [← Category.assoc, square.w, Category.assoc, unitary.isometry, Category.comp_id]

/-- Recovery applies to arbitrary joint inputs with an untouched reference.
The confirmation uses the original forward image, with its exact phase. -/
theorem dilation_recover_reference [MonoidalCategory C]
    {A B P Q S R : C} {logical : A ⟶ B}
    {encodeIn : A ⟶ P} {encodeOut : B ⟶ Q} {physical : P ⟶ Q}
    (square : CommSq logical encodeIn encodeOut physical) (unitary : IsUnitary physical)
    (input : S ⟶ A ⊗ R) :
    input ≫ (((logical ≫ encodeOut) ⊗ₘ 𝟙 R) ≫ (physical† ⊗ₘ 𝟙 R)) =
      input ≫ (encodeIn ⊗ₘ 𝟙 R) := by
  have recovered := dilation_recover square unitary
  apply congrArg (input ≫ ·)
  calc
    _ = ((logical ≫ encodeOut) ≫ physical†) ⊗ₘ (𝟙 R ≫ 𝟙 R) :=
      tensorHom_comp_tensorHom _ _ _ _
    _ = _ := by rw [Category.comp_id, Category.assoc, recovered]

#print axioms IsIsometry.image_fixes
#print axioms dilation_recover_reference

end QPTL
