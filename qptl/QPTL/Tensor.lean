/-
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
-/
import QPTL.Dagger
import Mathlib.CategoryTheory.Monoidal.Category

/-! Parallel composition in a dagger monoidal category. -/

namespace QPTL
open CategoryTheory MonoidalCategory

universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Parallel exact squares, with the order of both factors preserved. -/
theorem tensor_square {A B P Q A' B' P' Q' : C}
    {f : A ⟶ B} {i : A ⟶ P} {o : B ⟶ Q} {g : P ⟶ Q}
    {f' : A' ⟶ B'} {i' : A' ⟶ P'} {o' : B' ⟶ Q'} {g' : P' ⟶ Q'}
    (s : CommSq f i o g) (t : CommSq f' i' o' g') :
    CommSq (f ⊗ₘ f') (i ⊗ₘ i') (o ⊗ₘ o') (g ⊗ₘ g') :=
  ⟨by simp only [tensorHom_comp_tensorHom, s.w, t.w]⟩

/-- The tensor respects the dagger and the monoidal coherence maps are unitary. -/
class DaggerMonoidalCategory (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [DaggerCategory C] : Prop where
  dagger_tensor {A B P Q : C} (f : A ⟶ B) (g : P ⟶ Q) : (f ⊗ₘ g)† = f† ⊗ₘ g†
  associator_unitary (A B D : C) : IsUnitary (α_ A B D).hom
  leftUnitor_unitary (A : C) : IsUnitary (λ_ A).hom
  rightUnitor_unitary (A : C) : IsUnitary (ρ_ A).hom

attribute [simp] DaggerMonoidalCategory.dagger_tensor

variable [DaggerCategory C] [DaggerMonoidalCategory C] {A B P Q : C}

theorem IsIsometry.tensor {f : A ⟶ B} {g : P ⟶ Q} (hf : IsIsometry f) (hg : IsIsometry g) :
    IsIsometry (f ⊗ₘ g) := by
  unfold IsIsometry at *
  rw [DaggerMonoidalCategory.dagger_tensor, tensorHom_comp_tensorHom, hf, hg, id_tensorHom_id]

theorem IsUnitary.tensor {f : A ⟶ B} {g : P ⟶ Q} (hf : IsUnitary f) (hg : IsUnitary g) :
    IsUnitary (f ⊗ₘ g) := by
  refine ⟨hf.isometry.tensor hg.isometry, ?_⟩
  rw [DaggerMonoidalCategory.dagger_tensor, tensorHom_comp_tensorHom,
    hf.coisometry, hg.coisometry, id_tensorHom_id]

end QPTL
