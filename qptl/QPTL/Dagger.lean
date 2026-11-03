/-
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.CategoryTheory.CommSq

/-! Dagger categories, isometries and exact transport along an encoding. -/

namespace QPTL
open CategoryTheory

universe v u

/-- An identity-on-objects, involutive contravariant action on morphisms. -/
class DaggerCategory (C : Type u) [Category.{v} C] where
  dagger {X Y : C} : (X ⟶ Y) → (Y ⟶ X)
  dagger_id (X : C) : dagger (𝟙 X) = 𝟙 X
  dagger_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    dagger (f ≫ g) = dagger g ≫ dagger f
  dagger_dagger {X Y : C} (f : X ⟶ Y) : dagger (dagger f) = f

scoped postfix:1024 "†" => DaggerCategory.dagger

attribute [simp] DaggerCategory.dagger_id DaggerCategory.dagger_comp DaggerCategory.dagger_dagger

variable {C : Type u} [Category.{v} C] [DaggerCategory C] {X Y Z : C}

/-- In diagrammatic order this is `f ≫ f† = 𝟙 X`. The codomain may differ. -/
def IsIsometry (f : X ⟶ Y) : Prop := f ≫ f† = 𝟙 X

/-- A unitary also has the inverse equation on its codomain. -/
structure IsUnitary (f : X ⟶ Y) : Prop where
  isometry : IsIsometry f
  coisometry : f† ≫ f = 𝟙 Y

theorem IsIsometry.id (X : C) : IsIsometry (𝟙 X) := by simp [IsIsometry]

/-- An isometric output embedding preserves and reflects isometry. -/
theorem IsIsometry.comp_iff {f : X ⟶ Y} {g : Y ⟶ Z} (hg : IsIsometry g) :
    IsIsometry (f ≫ g) ↔ IsIsometry f := by
  unfold IsIsometry at *
  rw [DaggerCategory.dagger_comp, Category.assoc, ← Category.assoc g, hg, Category.id_comp]

theorem IsIsometry.comp {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsIsometry f) (hg : IsIsometry g) :
    IsIsometry (f ≫ g) := hg.comp_iff.mpr hf

theorem IsUnitary.id (X : C) : IsUnitary (𝟙 X) := ⟨IsIsometry.id X, by simp⟩

theorem IsUnitary.dagger {f : X ⟶ Y} (hf : IsUnitary f) : IsUnitary f† := by
  exact ⟨by simpa only [IsIsometry, DaggerCategory.dagger_dagger] using hf.coisometry,
    by simpa only [DaggerCategory.dagger_dagger] using hf.isometry⟩

theorem IsUnitary.comp {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsUnitary f) (hg : IsUnitary g) :
    IsUnitary (f ≫ g) := by
  refine ⟨hf.isometry.comp hg.isometry, ?_⟩
  simpa only [IsIsometry, DaggerCategory.dagger_comp, DaggerCategory.dagger_dagger] using
    hg.dagger.isometry.comp hf.dagger.isometry

/-- An exact commuting square transfers a physical isometry to its logical
action. Both encodings may be rectangular. Mathlib's `CommSq.horiz_comp`
composes successive squares without identifying their intermediate objects. -/
theorem isometry_of_square {A B P Q : C} {logical : A ⟶ B} {physical : P ⟶ Q}
    {encodeIn : A ⟶ P} {encodeOut : B ⟶ Q} (square : CommSq logical encodeIn encodeOut physical)
    (hin : IsIsometry encodeIn) (hout : IsIsometry encodeOut) (hp : IsIsometry physical) :
    IsIsometry logical := by
  apply hout.comp_iff.mp
  rw [square.w]
  exact hin.comp hp

end QPTL
