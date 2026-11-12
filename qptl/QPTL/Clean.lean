/-
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
-/
import QPTL.Dagger

/-! Exact compute/use/uncompute squares. These are mathematical transport
laws, not inverse capabilities or acceptance rules. The declared encoding is
restored exactly; no marginal, phase quotient or discard appears. -/

namespace QPTL
open CategoryTheory

universe v u
variable {C : Type u} [Category.{v} C]

/-- A checked use on the computed image transports back to the original
encoding through the specified inverse. Input and output ports may differ.
The inverse equation is explicit and concerns the actual output computation. -/
theorem uncompute_square {A B P Q P' Q' : C}
    {logical : A ⟶ B} {encodeIn : A ⟶ P} {encodeOut : B ⟶ Q}
    {computeIn : P ⟶ P'} {computeOut : Q ⟶ Q'}
    {body : P' ⟶ Q'} {uncomputeOut : Q' ⟶ Q}
    (useSquare : CommSq logical (encodeIn ≫ computeIn) (encodeOut ≫ computeOut) body)
    (inverse : computeOut ≫ uncomputeOut = 𝟙 Q) :
    CommSq logical encodeIn encodeOut (computeIn ≫ body ≫ uncomputeOut) := by
  refine ⟨?_⟩
  calc
    logical ≫ encodeOut = (logical ≫ (encodeOut ≫ computeOut)) ≫ uncomputeOut := by
      simp only [Category.assoc, inverse, Category.comp_id]
    _ = ((encodeIn ≫ computeIn) ≫ body) ≫ uncomputeOut :=
      congrArg (fun action => action ≫ uncomputeOut) useSquare.w
    _ = encodeIn ≫ (computeIn ≫ body ≫ uncomputeOut) := by
      simp only [Category.assoc]

/-- For a unitary computation, its dagger supplies the exact inverse in the
same clean square. This theorem grants no source-level adjoint/control API. -/
theorem conjugate_square [DaggerCategory C] {A B P : C}
    {logical : A ⟶ B} {encodeIn : A ⟶ P} {encodeOut : B ⟶ P}
    {compute body : P ⟶ P}
    (useSquare : CommSq logical (encodeIn ≫ compute) (encodeOut ≫ compute) body)
    (unitary : IsUnitary compute) :
    CommSq logical encodeIn encodeOut (compute ≫ body ≫ compute†) :=
  uncompute_square useSquare unitary.isometry

end QPTL
