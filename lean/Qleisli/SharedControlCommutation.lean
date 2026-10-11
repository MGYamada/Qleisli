import Qleisli.HierarchicalRoutedPower
import Qleisli.HierarchicalTensorCoordinates

/-! A bounded proof component for issue #303: shared coherent control of
disjoint ordered target factors, connected to the actual hierarchy operators.
No ctrl/borrow access rule, owner identity claim or artifact acceptance is added.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.SharedControlCommutation
open Qleisli.CoordinateOperators Qleisli.HierarchicalOperators
open QleisliKernel.Hierarchical.Artifact
open scoped BigOperators Matrix

/-- The common control basis is retained. Both target factors may have width zero. -/
theorem block_tensor_commute {B : Type} [Fintype B] [DecidableEq B]
    (n m : Nat) (U : B → Matrix (Bits n) (Bits n) ℂ)
    (V : B → Matrix (Bits m) (Bits m) ℂ) :
    Qleisli.ControlledPowers.block (fun b => tensor (U b) (1 : Matrix (Bits m) (Bits m) ℂ)) *
        Qleisli.ControlledPowers.block (fun b => tensor (1 : Matrix (Bits n) (Bits n) ℂ) (V b)) =
      Qleisli.ControlledPowers.block (fun b => tensor (1 : Matrix (Bits n) (Bits n) ℂ) (V b)) *
        Qleisli.ControlledPowers.block (fun b => tensor (U b) (1 : Matrix (Bits m) (Bits m) ℂ)) := by
  rw [← Qleisli.ControlledPowers.block_mul,← Qleisli.ControlledPowers.block_mul]
  congr 1
  funext b
  rw [tensor_mul,tensor_mul]
  simp only [Matrix.mul_one,Matrix.one_mul]

/-- First-bit coherent control of the real ordered tensor operators commutes. -/
theorem controlled_tensor_commute (n m : Nat)
    (U : Matrix (Bits n) (Bits n) ℂ) (V : Matrix (Bits m) (Bits m) ℂ) :
    Qleisli.HierarchicalRoutedPower.controlled (n+m) (tensor U (1 : Matrix (Bits m) (Bits m) ℂ)) *
        Qleisli.HierarchicalRoutedPower.controlled (n+m) (tensor (1 : Matrix (Bits n) (Bits n) ℂ) V) =
      Qleisli.HierarchicalRoutedPower.controlled (n+m) (tensor (1 : Matrix (Bits n) (Bits n) ℂ) V) *
        Qleisli.HierarchicalRoutedPower.controlled (n+m) (tensor U (1 : Matrix (Bits m) (Bits m) ℂ)) := by
  have left : (fun b : Bool => tensor (if b then U else 1) (1 : Matrix (Bits m) (Bits m) ℂ)) =
      fun b => if b then tensor U (1 : Matrix (Bits m) (Bits m) ℂ) else 1 := by
    funext b
    cases b <;> simp [tensor_one_right,lift_one]
  have right : (fun b : Bool => tensor (1 : Matrix (Bits n) (Bits n) ℂ) (if b then V else 1)) =
      fun b => if b then tensor (1 : Matrix (Bits n) (Bits n) ℂ) V else 1 := by
    funext b
    cases b <;> simp [tensor_one_left,lift_one]
  have blocks := block_tensor_commute n m (fun b : Bool => if b then U else 1) (fun b : Bool => if b then V else 1)
  rw [left,right] at blocks
  let route := (Fin.consEquiv (fun _ : Fin (n+m+1) => Bool)).symm
  have routed := congrArg (fun M : Matrix (Bool × Bits (n+m)) (Bool × Bits (n+m)) ℂ =>
    M.submatrix route route) blocks
  simpa only [Qleisli.HierarchicalRoutedPower.controlled,Qleisli.ControlledPowers.controlled,
    Matrix.submatrix_mul_equiv,route] using routed

/-- Actual hierarchy tensor/control bodies, including their identity factors.
Input/output width premises describe the operator fragment, not owner permissions. -/
theorem apply_controlled_tensor_commute (targets joint : Interface) (n m : Nat)
    (U V : Operator)
    (ti : width targets.inputs = n+m) (tout : width targets.outputs = n+m)
    (ji : width joint.inputs = n+m+1) (jo : width joint.outputs = n+m+1)
    (ui : U.inputWidth = n) (uo : U.outputWidth = n)
    (vi : V.inputWidth = m) (vo : V.outputWidth = m) :
    let first := apply joint (.control true) [apply targets .tensor [U,identity m]]
    let second := apply joint (.control true) [apply targets .tensor [identity n,V]]
    matrixAt (n+m+1) (n+m+1) first * matrixAt (n+m+1) (n+m+1) second =
      matrixAt (n+m+1) (n+m+1) second * matrixAt (n+m+1) (n+m+1) first := by
  dsimp only
  have first : matrixAt (n+m+1) (n+m+1)
      (apply joint (.control true) [apply targets .tensor [U,identity m]]) =
      Qleisli.HierarchicalRoutedPower.controlled (n+m)
        (tensor (matrixAt n n U) (1 : Matrix (Bits m) (Bits m) ℂ)) := by
    rw [Qleisli.HierarchicalRoutedPower.apply_control_matrix joint (n+m) _ ji jo]
    rw [Qleisli.HierarchicalTensorCoordinates.apply_tensor_matrix targets n m U (identity m) ti tout ui uo rfl rfl]
    rw [matrix_identity]
  have second : matrixAt (n+m+1) (n+m+1)
      (apply joint (.control true) [apply targets .tensor [identity n,V]]) =
      Qleisli.HierarchicalRoutedPower.controlled (n+m)
        (tensor (1 : Matrix (Bits n) (Bits n) ℂ) (matrixAt m m V)) := by
    rw [Qleisli.HierarchicalRoutedPower.apply_control_matrix joint (n+m) _ ji jo]
    rw [Qleisli.HierarchicalTensorCoordinates.apply_tensor_matrix targets n m (identity n) V ti tout rfl rfl vi vo]
    rw [matrix_identity]
  rw [first,second]
  exact controlled_tensor_commute _ _ _ _

/-- Only the two constructed adjacent operators are exchanged in the actual
sequence body. Execution order is first list element first, matrix rightmost first. -/
theorem apply_sequence_adjacent_swap (targets joint : Interface) (n m : Nat)
    (U V : Operator) (before after : List Operator)
    (ti : width targets.inputs = n+m) (tout : width targets.outputs = n+m)
    (ji : width joint.inputs = n+m+1) (jo : width joint.outputs = n+m+1)
    (ui : U.inputWidth = n) (uo : U.outputWidth = n)
    (vi : V.inputWidth = m) (vo : V.outputWidth = m)
    (ready : ∀ child ∈ before ++ after,
      child.inputWidth = n+m+1 ∧ child.outputWidth = n+m+1) :
    let first := apply joint (.control true) [apply targets .tensor [U,identity m]]
    let second := apply joint (.control true) [apply targets .tensor [identity n,V]]
    matrixAt (n+m+1) (n+m+1) (apply joint .sequence (before ++ first :: second :: after)) =
      matrixAt (n+m+1) (n+m+1) (apply joint .sequence (before ++ second :: first :: after)) := by
  let first := apply joint (.control true) [apply targets .tensor [U,identity m]]
  let second := apply joint (.control true) [apply targets .tensor [identity n,V]]
  have firstWidth : first.inputWidth = n+m+1 ∧ first.outputWidth = n+m+1 := ⟨ji,jo⟩
  have secondWidth : second.inputWidth = n+m+1 ∧ second.outputWidth = n+m+1 := ⟨ji,jo⟩
  have widths (a b : Operator) (ha : a.inputWidth = n+m+1 ∧ a.outputWidth = n+m+1)
      (hb : b.inputWidth = n+m+1 ∧ b.outputWidth = n+m+1) :
      ∀ child ∈ before ++ a :: b :: after,
        child.inputWidth = n+m+1 ∧ child.outputWidth = n+m+1 := by
    intro child inside
    simp only [List.mem_append,List.mem_cons] at inside
    rcases inside with h | rfl | rfl | h
    · exact ready _ (List.mem_append_left _ h)
    · exact ha
    · exact hb
    · exact ready _ (List.mem_append_right _ h)
  change matrixAt _ _ (apply joint .sequence (before ++ first :: second :: after)) =
    matrixAt _ _ (apply joint .sequence (before ++ second :: first :: after))
  rw [Qleisli.HierarchicalFourier.apply_sequence_matrix joint (n+m+1) _ ji jo (widths first second firstWidth secondWidth)]
  rw [Qleisli.HierarchicalFourier.apply_sequence_matrix joint (n+m+1) _ ji jo (widths second first secondWidth firstWidth)]
  simp only [List.foldl_append,List.foldl_cons]
  have commute := apply_controlled_tensor_commute targets joint n m U V ti tout ji jo ui uo vi vo
  change matrixAt _ _ first * matrixAt _ _ second = matrixAt _ _ second * matrixAt _ _ first at commute
  rw [← Matrix.mul_assoc,← commute,Matrix.mul_assoc]

/-- The exact original sequence equality acts on every joint/reference amplitude.
No finite reference, normalization or product-state premise is required. -/
theorem apply_sequence_adjacent_swap_reference {R : Type}
    (targets joint : Interface) (n m : Nat) (U V : Operator) (before after : List Operator)
    (ti : width targets.inputs = n+m) (tout : width targets.outputs = n+m)
    (ji : width joint.inputs = n+m+1) (jo : width joint.outputs = n+m+1)
    (ui : U.inputWidth = n) (uo : U.outputWidth = n)
    (vi : V.inputWidth = m) (vo : V.outputWidth = m)
    (ready : ∀ child ∈ before ++ after,
      child.inputWidth = n+m+1 ∧ child.outputWidth = n+m+1)
    (ψ : Bits (n+m+1) → R → ℂ) (output : Bits (n+m+1)) (reference : R) :
    let first := apply joint (.control true) [apply targets .tensor [U,identity m]]
    let second := apply joint (.control true) [apply targets .tensor [identity n,V]]
    (matrixAt (n+m+1) (n+m+1) (apply joint .sequence (before ++ first :: second :: after)) *ᵥ
      (fun input => ψ input reference)) output =
      (matrixAt (n+m+1) (n+m+1) (apply joint .sequence (before ++ second :: first :: after)) *ᵥ
        (fun input => ψ input reference)) output := by
  have same := apply_sequence_adjacent_swap targets joint n m U V before after ti tout ji jo ui uo vi vo ready
  exact congrArg (fun M => (M *ᵥ (fun input => ψ input reference)) output) same

end Qleisli.SharedControlCommutation
