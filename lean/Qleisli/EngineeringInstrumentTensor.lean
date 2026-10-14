import Qleisli.EngineeringInstrumentComposition

/-! Ordered engineering instrument tensor composition. Explicit coordinate
isometries regroup the untouched system and arbitrary finite reference. All
public results and hidden histories remain in their declared product order.
These are engineering norm theorems, not source/QIRF preservation or native
composition certificates; exact/control/cleanup and resource authority remain
separate, including at zero budget.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.EngineeringInstrumentTensor
open Qleisli.Semantics.EngineeringInstrument
open Qleisli.Semantics.EngineeringInstrumentComposition
open scoped BigOperators

noncomputable def axes {A B : Type} [Fintype A] [Fintype B] (e : A ≃ B) :
    EuclideanSpace ℂ A ≃ₗᵢ[ℂ] EuclideanSpace ℂ B :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e

@[simp] theorem axes_apply {A B : Type} [Fintype A] [Fintype B] (e : A ≃ B)
    (vector : EuclideanSpace ℂ A) (b : B) : axes e vector b = vector (e.symm b) := rfl

noncomputable def axisMap {A B : Type} [Fintype A] [Fintype B] (e : A ≃ B) :
    EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ B :=
  (axes e : EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ B)

@[simp] theorem axisMap_apply {A B : Type} [Fintype A] [Fintype B] (e : A ≃ B)
    (vector : EuclideanSpace ℂ A) (b : B) : axisMap e vector b = vector (e.symm b) := rfl

theorem axisMap_norm_le {A B : Type} [Fintype A] [Fintype B] (e : A ≃ B) :
    ‖axisMap e‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro vector
  simpa only [one_mul] using (axes e).norm_map vector |>.le

theorem axisMap_adjoint {A B : Type} [Fintype A] [Fintype B] (e : A ≃ B) :
    (axisMap e).adjoint = axisMap e.symm := by
  simp only [axisMap,LinearIsometryEquiv.adjoint_eq_symm,axes,
    LinearIsometryEquiv.piLpCongrLeft_symm]

def leftAxes (I S R : Type) : ((I × S) × R) ≃ (I × (S × R)) where
  toFun p := (p.1.1,(p.1.2,p.2))
  invFun p := ((p.1,p.2.1),p.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def rightAxes (I S R : Type) : ((S × I) × R) ≃ (I × (S × R)) where
  toFun p := (p.1.2,(p.1.1,p.2))
  invFun p := ((p.2.1,p.1),p.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem liftLeft_extendLeft {I O S R : Type}
    [Fintype I] [Fintype O] [Fintype S] [Fintype R] (matrix : Matrix O I ℂ) :
    liftLeft (liftLeftMatrix (S := S) matrix) R =
      (axisMap (leftAxes O S R)).adjoint ∘L liftLeft matrix (S × R) ∘L
        axisMap (leftAxes I S R) := by
  classical
  rw [axisMap_adjoint]
  ext joint pair
  rcases pair with ⟨⟨o,s⟩,r⟩
  simp [Qleisli.EngineeringInstrument.liftLeft_apply,ContinuousLinearMap.comp_apply,
    axisMap_apply,leftAxes,liftLeftMatrix,Fintype.sum_prod_type]

theorem liftLeft_extendRight {I O S R : Type}
    [Fintype I] [Fintype O] [Fintype S] [Fintype R] (matrix : Matrix O I ℂ) :
    liftLeft (liftRightMatrix (S := S) matrix) R =
      (axisMap (rightAxes O S R)).adjoint ∘L liftLeft matrix (S × R) ∘L
        axisMap (rightAxes I S R) := by
  classical
  rw [axisMap_adjoint]
  ext joint pair
  rcases pair with ⟨⟨s,o⟩,r⟩
  simp [Qleisli.EngineeringInstrument.liftLeft_apply,ContinuousLinearMap.comp_apply,
    axisMap_apply,rightAxes,liftRightMatrix,Fintype.sum_prod_type]

theorem conjugate_norm_le {A B : Type} [Fintype A] [Fintype B]
    (e : A ≃ B) (operator : EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B) :
    ‖(axisMap e).adjoint ∘L operator ∘L axisMap e‖ ≤ ‖operator‖ := by
  calc
    _ ≤ ‖(axisMap e).adjoint‖ * (‖operator‖ * ‖axisMap e‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ = ‖axisMap e‖ * (‖operator‖ * ‖axisMap e‖) := by rw [LinearIsometryEquiv.norm_map]
    _ ≤ 1 * (‖operator‖ * 1) := by gcongr <;> exact axisMap_norm_le e
    _ = _ := by ring

theorem adjoint_extendLeft {X Y H I O S R : Type}
    [Fintype Y] [Fintype H] [Fintype I] [Fintype O] [Fintype S] [Fintype R]
    (operators : Kraus X Y H I O) (observables : Observable Y (O × S) R) (input : X) :
    adjointWithReference (extendLeft operators) observables input =
      (axisMap (leftAxes I S R)).adjoint ∘L
        adjointWithReference operators
          (fun y => axisMap (leftAxes O S R) ∘L observables y ∘L
            (axisMap (leftAxes O S R)).adjoint) input ∘L axisMap (leftAxes I S R) := by
  simp only [adjointWithReference,extendLeft,liftLeft_extendLeft,
    ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.comp_assoc,ContinuousLinearMap.comp_finsetSum,
    ContinuousLinearMap.finsetSum_comp]

theorem adjoint_extendRight {X Y H I O S R : Type}
    [Fintype Y] [Fintype H] [Fintype I] [Fintype O] [Fintype S] [Fintype R]
    (operators : Kraus X Y H I O) (observables : Observable Y (S × O) R) (input : X) :
    adjointWithReference (extendRight operators) observables input =
      (axisMap (rightAxes I S R)).adjoint ∘L
        adjointWithReference operators
          (fun y => axisMap (rightAxes O S R) ∘L observables y ∘L
            (axisMap (rightAxes O S R)).adjoint) input ∘L axisMap (rightAxes I S R) := by
  simp only [adjointWithReference,extendRight,liftLeft_extendRight,
    ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.comp_assoc,ContinuousLinearMap.comp_finsetSum,
    ContinuousLinearMap.finsetSum_comp]

theorem forward_conjugate_norm_le {A B : Type} [Fintype A] [Fintype B]
    (e : A ≃ B) (operator : EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A) :
    ‖axisMap e ∘L operator ∘L (axisMap e).adjoint‖ ≤ ‖operator‖ := by
  have h := conjugate_norm_le e.symm operator
  simpa only [axisMap_adjoint,Equiv.symm_symm] using h

theorem extendLeft_bound {X Y H K I O S : Type}
    [Fintype Y] [Fintype H] [Fintype K] [Fintype I] [Fintype O] [Fintype S]
    (actual : Kraus X Y H I O) (ideal : Kraus X Y K I O) (epsilon : ℝ)
    (bound : CompleteAdjointBound actual ideal epsilon) :
    CompleteAdjointBound (extendLeft (S := S) actual) (extendLeft ideal) epsilon := by
  refine ⟨bound.1,?_⟩
  intro R _ observables input
  let transformed : Observable Y O (S × R) :=
    fun y => axisMap (leftAxes O S R) ∘L observables y ∘L (axisMap (leftAxes O S R)).adjoint
  have transformed_norm : ‖transformed‖ ≤ ‖observables‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro y
    exact (forward_conjugate_norm_le (leftAxes O S R) (observables y)).trans
      (norm_le_pi_norm observables y)
  have transport :
      adjointWithReference (extendLeft actual) observables input -
          adjointWithReference (extendLeft ideal) observables input =
        (axisMap (leftAxes I S R)).adjoint ∘L
          (adjointWithReference actual transformed input - adjointWithReference ideal transformed input) ∘L
            axisMap (leftAxes I S R) := by
    simp only [adjoint_extendLeft,ContinuousLinearMap.comp_sub,ContinuousLinearMap.sub_comp,transformed]
  rw [transport]
  exact (conjugate_norm_le (leftAxes I S R) _).trans
    ((bound.2 (S × R) transformed input).trans
      (mul_le_mul_of_nonneg_left transformed_norm bound.1))

theorem extendRight_bound {X Y H K I O S : Type}
    [Fintype Y] [Fintype H] [Fintype K] [Fintype I] [Fintype O] [Fintype S]
    (actual : Kraus X Y H I O) (ideal : Kraus X Y K I O) (epsilon : ℝ)
    (bound : CompleteAdjointBound actual ideal epsilon) :
    CompleteAdjointBound (extendRight (S := S) actual) (extendRight ideal) epsilon := by
  refine ⟨bound.1,?_⟩
  intro R _ observables input
  let transformed : Observable Y O (S × R) :=
    fun y => axisMap (rightAxes O S R) ∘L observables y ∘L (axisMap (rightAxes O S R)).adjoint
  have transformed_norm : ‖transformed‖ ≤ ‖observables‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro y
    exact (forward_conjugate_norm_le (rightAxes O S R) (observables y)).trans
      (norm_le_pi_norm observables y)
  have transport :
      adjointWithReference (extendRight actual) observables input -
          adjointWithReference (extendRight ideal) observables input =
        (axisMap (rightAxes I S R)).adjoint ∘L
          (adjointWithReference actual transformed input - adjointWithReference ideal transformed input) ∘L
            axisMap (rightAxes I S R) := by
    simp only [adjoint_extendRight,ContinuousLinearMap.comp_sub,ContinuousLinearMap.sub_comp,transformed]
  rw [transport]
  exact (conjugate_norm_le (rightAxes I S R) _).trans
    ((bound.2 (S × R) transformed input).trans
      (mul_le_mul_of_nonneg_left transformed_norm bound.1))

theorem extendLeft_gram {X Y H I O S : Type}
    [Fintype Y] [Fintype H] [Fintype I] [Fintype O] [Fintype S]
    [DecidableEq I] [DecidableEq S] (operators : Kraus X Y H I O)
    (gram : GramComplete operators) : GramComplete (extendLeft (S := S) operators) := by
  intro input
  classical
  ext a b
  rcases a with ⟨i,s⟩
  rcases b with ⟨j,t⟩
  by_cases hs : s = t
  · subst t
    have entry := congrArg (fun matrix : Matrix I I ℂ => matrix i j) (gram input)
    simpa [extendLeft,liftLeftMatrix,Matrix.sum_apply,
      Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_prod_type,Matrix.one_apply,
      ite_mul,mul_ite] using entry
  · simp [extendLeft,liftLeftMatrix,Matrix.sum_apply,
      Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_prod_type,
      mul_ite,hs,Ne.symm hs]

theorem extendRight_gram {X Y H I O S : Type}
    [Fintype Y] [Fintype H] [Fintype I] [Fintype O] [Fintype S]
    [DecidableEq I] [DecidableEq S] (operators : Kraus X Y H I O)
    (gram : GramComplete operators) : GramComplete (extendRight (S := S) operators) := by
  intro input
  classical
  ext a b
  rcases a with ⟨s,i⟩
  rcases b with ⟨t,j⟩
  by_cases hs : s = t
  · subst t
    have entry := congrArg (fun matrix : Matrix I I ℂ => matrix i j) (gram input)
    simpa [extendRight,liftRightMatrix,Matrix.sum_apply,
      Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_prod_type,Matrix.one_apply,
      ite_mul,mul_ite] using entry
  · simp [extendRight,liftRightMatrix,Matrix.sum_apply,
      Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_prod_type,
      mul_ite,hs,Ne.symm hs]

theorem tensor_as_product {I₁ I₂ O₁ O₂ : Type}
    [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
    (left : Matrix O₁ I₁ ℂ) (right : Matrix O₂ I₂ ℂ) :
    tensorMatrix left right =
      liftRightMatrix (S := O₁) right *
        liftLeftMatrix (S := I₂) left := by
  classical
  ext output input
  rcases output with ⟨o₁,o₂⟩
  rcases input with ⟨i₁,i₂⟩
  simp [tensorMatrix,liftLeftMatrix,
    liftRightMatrix,Matrix.mul_apply,Fintype.sum_prod_type]
  ring

theorem tensor_gram {X₁ X₂ Y₁ Y₂ H₁ H₂ I₁ I₂ O₁ O₂ : Type}
    [Fintype Y₁] [Fintype Y₂] [Fintype H₁] [Fintype H₂]
    [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
    [DecidableEq I₁] [DecidableEq I₂]
    (left : Kraus X₁ Y₁ H₁ I₁ O₁) (right : Kraus X₂ Y₂ H₂ I₂ O₂)
    (leftGram : GramComplete left)
    (rightGram : GramComplete right) : GramComplete (tensor left right) := by
  intro inputs
  classical
  have h := Qleisli.EngineeringInstrumentComposition.feedForward_gram
    (extendLeft (S := I₂) left)
    (fun _ : Y₁ => extendRight (S := O₁) right inputs.2)
    (extendLeft_gram left leftGram)
    (fun _ => extendRight_gram right rightGram inputs.2) inputs.1
  simpa only [feedForward,extendLeft,extendRight,
    tensor,tensor_as_product] using h

/-- Both matrices, every public result and every hidden history are retained.
The reference is explicitly regrouped using the proven axis equivalences; no
separability premise or reference-dimension multiplier occurs. -/
theorem tensor_bound {X₁ X₂ Y₁ Y₂ H₁ K₁ H₂ K₂ I₁ I₂ O₁ O₂ : Type}
    [Fintype Y₁] [Fintype Y₂] [Fintype H₁] [Fintype K₁] [Fintype H₂] [Fintype K₂]
    [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
    [DecidableEq I₁] [DecidableEq I₂]
    (actual₁ : Kraus X₁ Y₁ H₁ I₁ O₁) (ideal₁ : Kraus X₁ Y₁ K₁ I₁ O₁)
    (actual₂ : Kraus X₂ Y₂ H₂ I₂ O₂) (ideal₂ : Kraus X₂ Y₂ K₂ I₂ O₂)
    (actualRightGram : GramComplete actual₂)
    (idealLeftGram : GramComplete ideal₁)
    (epsilon₁ epsilon₂ : ℝ)
    (leftBound : CompleteAdjointBound actual₁ ideal₁ epsilon₁)
    (rightBound : CompleteAdjointBound actual₂ ideal₂ epsilon₂) :
    CompleteAdjointBound (tensor actual₁ actual₂) (tensor ideal₁ ideal₂) (epsilon₁ + epsilon₂) := by
  classical
  refine ⟨add_nonneg leftBound.1 rightBound.1,?_⟩
  intro R _ observables inputs
  have firstBound := extendLeft_bound (S := I₂) actual₁ ideal₁ epsilon₁ leftBound
  have secondBound : CompleteAdjointBound
      (fun _ : Y₁ => extendRight (S := O₁) actual₂ inputs.2)
      (fun _ : Y₁ => extendRight (S := O₁) ideal₂ inputs.2) epsilon₂ := by
    have component := extendRight_bound (S := O₁) actual₂ ideal₂ epsilon₂ rightBound
    exact ⟨component.1,fun S _ B _ => component.2 S B inputs.2⟩
  have composed := Qleisli.EngineeringInstrumentComposition.feedForward_bound
    (extendLeft (S := I₂) actual₁) (extendLeft (S := I₂) ideal₁)
    (fun _ : Y₁ => extendRight (S := O₁) actual₂ inputs.2)
    (fun _ : Y₁ => extendRight (S := O₁) ideal₂ inputs.2)
    (fun _ => extendRight_gram actual₂ actualRightGram inputs.2)
    (extendLeft_gram ideal₁ idealLeftGram)
    epsilon₁ epsilon₂ firstBound secondBound
  have h := composed.2 R observables inputs.1
  simpa only [adjointWithReference,feedForward,
    extendLeft,extendRight,tensor,tensor_as_product] using h

end Qleisli.EngineeringInstrumentTensor
