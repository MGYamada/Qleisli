import QleisliKernel.Qirf.EngineeringPureTensor
import Qleisli.EngineeringPureComposition
import Qleisli.ExactMatrix

/-! Actual ordered tensor engineering refinement. Engineering-only: no accepted handle,
source preservation, controlled access, cleanup or resource promotion.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.NativeEngineeringPureTensor
open scoped BigOperators
open Qleisli.EngineeringPureComposition

noncomputable def coordinates {I J : Type} [Fintype I] [Fintype J]
    (e : I ≃ J) : EuclideanSpace ℂ I ≃ₗᵢ[ℂ] EuclideanSpace ℂ J :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e

@[simp] theorem coordinates_apply {I J : Type} [Fintype I] [Fintype J]
    (e : I ≃ J) (v : EuclideanSpace ℂ I) (j : J) :
    coordinates e v j = v (e.symm j) := rfl

@[simp] theorem coordinates_symm_apply {I J : Type} [Fintype I] [Fintype J]
    (e : I ≃ J) (v : EuclideanSpace ℂ J) (i : I) :
    (coordinates e).symm v i = v (e i) := by
  rw [coordinates, LinearIsometryEquiv.piLpCongrLeft_symm]
  rfl

/-- Coordinate transport is an exact permutation of the Euclidean operator. -/
theorem reindex_operator {I I' O O' : Type}
    [Fintype I] [Fintype I'] [Fintype O] [Fintype O']
    (input : I ≃ I') (output : O ≃ O') (matrix : Matrix O' I' ℂ) :
    operator (fun row col => matrix (output row) (input col)) =
      (coordinates output).symm.toLinearIsometry.toContinuousLinearMap.comp
        ((operator matrix).comp (coordinates input).toLinearIsometry.toContinuousLinearMap) := by
  ext vector row
  simp only [operator_apply, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    coordinates_apply, coordinates_symm_apply]
  exact Fintype.sum_equiv input _ _ (fun col => by simp)

theorem reindex_norm {I I' O O' : Type}
    [Fintype I] [Fintype I'] [Fintype O] [Fintype O']
    (input : I ≃ I') (output : O ≃ O') (matrix : Matrix O' I' ℂ) :
    ‖operator (fun row col => matrix (output row) (input col))‖ = ‖operator matrix‖ := by
  rw [reindex_operator, LinearIsometry.norm_toContinuousLinearMap_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

/-- Exact.Matrix.tensor places the first component in the low coordinate. -/
def lowEquiv (m n : Nat) : Fin m × Fin n ≃ Fin (m*n) :=
  (Equiv.prodComm (Fin m) (Fin n)).trans
    ((finProdFinEquiv : Fin n × Fin m ≃ Fin (n*m)).trans
      (finCongr (Nat.mul_comm n m)))

@[simp] theorem lowEquiv_val (m n : Nat) (p : Fin m × Fin n) :
    (lowEquiv m n p).val = p.1.val + m*p.2.val := by
  simp [lowEquiv, finProdFinEquiv]

/-- The actual bounded exact tensor result is identified entry by entry;
no producer summary, width-only identification or phase quotient is used. -/
theorem exact_tensor_matrix
    (x y z : QleisliKernel.Semantics.Exact.Matrix) (work left : Nat)
    (ok : QleisliKernel.Exact.Matrix.tensor x y work = (.ok z,left)) :
    (fun row : Fin x.rows × Fin y.rows => fun col : Fin x.cols × Fin y.cols =>
      Qleisli.Semantics.Exact.entry z (lowEquiv x.rows y.rows row)
        (lowEquiv x.cols y.cols col)) =
      tensor (matrixAt x.rows x.cols x) (matrixAt y.rows y.cols y) := by
  ext row col
  simp only [lowEquiv_val, tensor, matrixAt]
  exact Qleisli.Exact.tensor_low_coordinate x y z work left ok _ _ _ _
    row.1.isLt row.2.isLt col.1.isLt col.2.isLt

/-- Known component dimensions are carried explicitly through the exact operation. -/
theorem exact_tensor_at (r₁ c₁ r₂ c₂ : Nat)
    (x y z : QleisliKernel.Semantics.Exact.Matrix) (work left : Nat)
    (ok : QleisliKernel.Exact.Matrix.tensor x y work = (.ok z,left))
    (xr : x.rows = r₁) (xc : x.cols = c₁) (yr : y.rows = r₂) (yc : y.cols = c₂) :
    (fun row : Fin r₁ × Fin r₂ => fun col : Fin c₁ × Fin c₂ =>
      Qleisli.Semantics.Exact.entry z (lowEquiv r₁ r₂ row) (lowEquiv c₁ c₂ col)) =
      tensor (matrixAt r₁ c₁ x) (matrixAt r₂ c₂ y) := by
  subst r₁; subst c₁; subst r₂; subst c₂
  exact exact_tensor_matrix x y z work left ok

/-- The parent gap uses the component tensor inequality directly. Flattening
is an exact isometry, and does not multiply the error by a dimension factor. -/
theorem exact_tensor_gap_bound (r₁ c₁ r₂ c₂ : Nat)
    (actual₁ ideal₁ actual₂ ideal₂ parentActual parentIdeal : QleisliKernel.Semantics.Exact.Matrix)
    (aw al iw il : Nat)
    (aok : QleisliKernel.Exact.Matrix.tensor actual₁ actual₂ aw = (.ok parentActual,al))
    (iok : QleisliKernel.Exact.Matrix.tensor ideal₁ ideal₂ iw = (.ok parentIdeal,il))
    (ar₁ : actual₁.rows = r₁) (ac₁ : actual₁.cols = c₁)
    (ir₁ : ideal₁.rows = r₁) (ic₁ : ideal₁.cols = c₁)
    (ar₂ : actual₂.rows = r₂) (ac₂ : actual₂.cols = c₂)
    (ir₂ : ideal₂.rows = r₂) (ic₂ : ideal₂.cols = c₂)
    (epsilon : ℝ)
    (bound : ‖operator (tensor (matrixAt r₁ c₁ actual₁) (matrixAt r₂ c₂ actual₂) -
      tensor (matrixAt r₁ c₁ ideal₁) (matrixAt r₂ c₂ ideal₂))‖ ≤ epsilon) :
    ‖operator (matrixAt (r₁*r₂) (c₁*c₂) parentActual -
      matrixAt (r₁*r₂) (c₁*c₂) parentIdeal)‖ ≤ epsilon := by
  have actual := exact_tensor_at r₁ c₁ r₂ c₂ actual₁ actual₂ parentActual aw al aok ar₁ ac₁ ar₂ ac₂
  have ideal := exact_tensor_at r₁ c₁ r₂ c₂ ideal₁ ideal₂ parentIdeal iw il iok ir₁ ic₁ ir₂ ic₂
  have gap : (fun row : Fin r₁ × Fin r₂ => fun col : Fin c₁ × Fin c₂ =>
      (matrixAt (r₁*r₂) (c₁*c₂) parentActual -
        matrixAt (r₁*r₂) (c₁*c₂) parentIdeal) (lowEquiv r₁ r₂ row) (lowEquiv c₁ c₂ col)) =
      tensor (matrixAt r₁ c₁ actual₁) (matrixAt r₂ c₂ actual₂) -
        tensor (matrixAt r₁ c₁ ideal₁) (matrixAt r₂ c₂ ideal₂) := by
    change (fun row col => Qleisli.Semantics.Exact.entry parentActual _ _ -
      Qleisli.Semantics.Exact.entry parentIdeal _ _) = _
    rw [← actual, ← ideal]
    rfl
  rw [← gap, reindex_norm] at bound
  exact bound

open QleisliKernel.Qirf.EngineeringPureTensor
open QleisliKernel.Semantics.Finite

/-- Complete original component and parent meanings. The bound is a property
of the freshly reconstructed parent matrices, not a certificate summary. -/
structure Meaning (request : Request) (checked : Checked) : Prop where
  left : Qleisli.NativeEngineeringPure.Meaning request.left checked.left
  right : Qleisli.NativeEngineeringPure.Meaning request.right checked.right
  parentActual : Qleisli.NativeEngineeringPure.LeafMeaning request.parentActual
    request.domain request.codomain checked.parentActual
  parentIdeal : Qleisli.NativeEngineeringPure.LeafMeaning request.parentIdeal
    request.domain request.codomain checked.parentIdeal
  bound : Qleisli.Semantics.EngineeringPure.OperatorBound request.parentActual.required
    request.parentIdeal.required checked.epsilon

/-- Original-root checking, exact parent tensors, and additive composition are
connected to the same execution. No whole-parent Frobenius bound is assumed. -/
theorem check_meaning (request : Request) (checked : Checked) (work left : Nat)
    (ok : (check request).run work = (.ok checked,left)) : Meaning request checked := by
  have facts := check_postcondition _ _ _ _ ok
  obtain ⟨a,b,c,d,e,ec,f,fc,hl,hr,hpa,hpi,hat,_,hit,_,_⟩ := facts.execution
  have lm := Qleisli.NativeEngineeringPure.check_meaning _ _ _ _ hl
  have rm := Qleisli.NativeEngineeringPure.check_meaning _ _ _ _ hr
  have pa := Qleisli.NativeEngineeringPure.leaf_meaning _ _ _ _ _ _ hpa
  have pi := Qleisli.NativeEngineeringPure.leaf_meaning _ _ _ _ _ _ hpi
  rw [lm.actual.equation,rm.actual.equation,← facts.actualEquation,pa.equation] at hat
  rw [lm.ideal.equation,rm.ideal.equation,← facts.idealEquation,pi.equation] at hit
  have bounds := tensor_bound
    (portMatrix request.left.domain request.left.codomain request.left.actual.required)
    (portMatrix request.left.domain request.left.codomain request.left.ideal.required)
    (portMatrix request.right.domain request.right.codomain request.right.actual.required)
    (portMatrix request.right.domain request.right.codomain request.right.ideal.required)
    (meaning_isometries _ _ lm) (meaning_isometries _ _ rm) _ _
    lm.bound.2.2.1 rm.bound.2.2.1 (meaning_bound _ _ lm) (meaning_bound _ _ rm)
  have flat := exact_tensor_gap_bound
    (2^width request.left.codomain) (2^width request.left.domain)
    (2^width request.right.codomain) (2^width request.right.domain)
    request.left.actual.required request.left.ideal.required request.right.actual.required
    request.right.ideal.required request.parentActual.required request.parentIdeal.required
    d e ec f hat hit lm.actual.rows lm.actual.cols lm.ideal.rows lm.ideal.cols
    rm.actual.rows rm.actual.cols rm.ideal.rows rm.ideal.cols _ bounds
  have epsilon := Qleisli.Exact.coefficient_add_preserves _ _ _ facts.epsilonAdd
  have epsilonReal : (Qleisli.Semantics.Exact.rational checked.epsilon : ℝ) =
      (Qleisli.Semantics.Exact.rational request.left.epsilon : ℝ) +
        (Qleisli.Semantics.Exact.rational request.right.epsilon : ℝ) := by
    exact_mod_cast epsilon
  rw [← epsilonReal] at flat
  have rows : request.parentActual.required.rows =
      (2^width request.left.codomain)*(2^width request.right.codomain) := by
    rw [pa.rows,Request.codomain,Basis.width_pair,pow_add]
  have cols : request.parentActual.required.cols =
      (2^width request.left.domain)*(2^width request.right.domain) := by
    rw [pa.cols,Request.domain,Basis.width_pair,pow_add]
  refine ⟨lm,rm,pa,pi,?_,?_,?_,?_⟩
  · rw [pa.rows,pi.rows]
  · rw [pa.cols,pi.cols]
  · exact (Qleisli.EngineeringPure.dyadic_nonneg _).mpr facts.epsilonNonnegative
  · rw [← gap_operator,rows,cols]
    exact flat

/-- Arbitrary finite references preserve the literal parent budget. Quantum
inputs may be entangled with that reference; no product-state premise occurs. -/
theorem checked_reference_bound {R : Type} [Fintype R]
    (request : Request) (checked : Checked) (work left : Nat)
    (ok : (check request).run work = (.ok checked,left)) :
    ‖operator (liftLeft (R := R)
      (matrixAt request.parentActual.required.rows request.parentActual.required.cols
        request.parentActual.required -
        matrixAt request.parentActual.required.rows request.parentActual.required.cols
        request.parentIdeal.required))‖ ≤
      (Qleisli.Semantics.Exact.rational checked.epsilon : ℝ) := by
  have meaning := check_meaning _ _ _ _ ok
  apply liftLeft_bound _ _ meaning.bound.2.2.1
  rw [gap_operator]
  exact meaning.bound.2.2.2

end Qleisli.NativeEngineeringPureTensor
