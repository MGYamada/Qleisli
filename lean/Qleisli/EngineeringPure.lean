import QleisliKernel.Engineering.Pure
import Qleisli.Semantics.EngineeringPure
import Qleisli.ExactMatrix
import Qleisli.Finite
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Refinement of the actual bounded engineering arithmetic to an independent
Euclidean operator inequality. Original-artifact and native-entry bridges are
separate modules; this arithmetic proof supplies no resource certificate or
constitutional discharge. Existing exact acceptance and cleanup gates are unchanged.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.EngineeringPure
open QleisliKernel.Semantics.Exact QleisliKernel.Engineering.Pure
open Qleisli.Semantics.Exact Qleisli.Semantics.EngineeringPure
open scoped BigOperators

theorem dyadic_nonneg (x : Coefficient) :
    0 ≤ (rational x : ℝ) ↔ 0 ≤ x.numerator := by
  unfold rational
  push_cast
  rw [le_div_iff₀ (by positivity)]
  norm_num

theorem dyadic_nonpos (x : Coefficient) :
    (rational x : ℝ) ≤ 0 ↔ x.numerator ≤ 0 := by
  unfold rational
  push_cast
  rw [div_le_iff₀ (by positivity)]
  norm_num

theorem squareGap_meaning (a b gap : Coefficient)
    (ok : squareGap a b = .ok gap) :
    rational gap = rational a ^ 2 - 2 * rational b ^ 2 := by
  unfold squareGap at ok
  obtain ⟨aa,ha,h⟩ := QleisliKernel.Exact.bind_success _ _ _ ok
  obtain ⟨bb,hb,h⟩ := QleisliKernel.Exact.bind_success _ _ _ h
  obtain ⟨twice,ht,h⟩ := QleisliKernel.Exact.bind_success _ _ _ h
  obtain ⟨negative,hn,h⟩ := QleisliKernel.Exact.bind_success _ _ _ h
  rw [Qleisli.Exact.coefficient_add_preserves _ _ _ h,
    Qleisli.Exact.coefficient_mul_preserves _ _ _ ha,
    Qleisli.Exact.coefficient_neg_preserves _ _ hn,
    Qleisli.Exact.coefficient_mul_preserves _ _ _ ht,
    Qleisli.Exact.coefficient_mul_preserves _ _ _ hb]
  norm_num [rational,Coefficient.integer,pow_two]
  ring

private theorem mixed_left (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 0) :
    0 ≤ a ^ 2 - 2 * b ^ 2 ↔ 0 ≤ a + b * Real.sqrt 2 := by
  let c := -b * Real.sqrt 2
  have hc : 0 ≤ c := mul_nonneg (neg_nonneg.mpr hb) (Real.sqrt_nonneg _)
  have hs : c ^ 2 = 2 * b ^ 2 := by
    dsimp [c]
    rw [mul_pow,neg_sq,Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
    ring
  constructor
  · intro h
    have hsq : c ^ 2 ≤ a ^ 2 := by rw [hs]; linarith
    have hca := (sq_le_sq₀ hc ha).mp hsq
    dsimp [c] at hca
    linarith
  · intro h
    have hca : c ≤ a := by dsimp [c]; linarith
    have hsq := (sq_le_sq₀ hc ha).mpr hca
    rw [hs] at hsq
    linarith

private theorem mixed_right (a b : ℝ) (ha : a ≤ 0) (hb : 0 ≤ b) :
    a ^ 2 - 2 * b ^ 2 ≤ 0 ↔ 0 ≤ a + b * Real.sqrt 2 := by
  have hc : 0 ≤ -a := neg_nonneg.mpr ha
  have hd : 0 ≤ b * Real.sqrt 2 := mul_nonneg hb (Real.sqrt_nonneg _)
  have hs : (b * Real.sqrt 2) ^ 2 = 2 * b ^ 2 := by
    rw [mul_pow,Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
    ring
  constructor
  · intro h
    have hsq : (-a) ^ 2 ≤ (b * Real.sqrt 2) ^ 2 := by rw [neg_sq,hs]; linarith
    have hca := (sq_le_sq₀ hc hd).mp hsq
    linarith
  · intro h
    have hca : -a ≤ b * Real.sqrt 2 := by linarith
    have hsq := (sq_le_sq₀ hc hd).mpr hca
    rw [neg_sq,hs] at hsq
    linarith

/-- Every successful Boolean, including false, has the independent real sign.
Malformed coefficients or bounded arithmetic failures establish no sign. -/
theorem realNonneg_correct (a b : Coefficient) (result : Bool)
    (ok : realNonneg a b = .ok result) :
    result = true ↔ 0 ≤ realPair a b := by
  unfold realNonneg at ok
  split at ok
  · cases ok
  · split at ok
    · rename_i ha
      have har := (dyadic_nonneg a).mpr ha
      split at ok
      · rename_i hb
        have hbr := (dyadic_nonneg b).mpr hb
        have same : result = true := (Except.ok.inj ok).symm
        simp only [same,true_iff,realPair]
        exact add_nonneg har (mul_nonneg hbr (Real.sqrt_nonneg _))
      · rename_i hb
        obtain ⟨gap,hg,h⟩ := QleisliKernel.Exact.bind_success _ _ _ ok
        have same : result = decide (0 ≤ gap.numerator) := (Except.ok.inj h).symm
        have value : (rational gap : ℝ) =
            (rational a : ℝ) ^ 2 - 2 * (rational b : ℝ) ^ 2 := by
          exact_mod_cast squareGap_meaning a b gap hg
        rw [same,decide_eq_true_eq,← dyadic_nonneg gap,value]
        exact mixed_left _ _ har ((dyadic_nonpos b).mpr (le_of_not_ge hb))
    · rename_i ha
      have har : (rational a : ℝ) < 0 := by
        exact lt_of_not_ge (fun h => ha ((dyadic_nonneg a).mp h))
      split at ok
      · rename_i hb
        have hbr := (dyadic_nonpos b).mpr hb
        have same : result = false := (Except.ok.inj ok).symm
        simp only [same,Bool.false_eq_true,false_iff,realPair]
        have product := mul_nonpos_of_nonpos_of_nonneg hbr (Real.sqrt_nonneg (2 : ℝ))
        linarith
      · rename_i hb
        obtain ⟨gap,hg,h⟩ := QleisliKernel.Exact.bind_success _ _ _ ok
        have same : result = decide (gap.numerator ≤ 0) := (Except.ok.inj h).symm
        have value : (rational gap : ℝ) =
            (rational a : ℝ) ^ 2 - 2 * (rational b : ℝ) ^ 2 := by
          exact_mod_cast squareGap_meaning a b gap hg
        rw [same,decide_eq_true_eq,← dyadic_nonpos gap,value]
        exact mixed_right _ _ har.le ((dyadic_nonneg b).mpr (le_of_not_ge hb))

theorem accumulate_meaning (actual ideal : Matrix) (sum result : Scalar)
    (index : Nat × Nat) (work left : Nat)
    (ok : (accumulate actual ideal sum index).run work = (.ok result,left)) :
    scalar result = scalar sum +
      (Complex.normSq (entry actual index.1 index.2 - entry ideal index.1 index.2) : ℂ) := by
  unfold accumulate at ok
  obtain ⟨negative,w₁,hn,h⟩ := QleisliKernel.Exact.work_bind_success _ _ _ _ _ ok
  obtain ⟨difference,w₂,hd,h⟩ := QleisliKernel.Exact.work_bind_success _ _ _ _ _ h
  obtain ⟨conjugate,w₃,hc,h⟩ := QleisliKernel.Exact.work_bind_success _ _ _ _ _ h
  obtain ⟨term,w₄,ht,h⟩ := QleisliKernel.Exact.work_bind_success _ _ _ _ _ h
  have hn := Qleisli.Exact.scalar_neg_preserves _ _
    (QleisliKernel.Exact.work_lift_success _ _ _ _ hn).1
  have hd := Qleisli.Exact.scalar_add_preserves _ _ _
    (QleisliKernel.Exact.work_lift_success _ _ _ _ hd).1
  have hc := Qleisli.Exact.scalar_conjugate_preserves _ _
    (QleisliKernel.Exact.work_lift_success _ _ _ _ hc).1
  have ht := Qleisli.Exact.scalar_mul_preserves _ _ _
    (QleisliKernel.Exact.work_lift_success _ _ _ _ ht).1
  have hs := Qleisli.Exact.scalar_add_preserves _ _ _
    (QleisliKernel.Exact.work_lift_success _ _ _ _ h).1
  rw [hs,ht,hc,hd,hn,sub_eq_add_neg,Complex.normSq_eq_conj_mul_self]
  rfl

private theorem range_sum (n : Nat) (f : Nat → ℂ) :
    ((List.range n).map f).sum = ∑ k : Fin n, f k := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ,List.map_append,List.sum_append,List.map_singleton,List.sum_singleton]
    rw [Fin.sum_univ_castSucc]
    simpa only [Fin.val_castSucc,Fin.val_last] using congrArg (fun z => z + f n) ih

private theorem sum_flatMap {A : Type} (xs : List A) (f : A → List ℂ) :
    (xs.flatMap f).sum = (xs.map fun a => (f a).sum).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [List.flatMap_cons,ih]

theorem coordinates_meaning (actual ideal : Matrix) :
    ((coordinates actual.rows actual.cols).map fun index =>
      (Complex.normSq (entry actual index.1 index.2 - entry ideal index.1 index.2) : ℂ)).sum =
      (squaredDistance actual ideal : ℂ) := by
  simp only [coordinates,List.map_flatMap,sum_flatMap,List.map_map]
  rw [range_sum]
  unfold squaredDistance
  push_cast
  apply Finset.sum_congr rfl
  intro row _
  rw [range_sum]
  rfl

/-- The actual charged fold equals the independently specified complex sum.
Every coordinate is retained, including scalar phase and rectangular rows. -/
theorem normSqDifference_meaning (actual ideal : Matrix) (sum : Scalar) (work left : Nat)
    (ok : (normSqDifferenceWork actual ideal).run work = (.ok sum,left)) :
    scalar sum = (squaredDistance actual ideal : ℂ) := by
  unfold normSqDifferenceWork at ok
  split at ok
  · cases ok
  · split at ok
    · cases ok
    · split at ok
      · cases ok
      · obtain ⟨_,middle,_,h⟩ := QleisliKernel.Exact.work_bind_success _ _ _ _ _ ok
        split at h
        · cases h
        · obtain ⟨_,after,_,h⟩ := QleisliKernel.Exact.work_bind_success _ _ _ _ _ h
          have meaning := Qleisli.Exact.work_fold_sum (accumulate actual ideal)
            (fun index => (Complex.normSq
              (entry actual index.1 index.2 - entry ideal index.1 index.2) : ℂ))
            (fun acc index value before after step =>
              accumulate_meaning actual ideal acc value index before after step)
            _ Scalar.zero sum after left h
          simpa only [Qleisli.Exact.scalar_zero_meaning,zero_add,coordinates_meaning] using meaning

theorem mulVec_square_le {I O : Type} [Fintype I] [Fintype O]
    (matrix : _root_.Matrix O I ℂ) (vector : I → ℂ) :
    (∑ row, ‖∑ col, matrix row col * vector col‖ ^ 2) ≤
      (∑ row, ∑ col, ‖matrix row col‖ ^ 2) * ∑ col, ‖vector col‖ ^ 2 := by
  have rowBound (row : O) :
      ‖∑ col, matrix row col * vector col‖ ^ 2 ≤
        (∑ col, ‖matrix row col‖ ^ 2) * ∑ col, ‖vector col‖ ^ 2 := by
    calc
      _ ≤ (∑ col, ‖matrix row col‖ * ‖vector col‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ =>
          mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
            (by simpa only [norm_mul] using
              (norm_sum_le Finset.univ (fun col => matrix row col * vector col)))
      _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  calc
    _ ≤ ∑ row, (∑ col, ‖matrix row col‖ ^ 2) * ∑ col, ‖vector col‖ ^ 2 :=
      Finset.sum_le_sum fun row _ => rowBound row
    _ = _ := by rw [Finset.sum_mul]

/-- The Frobenius square is a sufficient witness for the explicitly selected
Euclidean operator norm, not the default norm on Matrix entries. -/
theorem frobenius_operator_bound (actual ideal : Matrix) (epsilon : ℝ)
    (nonnegative : 0 ≤ epsilon) (bound : squaredDistance actual ideal ≤ epsilon ^ 2) :
    ‖gapCLM actual ideal‖ ≤ epsilon := by
  apply ContinuousLinearMap.opNorm_le_bound _ nonnegative
  intro vector
  have action := mulVec_square_le (gapMatrix actual.rows actual.cols actual ideal)
    (WithLp.ofLp vector)
  have matrixBound : (∑ row : Fin actual.rows, ∑ col : Fin actual.cols,
      ‖gapMatrix actual.rows actual.cols actual ideal row col‖ ^ 2) ≤ epsilon ^ 2 := by
    simpa only [Complex.sq_norm,squaredDistance] using bound
  have inputNonnegative : 0 ≤ ∑ col : Fin actual.cols, ‖(WithLp.ofLp vector) col‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have squared := action.trans (mul_le_mul_of_nonneg_right matrixBound inputNonnegative)
  have outputBound : ‖gapCLM actual ideal vector‖ ^ 2 ≤ (epsilon * ‖vector‖) ^ 2 := by
    simpa only [gapCLM,LinearMap.coe_toContinuousLinearMap',Matrix.toLpLin_apply,
      EuclideanSpace.norm_sq_eq,PiLp.toLp_apply,Complex.sq_norm,mul_pow,
      _root_.Matrix.mulVec,dotProduct] using squared
  exact le_of_sq_le_sq outputBound (mul_nonneg nonnegative (norm_nonneg _))

theorem scalar_re (x : Scalar) : (scalar x).re = realPair x.a x.b := by
  simp [scalar,realPair]

/-- Successful execution of the actual checker proves this engineering
inequality only. Even a zero budget does not promote it to an exact gate. -/
theorem checkMatrices_squaredDistance (actual ideal : Matrix) (epsilon : Coefficient)
    (checked : Checked) (work left : Nat)
    (ok : (checkMatrices actual ideal epsilon).run work = (.ok checked,left)) :
    actual.rows = ideal.rows ∧ actual.cols = ideal.cols ∧
      0 ≤ (rational epsilon : ℝ) ∧
      squaredDistance actual ideal ≤ (rational epsilon : ℝ) ^ 2 := by
  have facts := checkMatrices_conditions _ _ _ _ _ _ ok
  obtain ⟨before,after,hs⟩ := facts.sum
  have sumMeaning := normSqDifference_meaning actual ideal checked.squaredError before after hs
  obtain ⟨budget,negative,hb,hn,hm⟩ := facts.budget
  have budgetMeaning := Qleisli.Exact.coefficient_mul_preserves _ _ _ hb
  have budgetReal : (rational budget : ℝ) = (rational epsilon : ℝ) ^ 2 := by
    exact_mod_cast (show rational budget = rational epsilon ^ 2 by simpa only [pow_two] using budgetMeaning)
  have negativeMeaning := Qleisli.Exact.scalar_neg_preserves _ _ hn
  have marginMeaning := Qleisli.Exact.scalar_add_preserves _ _ _ hm
  have embedding : scalar ⟨budget,.integer 0,.integer 0,.integer 0⟩ = (rational budget : ℂ) := by
    simp [scalar,rational,Coefficient.integer]
  rw [embedding,negativeMeaning,sumMeaning] at marginMeaning
  have realMargin : realPair checked.margin.a checked.margin.b =
      (rational budget : ℝ) - squaredDistance actual ideal := by
    simpa [scalar_re] using congrArg Complex.re marginMeaning
  have nonnegative := (realNonneg_correct _ _ true facts.nonnegative).mp rfl
  rw [realMargin,budgetReal] at nonnegative
  have distance : squaredDistance actual ideal ≤ (rational epsilon : ℝ) ^ 2 := by linarith
  have epsNonnegative := (dyadic_nonneg epsilon).mpr facts.epsilonNonnegative
  exact ⟨facts.rows,facts.cols,epsNonnegative,distance⟩

theorem checkMatrices_bound (actual ideal : Matrix) (epsilon : Coefficient)
    (checked : Checked) (work left : Nat)
    (ok : (checkMatrices actual ideal epsilon).run work = (.ok checked,left)) :
    OperatorBound actual ideal epsilon := by
  obtain ⟨rows,cols,nonnegative,bound⟩ := checkMatrices_squaredDistance _ _ _ _ _ _ ok
  exact ⟨rows,cols,nonnegative,frobenius_operator_bound actual ideal _ nonnegative bound⟩

/-- Every finite reference is untouched. The joint input need not factor into
system/reference states, and its dimension does not inflate the error budget. -/
theorem checkMatrices_reference_square {R : Type} [Fintype R]
    (actual ideal : Matrix) (epsilon : Coefficient) (checked : Checked) (work left : Nat)
    (ok : (checkMatrices actual ideal epsilon).run work = (.ok checked,left))
    (joint : Fin actual.cols → R → ℂ) :
    (∑ reference, ∑ row : Fin actual.rows, Complex.normSq
      (∑ col : Fin actual.cols,
        gapMatrix actual.rows actual.cols actual ideal row col * joint col reference)) ≤
      (rational epsilon : ℝ) ^ 2 *
        ∑ reference, ∑ col : Fin actual.cols, Complex.normSq (joint col reference) := by
  have facts := checkMatrices_squaredDistance _ _ _ _ _ _ ok
  have matrixBound : (∑ row : Fin actual.rows, ∑ col : Fin actual.cols,
      ‖gapMatrix actual.rows actual.cols actual ideal row col‖ ^ 2) ≤
        (rational epsilon : ℝ) ^ 2 := by
    simpa only [Complex.sq_norm,squaredDistance] using facts.2.2.2
  have fiber (reference : R) :
      (∑ row : Fin actual.rows, Complex.normSq
        (∑ col : Fin actual.cols,
          gapMatrix actual.rows actual.cols actual ideal row col * joint col reference)) ≤
        (rational epsilon : ℝ) ^ 2 * ∑ col : Fin actual.cols,
          Complex.normSq (joint col reference) := by
    have action := mulVec_square_le (gapMatrix actual.rows actual.cols actual ideal)
      (fun col => joint col reference)
    have inputNonnegative : 0 ≤ ∑ col : Fin actual.cols, ‖joint col reference‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have bounded := action.trans (mul_le_mul_of_nonneg_right matrixBound inputNonnegative)
    simpa only [Complex.normSq_eq_norm_sq] using bounded
  calc
    _ ≤ ∑ reference, (rational epsilon : ℝ) ^ 2 *
        ∑ col : Fin actual.cols, Complex.normSq (joint col reference) :=
      Finset.sum_le_sum fun reference _ => fiber reference
    _ = _ := by rw [Finset.mul_sum]

end Qleisli.EngineeringPure
