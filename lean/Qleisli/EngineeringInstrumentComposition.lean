import Qleisli.EngineeringInstrument
import Qleisli.EngineeringPureComposition
import Qleisli.Semantics.EngineeringInstrumentComposition

/-! Engineering instrument contraction and feed-forward composition. The
contractions below follow from original full Kraus Gram equations. These
mathematical constructions do not prove source/QIRF composition preservation,
consume a native composition certificate, or grant exact/control/cleanup or
resource authority, including at zero budget.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.EngineeringInstrumentComposition
open Qleisli.Semantics.EngineeringInstrument
open Qleisli.Semantics.EngineeringInstrumentComposition
open scoped BigOperators

noncomputable def stacked {T I O : Type} (matrices : T → Matrix O I ℂ) :
    Matrix (T × O) I ℂ := fun row col => matrices row.1 row.2 col

theorem stacked_gram {T I O : Type} [Fintype T] [Fintype O]
    (matrices : T → Matrix O I ℂ) :
    (stacked matrices).conjTranspose * stacked matrices =
      ∑ t, (matrices t).conjTranspose * matrices t := by
  classical
  ext i j
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,stacked,
    Fintype.sum_prod_type,Matrix.sum_apply]

theorem sum_norm_sq_of_gram {T I O : Type} [Fintype T] [Fintype I] [Fintype O]
    [DecidableEq I] (matrices : T → Matrix O I ℂ)
    (gram : ∑ t, (matrices t).conjTranspose * matrices t = 1)
    (vector : EuclideanSpace ℂ I) :
    ∑ t, ‖Qleisli.EngineeringPureComposition.operator (matrices t) vector‖ ^ 2 =
      ‖vector‖ ^ 2 := by
  have h := congrArg (fun value : ℝ => value ^ 2)
    (Qleisli.EngineeringPureComposition.gram_isometry (stacked matrices)
      (by rw [stacked_gram,gram]) vector)
  dsimp only at h
  rw [EuclideanSpace.norm_sq_eq,Fintype.sum_prod_type] at h
  simpa only [EuclideanSpace.norm_sq_eq,Qleisli.EngineeringPureComposition.operator_apply,
    stacked] using h

theorem sum_reference_norm_sq_of_gram {T I O R : Type}
    [Fintype T] [Fintype I] [Fintype O] [Fintype R] [DecidableEq I]
    (matrices : T → Matrix O I ℂ)
    (gram : ∑ t, (matrices t).conjTranspose * matrices t = 1)
    (joint : Joint I R) :
    ∑ t, ‖liftLeft (matrices t) R joint‖ ^ 2 = ‖joint‖ ^ 2 := by
  have fiber (r : R) := sum_norm_sq_of_gram matrices gram
    (WithLp.toLp 2 (fun i => joint (i,r)))
  have output (t : T) : ‖liftLeft (matrices t) R joint‖ ^ 2 =
      ∑ r : R, ‖Qleisli.EngineeringPureComposition.operator (matrices t)
        (WithLp.toLp 2 (fun i => joint (i,r)))‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq,Fintype.sum_prod_type,Finset.sum_comm]
    simp only [Qleisli.EngineeringInstrument.liftLeft_apply,EuclideanSpace.norm_sq_eq,
      Qleisli.EngineeringPureComposition.operator_apply]
  simp_rw [output]
  rw [Finset.sum_comm]
  simp_rw [fiber]
  rw [EuclideanSpace.norm_sq_eq,Fintype.sum_prod_type,Finset.sum_comm]
  simp only [EuclideanSpace.norm_sq_eq]

theorem adjoint_family_norm_le {T I O : Type} [Fintype T] [Fintype I] [Fintype O]
    (operators : T → EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ O)
    (energy : ∀ vector, ∑ t, ‖operators t vector‖ ^ 2 = ‖vector‖ ^ 2)
    (observables : T → EuclideanSpace ℂ O →L[ℂ] EuclideanSpace ℂ O)
    (M : ℝ) (nonnegative : 0 ≤ M) (observable_bound : ∀ t, ‖observables t‖ ≤ M) :
    ‖∑ t, (operators t).adjoint ∘L observables t ∘L operators t‖ ≤ M := by
  have cauchy (u v : EuclideanSpace ℂ I) :
      ∑ t, ‖operators t u‖ * ‖operators t v‖ ≤ ‖u‖ * ‖v‖ := by
    apply le_of_sq_le_sq _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    simpa only [energy,mul_pow] using
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun t => ‖operators t u‖) (fun t => ‖operators t v‖)
  let combined := ∑ t, (operators t).adjoint ∘L observables t ∘L operators t
  have inner_bound (u v : EuclideanSpace ℂ I) :
      ‖inner ℂ u (combined v)‖ ≤ M * ‖u‖ * ‖v‖ := by
    calc
      _ = ‖∑ t, inner ℂ (operators t u) (observables t (operators t v))‖ := by
        simp only [combined,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,
          inner_sum,ContinuousLinearMap.adjoint_inner_right]
      _ ≤ ∑ t, ‖inner ℂ (operators t u) (observables t (operators t v))‖ := norm_sum_le _ _
      _ ≤ ∑ t, ‖operators t u‖ * (M * ‖operators t v‖) := by
        apply Finset.sum_le_sum
        intro t _
        exact (norm_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_left ((observables t).le_opNorm _ |>.trans
            (mul_le_mul_of_nonneg_right (observable_bound t) (norm_nonneg _))) (norm_nonneg _))
      _ = M * (∑ t, ‖operators t u‖ * ‖operators t v‖) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t _
        ring
      _ ≤ M * (‖u‖ * ‖v‖) := mul_le_mul_of_nonneg_left (cauchy u v) nonnegative
      _ = _ := by ring
  apply ContinuousLinearMap.opNorm_le_bound _ nonnegative
  intro v
  change ‖combined v‖ ≤ M * ‖v‖
  have h := inner_bound (combined v) v
  simp only [inner_self_eq_norm_sq_to_K,norm_pow,RCLike.norm_ofReal,
    abs_of_nonneg (norm_nonneg _)] at h
  have hn := norm_nonneg (combined v)
  have hm := mul_nonneg nonnegative (norm_nonneg v)
  nlinarith

/-- Full Kraus Gram completeness implies adjoint contraction for arbitrary
finite references and an arbitrary family of public-outcome observables. -/
theorem gram_completeAdjoint_contraction {X Y H I O : Type}
    [Fintype Y] [Fintype H] [Fintype I] [Fintype O] [DecidableEq I]
    (operators : Kraus X Y H I O)
    (gram : GramComplete operators) :
    ∀ (R : Type) [Fintype R] (observables : Observable Y O R) (input : X),
      ‖adjointWithReference operators observables input‖ ≤ ‖observables‖ := by
  intro R _ observables input
  have energy := sum_reference_norm_sq_of_gram (R := R)
    (fun pair : Y × H => operators input pair.1 pair.2)
    (by simpa only [Fintype.sum_prod_type] using gram input)
  have h := adjoint_family_norm_le
    (fun pair : Y × H => liftLeft (operators input pair.1 pair.2) R) energy
    (fun pair : Y × H => observables pair.1) ‖observables‖ (norm_nonneg _)
    (fun pair => norm_le_pi_norm observables pair.1)
  simpa only [adjointWithReference,Fintype.sum_prod_type] using h

theorem liftLeft_mul {I M O R : Type}
    [Fintype I] [Fintype M] [Fintype O] [Fintype R]
    (after : Matrix O M ℂ) (before : Matrix M I ℂ) :
    liftLeft (after * before) R = liftLeft after R ∘L liftLeft before R := by
  ext joint pair
  rcases pair with ⟨o,r⟩
  simp only [Qleisli.EngineeringInstrument.liftLeft_apply,ContinuousLinearMap.comp_apply,
    Matrix.mul_apply,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem adjoint_sub_observables {X Y H I O R : Type}
    [Fintype Y] [Fintype H] [Fintype I] [Fintype O] [Fintype R]
    (operators : Kraus X Y H I O) (left right : Observable Y O R) (input : X) :
    adjointWithReference operators (left - right) input =
      adjointWithReference operators left input - adjointWithReference operators right input := by
  simp only [adjointWithReference,Pi.sub_apply,ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.sub_comp,Finset.sum_sub_distrib]

theorem adjoint_feedForward {X Y Z H K I M O R : Type}
    [Fintype Y] [Fintype Z] [Fintype H] [Fintype K]
    [Fintype I] [Fintype M] [Fintype O] [Fintype R]
    (first : Kraus X Y H I M) (second : Kraus Y Z K M O)
    (observables : Observable (Y × Z) O R) (input : X) :
    adjointWithReference (feedForward first second) observables input =
      adjointWithReference first
        (fun y => adjointWithReference second (fun z => observables (y,z)) y) input := by
  simp only [adjointWithReference,feedForward,Fintype.sum_prod_type,liftLeft_mul,
    ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.comp_assoc,
    ContinuousLinearMap.comp_finsetSum,ContinuousLinearMap.finsetSum_comp]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_comm]

/-- Composition keeps all histories and is complete whenever both original
families are complete. This permits the norm argument to be iterated. -/
theorem feedForward_gram {X Y Z H K I M O : Type}
    [Fintype Y] [Fintype Z] [Fintype H] [Fintype K]
    [Fintype I] [Fintype M] [Fintype O] [DecidableEq I] [DecidableEq M]
    (first : Kraus X Y H I M) (second : Kraus Y Z K M O)
    (firstGram : GramComplete first)
    (secondGram : GramComplete second) : GramComplete (feedForward first second) := by
  intro input
  simp only [feedForward,Fintype.sum_prod_type,Matrix.conjTranspose_mul]
  have terms (y : Y) (h : H) :
      ∑ z, ∑ k, (first input y h).conjTranspose * (second y z k).conjTranspose *
          (second y z k * first input y h) =
        (first input y h).conjTranspose * first input y h := by
    calc
      _ = (first input y h).conjTranspose *
          (∑ z, ∑ k, (second y z k).conjTranspose * second y z k) * first input y h := by
        simp only [Matrix.sum_mul,Matrix.mul_sum,Matrix.mul_assoc]
      _ = _ := by rw [secondGram]; simp only [Matrix.mul_one]
  calc
    _ = ∑ y, ∑ h, ∑ z, ∑ k,
        (first input y h).conjTranspose * (second y z k).conjTranspose *
          (second y z k * first input y h) := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_comm]
    _ = _ := by simp_rw [terms]; exact firstGram input

/-- Exact completeness of the actual second instrument and the ideal first
instrument derives the two contractions used by the telescoping argument.
All public results are retained and each second-stage choice uses the matching
first-stage public result. The reference and input may remain entangled. -/
theorem feedForward_bound {X Y Z H₁ K₁ H₂ K₂ I M O : Type}
    [Fintype Y] [Fintype Z] [Fintype H₁] [Fintype K₁] [Fintype H₂] [Fintype K₂]
    [Fintype I] [Fintype M] [Fintype O] [DecidableEq I] [DecidableEq M]
    (actual₁ : Kraus X Y H₁ I M) (ideal₁ : Kraus X Y K₁ I M)
    (actual₂ : Kraus Y Z H₂ M O) (ideal₂ : Kraus Y Z K₂ M O)
    (actualSecondGram : GramComplete actual₂)
    (idealFirstGram : GramComplete ideal₁)
    (epsilon₁ epsilon₂ : ℝ)
    (firstBound : CompleteAdjointBound actual₁ ideal₁ epsilon₁)
    (secondBound : CompleteAdjointBound actual₂ ideal₂ epsilon₂) :
    CompleteAdjointBound (feedForward actual₁ actual₂) (feedForward ideal₁ ideal₂)
      (epsilon₁ + epsilon₂) := by
  refine ⟨add_nonneg firstBound.1 secondBound.1,?_⟩
  intro R _ observables input
  let actualAfter : Observable Y M R :=
    fun y => adjointWithReference actual₂ (fun z => observables (y,z)) y
  let idealAfter : Observable Y M R :=
    fun y => adjointWithReference ideal₂ (fun z => observables (y,z)) y
  have slice_bound (y : Y) : ‖fun z => observables (y,z)‖ ≤ ‖observables‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro z
    exact norm_le_pi_norm observables (y,z)
  have after_bound : ‖actualAfter‖ ≤ ‖observables‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro y
    exact (Qleisli.EngineeringInstrumentComposition.gram_completeAdjoint_contraction
      actual₂ actualSecondGram R (fun z => observables (y,z)) y).trans (slice_bound y)
  have after_gap : ‖actualAfter - idealAfter‖ ≤ epsilon₂ * ‖observables‖ := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg secondBound.1 (norm_nonneg _))).mpr
    intro y
    exact (secondBound.2 R (fun z => observables (y,z)) y).trans
      (mul_le_mul_of_nonneg_left (slice_bound y) secondBound.1)
  have left_bound := firstBound.2 R actualAfter input
  have right_bound := Qleisli.EngineeringInstrumentComposition.gram_completeAdjoint_contraction
    ideal₁ idealFirstGram R (actualAfter - idealAfter) input
  rw [adjoint_sub_observables] at right_bound
  rw [adjoint_feedForward,adjoint_feedForward]
  change ‖adjointWithReference actual₁ actualAfter input -
    adjointWithReference ideal₁ idealAfter input‖ ≤ _
  calc
    _ = ‖(adjointWithReference actual₁ actualAfter input -
        adjointWithReference ideal₁ actualAfter input) +
      (adjointWithReference ideal₁ actualAfter input -
        adjointWithReference ideal₁ idealAfter input)‖ := by
      congr 1
      abel
    _ ≤ ‖adjointWithReference actual₁ actualAfter input -
          adjointWithReference ideal₁ actualAfter input‖ +
        ‖adjointWithReference ideal₁ actualAfter input -
          adjointWithReference ideal₁ idealAfter input‖ := norm_add_le _ _
    _ ≤ epsilon₁ * ‖actualAfter‖ + ‖actualAfter - idealAfter‖ := add_le_add left_bound right_bound
    _ ≤ epsilon₁ * ‖observables‖ + epsilon₂ * ‖observables‖ :=
      add_le_add (mul_le_mul_of_nonneg_left after_bound firstBound.1) after_gap
    _ = _ := by ring

end Qleisli.EngineeringInstrumentComposition
