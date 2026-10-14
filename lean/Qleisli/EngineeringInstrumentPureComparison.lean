import Qleisli.EngineeringInstrument
import Qleisli.EngineeringPureComposition
import Qleisli.Semantics.EngineeringInstrumentComposition

/-! One-way comparison of engineering metrics. A phase-sensitive
pure Euclidean operator gap and two exact isometry Gram equations imply an
all-reference instrument adjoint bound. The instrument bound cannot recover
pure phase, coherent-control access, cleanup, PR/RS or exact Meaning authority.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.EngineeringInstrumentPureComparison
open Qleisli.Semantics.EngineeringInstrument
open Qleisli.Semantics.EngineeringInstrumentComposition
open scoped BigOperators

theorem liftLeft_eq_operator {I O R : Type} [Fintype I] [Fintype O] [Fintype R]
    (matrix : Matrix O I ℂ) :
    Qleisli.Semantics.EngineeringInstrument.liftLeft matrix R =
      Qleisli.EngineeringPureComposition.operator
        (Qleisli.EngineeringPureComposition.liftLeft (R := R) matrix) := by
  ext joint pair
  rcases pair with ⟨row,reference⟩
  rw [Qleisli.EngineeringInstrument.liftLeft_apply,
    Qleisli.EngineeringPureComposition.liftLeft_apply,
    Qleisli.EngineeringPureComposition.operator_apply]

theorem liftLeft_sub {I O R : Type} [Fintype I] [Fintype O] [Fintype R]
    (actual ideal : Matrix O I ℂ) :
    Qleisli.Semantics.EngineeringInstrument.liftLeft (actual - ideal) R =
      Qleisli.Semantics.EngineeringInstrument.liftLeft actual R -
        Qleisli.Semantics.EngineeringInstrument.liftLeft ideal R := by
  simp only [liftLeft_eq_operator,Qleisli.EngineeringPureComposition.liftLeft_sub,
    Qleisli.EngineeringPureComposition.operator_sub]

theorem conjugation_bound {I O : Type} [Fintype I] [Fintype O]
    (actual ideal : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ O)
    (observable : EuclideanSpace ℂ O →L[ℂ] EuclideanSpace ℂ O)
    (delta : ℝ) (nonnegative : 0 ≤ delta)
    (actual_contractive : ‖actual‖ ≤ 1) (ideal_contractive : ‖ideal‖ ≤ 1)
    (gap : ‖actual - ideal‖ ≤ delta) :
    ‖actual.adjoint ∘L observable ∘L actual - ideal.adjoint ∘L observable ∘L ideal‖ ≤
      (2 * delta) * ‖observable‖ := by
  have telescope : actual.adjoint ∘L observable ∘L actual -
      ideal.adjoint ∘L observable ∘L ideal =
        (actual - ideal).adjoint ∘L observable ∘L actual +
          ideal.adjoint ∘L observable ∘L (actual - ideal) := by
    simp only [map_sub,ContinuousLinearMap.sub_comp,ContinuousLinearMap.comp_sub]
    abel
  rw [telescope]
  calc
    _ ≤ ‖(actual - ideal).adjoint ∘L observable ∘L actual‖ +
        ‖ideal.adjoint ∘L observable ∘L (actual - ideal)‖ := norm_add_le _ _
    _ ≤ ‖(actual - ideal).adjoint‖ * (‖observable‖ * ‖actual‖) +
        ‖ideal.adjoint‖ * (‖observable‖ * ‖actual - ideal‖) := by
      exact add_le_add
        ((ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)))
        ((ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)))
    _ = ‖actual - ideal‖ * (‖observable‖ * ‖actual‖) +
        ‖ideal‖ * (‖observable‖ * ‖actual - ideal‖) := by
      rw [LinearIsometryEquiv.norm_map,LinearIsometryEquiv.norm_map]
    _ ≤ delta * (‖observable‖ * 1) + 1 * (‖observable‖ * delta) := by
      gcongr
    _ = _ := by ring

theorem singleton_adjoint {I O R : Type} [Fintype I] [Fintype O] [Fintype R]
    (matrix : Matrix O I ℂ) (observables : Observable Unit O R) :
    adjointWithReference (singleton matrix) observables () =
      (Qleisli.Semantics.EngineeringInstrument.liftLeft matrix R).adjoint ∘L
        observables () ∘L Qleisli.Semantics.EngineeringInstrument.liftLeft matrix R := by
  simp [adjointWithReference,Qleisli.Semantics.EngineeringInstrumentComposition.singleton]

/-- Exact Gram equations derive both contractions. The phase-sensitive pure
gap is a sufficient one-way witness for the weaker instrument bound, with no
reference-dimension factor and no separability premise. -/
theorem pure_gap_completeAdjointBound {I O : Type} [Fintype I] [Fintype O] [DecidableEq I]
    (actual ideal : Matrix O I ℂ) (delta : ℝ) (nonnegative : 0 ≤ delta)
    (actual_gram : actual.conjTranspose * actual = 1)
    (ideal_gram : ideal.conjTranspose * ideal = 1)
    (gap : ‖Qleisli.EngineeringPureComposition.operator (actual - ideal)‖ ≤ delta) :
    CompleteAdjointBound (singleton actual) (singleton ideal) (2 * delta) := by
  have budget_nonnegative : 0 ≤ 2 * delta := mul_nonneg (by norm_num) nonnegative
  refine ⟨budget_nonnegative,?_⟩
  intro R _ observables input
  cases input
  have actual_contractive := Qleisli.EngineeringPureComposition.liftLeft_bound (R := R)
    actual 1 (by norm_num) (Qleisli.EngineeringPureComposition.gram_contractive actual actual_gram)
  have ideal_contractive := Qleisli.EngineeringPureComposition.liftLeft_bound (R := R)
    ideal 1 (by norm_num) (Qleisli.EngineeringPureComposition.gram_contractive ideal ideal_gram)
  have reference_gap := Qleisli.EngineeringPureComposition.liftLeft_bound (R := R)
    (actual - ideal) delta nonnegative gap
  rw [← liftLeft_eq_operator] at actual_contractive ideal_contractive reference_gap
  rw [liftLeft_sub] at reference_gap
  rw [singleton_adjoint,singleton_adjoint]
  exact (conjugation_bound _ _ _ delta nonnegative actual_contractive ideal_contractive reference_gap).trans
    (mul_le_mul_of_nonneg_left (norm_le_pi_norm observables ()) budget_nonnegative)

end Qleisli.EngineeringInstrumentPureComparison
