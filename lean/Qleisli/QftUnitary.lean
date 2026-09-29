import Qleisli.QpeComplete
import Mathlib.LinearAlgebra.Matrix.SemiringInverse

/-! Whole-space unitarity of the actual accepted QFT graph coefficients.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.QftGraph
open scoped BigOperators Matrix
open Qleisli.Qpe

noncomputable def fourier (N : Nat) [NeZero N] : Matrix (ZMod N) (ZMod N) ℂ :=
  fun y j => (Real.sqrt N : ℂ) * star (weight y j)

theorem fourier_isometry (N : Nat) [NeZero N] : (fourier N)ᴴ * fourier N = 1 := by
  have square : (Real.sqrt N : ℂ)^2 = N := by
    exact_mod_cast Real.sq_sqrt (by positivity : (0 : ℝ) ≤ N)
  ext j k
  change (∑ y, star ((Real.sqrt N : ℂ) * star (weight y j)) *
    ((Real.sqrt N : ℂ) * star (weight y k))) = if j = k then 1 else 0
  calc
    _ = (Real.sqrt N : ℂ)^2 * ∑ y, star (weight y k) * weight y j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      simp only [star_mul]
      simp only [star_star]
      rw [Complex.star_def, Complex.conj_ofReal]
      ring
    _ = _ := by
      rw [square, weight_orthogonal]
      by_cases h : j = k
      · simp [h]
      · simp [h, Ne.symm h]

theorem fourier_coisometry (N : Nat) [NeZero N] : fourier N * (fourier N)ᴴ = 1 :=
  mul_eq_one_comm.mp (fourier_isometry N)

theorem root_normalization (N : Nat) [NeZero N] (z : ℂ) :
    (Real.sqrt N : ℂ) * (z / N) = z / (Real.sqrt N : ℂ) := by
  have square : (Real.sqrt N : ℂ)^2 = N := by
    exact_mod_cast Real.sq_sqrt (by positivity : (0 : ℝ) ≤ N)
  have nonzero : (Real.sqrt N : ℂ) ≠ 0 := by
    have positive : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr positive))
  rw [← square]
  field_simp

theorem fourier_entry {N : Nat} [NeZero N] (y j : Fin N) :
    fourier N (ZMod.finEquiv N y) (ZMod.finEquiv N j) =
      Complex.exp (2 * Real.pi * Complex.I * j.val * y.val / N) /
        (Real.sqrt N : ℂ) := by
  rw [fourier, weight_exponential]
  change (Real.sqrt N : ℂ) * ((starRingEnd ℂ) (_ / _)) = _
  simp only [map_div₀, ← Complex.exp_conj, map_mul,
    Complex.conj_ofReal, Complex.conj_natCast, Complex.conj_I, map_ofNat, map_neg]
  rw [root_normalization]
  congr 2
  ring

/-- Matrix entries come from the direct operational graph path sum. -/
noncomputable def matrix (width : Nat) (actual : QleisliKernel.QftGraph.Action) :
    Matrix (Fin width → Bool) (Fin width → Bool) ℂ :=
  fun output input => coefficient width actual input output

noncomputable def indexEquiv (width : Nat) : (Fin width → Bool) ≃ ZMod (2^width) :=
  (bitEquiv width).trans (ZMod.finEquiv (2^width)).toEquiv

/-- temporary (TP-005), importance P1: Current QFT projection interface. Replacement: full-artifact
Fourier acceptance with both inverse laws. Retire after actual reversal and H
binding, QPE/registry migration and public API compatibility review. Keep the
generic Fourier, normalization and index lemmas in this module. -/
theorem checked_matrix (definitions : List QleisliKernel.QftGraph.Definition)
    (entry width : Nat) (receipt : QleisliKernel.QftGraph.Receipt)
    (accepted : QleisliKernel.QftGraph.check definitions entry width = some receipt)
    (actual : QleisliKernel.QftGraph.Action)
    (meaning : QleisliKernel.QftGraph.denote definitions entry = some actual) :
    matrix width actual = (fourier (2^width)).submatrix (indexEquiv width) (indexEquiv width) := by
  ext output input
  rw [matrix, check_fourier definitions entry width receipt accepted actual meaning]
  change _ = fourier (2^width) (ZMod.finEquiv (2^width) (bitEquiv width output))
    (ZMod.finEquiv (2^width) (bitEquiv width input))
  rw [fourier_entry, bitEquiv_value, bitEquiv_value]
  simp only [Nat.cast_pow, Nat.cast_ofNat]

/-- temporary (TP-005), importance P1: Current QFT projection interface. Replacement: full-artifact
Fourier acceptance with both inverse laws. Retire after actual reversal and H
binding, QPE/registry migration and public API compatibility review. Keep the
generic Fourier, normalization and index lemmas in this module.

Both inverse laws, without a matrix computation in the executable checker. -/
theorem check_unitary (definitions : List QleisliKernel.QftGraph.Definition)
    (entry width : Nat) (receipt : QleisliKernel.QftGraph.Receipt)
    (accepted : QleisliKernel.QftGraph.check definitions entry width = some receipt)
    (actual : QleisliKernel.QftGraph.Action)
    (meaning : QleisliKernel.QftGraph.denote definitions entry = some actual) :
    (matrix width actual)ᴴ * matrix width actual = 1 ∧
      matrix width actual * (matrix width actual)ᴴ = 1 := by
  rw [checked_matrix definitions entry width receipt accepted actual meaning]
  constructor
  · rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      fourier_isometry, Matrix.submatrix_one_equiv]
  · rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      fourier_coisometry, Matrix.submatrix_one_equiv]

end Qleisli.QftGraph
