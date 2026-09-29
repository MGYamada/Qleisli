import QleisliKernel.Interference
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.Ring.GrindInstances
import Mathlib.Tactic

/-! Complex interpretation of the actual Mathlib-free interference definitions.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.Interference
open QleisliKernel.Interference

noncomputable def complexModel : Model ℂ where
  halfRoot := (Real.sqrt 2 : ℂ)⁻¹
  root := Complex.exp (2 * Real.pi * Complex.I / 256)
  halfRoot_square := by
    have square : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
      exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have nonzero : (Real.sqrt 2 : ℂ) ≠ 0 := by
      intro zero
      rw [zero] at square
      norm_num at square
    calc
      2 * (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ =
          ((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)) *
            ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹) := by rw [square]; ring
      _ = 1 := by field_simp
  root_period := by
    rw [← Complex.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    have angle : (256 : ℂ) * (2 * Real.pi * Complex.I / 256) = 2 * Real.pi * Complex.I := by ring
    rw [angle]
    exact Complex.exp_two_pi_mul_I

theorem root_phase (ticks : Nat) :
    complexModel.root ^ ticks =
      Complex.exp (2 * Real.pi * Complex.I * ticks / 256) := by
  change (Complex.exp (2 * Real.pi * Complex.I / 256)) ^ ticks = _
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

theorem root_half_turn : complexModel.root ^ 128 = -1 := by
  rw [root_phase]
  norm_num only [Nat.cast_ofNat]
  have angle : 2 * (Real.pi : ℂ) * Complex.I * 128 / 256 = Real.pi * Complex.I := by ring
  rw [angle, Complex.exp_pi_mul_I]

theorem hadamard_squared (axis : Nat) (amplitude : Bits → ℂ) :
    hadamard complexModel.halfRoot axis (hadamard complexModel.halfRoot axis amplitude) =
      amplitude := hadamard_involution complexModel axis amplitude

/-- The actual two amplitudes mixed by H preserve their total probability. -/
theorem hadamard_pair_norm (a b : ℂ) :
    Complex.normSq (complexModel.halfRoot * (a + b)) +
      Complex.normSq (complexModel.halfRoot * (a - b)) =
      Complex.normSq a + Complex.normSq b := by
  have coefficient : Complex.normSq complexModel.halfRoot = (2 : ℝ)⁻¹ := by
    simp only [complexModel, Complex.normSq_inv, Complex.normSq_ofReal]
    rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [Complex.normSq_mul, Complex.normSq_mul, coefficient,
    Complex.normSq_add, Complex.normSq_sub]
  ring

theorem diagonal_point_norm (terms : QleisliKernel.PhasePolynomial.Polynomial)
    (amplitude : Bits → ℂ) (bits : Bits) :
    Complex.normSq (diagonal complexModel terms amplitude bits) =
      Complex.normSq (amplitude bits) := by
  unfold diagonal
  rw [root_phase, Complex.normSq_mul]
  have phaseNorm (t : Nat) :
      Complex.normSq (Complex.exp (2 * Real.pi * Complex.I * t / 256)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]
    simp
  rw [phaseNorm, one_mul]

theorem normalized_word (gates : List Gate) (amplitude : Bits → ℂ) :
    run complexModel (normalize gates) amplitude = run complexModel gates amplitude :=
  normalize_sound complexModel gates amplitude

theorem normalized_joint_amplitudes (gates : List Gate) {R : Type}
    (joint : Bits → R → ℂ) (reference : R) :
    run complexModel (normalize gates) (fun bits => joint bits reference) =
      run complexModel gates (fun bits => joint bits reference) :=
  normalize_reference complexModel gates joint reference

theorem checked_phase_layout (definitions : List QleisliKernel.PhaseLayout.Definition)
    (entry : Nat) (required : QleisliKernel.PhaseLayout.Summary)
    (stats : QleisliKernel.PhaseLayout.Stats)
    (accepted : QleisliKernel.PhaseLayout.check definitions entry required = .ok stats)
    (actual : QleisliKernel.PhaseLayout.Action)
    (meaning : QleisliKernel.PhaseLayout.denote definitions entry = some actual) :
    liftAction complexModel actual = liftAction complexModel required.action :=
  QleisliKernel.Interference.checked_phase_layout complexModel definitions entry required stats
    accepted actual meaning

end Qleisli.Interference
