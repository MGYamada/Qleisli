import QleisliKernel.Qft
import Qleisli.Interference
import Mathlib.Data.ZMod.Basic

/-! Fourier phase interpretation of the actual symbolic QFT certificate.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.Qft
open QleisliKernel QleisliKernel.Interference QleisliKernel.PathSum
open scoped BigOperators

def value (width : Nat) (bits : Bits) : Nat :=
  ∑ k ∈ Finset.range width, if bits k then 2 ^ k else 0

private theorem sum_range {A : Type} [AddCommMonoid A] (n : Nat) (f : Nat → A) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

private theorem high_power_zero (width k l : Nat) (bounded : width ≤ 8)
    (high : width ≤ k + l) : (2 : ZMod 256) ^ (8 - width + k + l) = 0 := by
  have exponent : 8 - width + k + l = 8 + (k + l - width) := by omega
  rw [exponent, pow_add]
  have zero : (2 : ZMod 256) ^ 8 = 0 := by decide
  rw [zero, zero_mul]

private theorem sum_flatMap {A B : Type} [AddCommMonoid B] (xs : List A) (f : A → List B) :
    (xs.flatMap f).sum = (xs.map (fun x => (f x).sum)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

private theorem phase_cast (width : Nat) (input choices : Bits) :
    (PhasePolynomial.evaluate (QleisliKernel.Qft.fourierTerms width)
      (assignment width input choices) : ZMod 256) =
      ∑ k ∈ Finset.range width, ∑ l ∈ Finset.range (width - k),
        if input k && choices l then (2 : ZMod 256) ^ (8 - width + k + l) else 0 := by
  unfold PhasePolynomial.evaluate
  rw [show modulus = 256 from rfl, ZMod.natCast_mod]
  simp only [QleisliKernel.Qft.fourierTerms, List.map_flatMap, sum_flatMap,
    List.map_map, Function.comp_def, sum_range, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l _
  have inside : k < width := Finset.mem_range.mp hk
  cases hi : input k <;> cases hc : choices l <;>
    simp [PhasePolynomial.Term.value, assignment, inside, hi, hc,
      show ¬ width + l < width by omega]

theorem fourier_phase (width : Nat) (bounded : width ≤ 8) (input choices : Bits) :
    PhasePolynomial.evaluate (QleisliKernel.Qft.fourierTerms width)
      (assignment width input choices) =
      (2 ^ (8 - width) * value width input * value width choices) % 256 := by
  have same : (PhasePolynomial.evaluate (QleisliKernel.Qft.fourierTerms width)
      (assignment width input choices) : ZMod 256) =
      (2 ^ (8 - width) * value width input * value width choices : Nat) := by
    rw [phase_cast]
    have extend (k : Nat) :
        (∑ l ∈ Finset.range (width - k),
          if input k && choices l then (2 : ZMod 256) ^ (8 - width + k + l) else 0) =
        ∑ l ∈ Finset.range width,
          if input k && choices l then (2 : ZMod 256) ^ (8 - width + k + l) else 0 := by
      apply Finset.sum_subset (Finset.range_mono (Nat.sub_le width k))
      intro l _ outside
      have high : width ≤ k + l := by simp only [Finset.mem_range, not_lt] at outside; omega
      split <;> simp [high_power_zero width k l bounded high]
    simp_rw [extend]
    simp only [value, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_sum]
    rw [mul_assoc, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    cases input k <;> cases choices l <;> simp [pow_add, mul_assoc]
  have sameMod := (ZMod.natCast_eq_natCast_iff' _ _ 256).mp same
  simpa only [PhasePolynomial.evaluate, modulus, Nat.mod_mod] using sameMod

open Qleisli.Interference

noncomputable def pathWeight (state : PathState) : ℂ :=
  complexModel.halfRoot ^ state.hadamards * complexModel.root ^ state.phase

theorem root_mod (ticks : Nat) :
    complexModel.root ^ (ticks % 256) = complexModel.root ^ ticks :=
  (pow_eq_pow_mod ticks complexModel.root_period).symm

/-- Each H contributes precisely its standard matrix entry to a fixed path. -/
theorem hadamard_path_weight (choices : Bits) (state : PathState) (axis : Nat) :
    pathWeight (step choices state (.hadamard axis)) =
      pathWeight state * (complexModel.halfRoot *
        if state.bits axis && choices state.hadamards then (-1 : ℂ) else 1) := by
  simp only [pathWeight, PathSum.step, modulus, root_mod, pow_add, pow_one]
  split <;> simp [root_half_turn] <;> ring

/-- A diagonal step multiplies by the exact literal controlled phase. -/
theorem diagonal_path_weight (choices : Bits) (state : PathState)
    (terms : PhasePolynomial.Polynomial) :
    pathWeight (step choices state (.diagonal terms)) = pathWeight state *
      complexModel.root ^ PhasePolynomial.evaluate terms state.bits := by
  simp only [pathWeight, PathSum.step, modulus, root_mod, pow_add]
  ring

theorem matched_phase (width : Nat) (gates : List QleisliKernel.Interference.Gate)
    (axes : List Nat) (accepted : QleisliKernel.Qft.matchCircuit width gates axes = true)
    (input choices : Bits) :
    (runFrom gates choices (realize width (initial width) input choices)).phase =
      (2 ^ (8 - width) * value width input * value width choices) % 256 := by
  rw [QleisliKernel.Qft.matched_paths width gates axes accepted input choices]
  simp only [realize, QleisliKernel.Qft.expected, PhasePolynomial.normalize_sound]
  exact fourier_phase width (QleisliKernel.Qft.matchCircuit_conditions width gates axes accepted).2.1
    input choices

theorem matched_weight (width : Nat) (gates : List QleisliKernel.Interference.Gate)
    (axes : List Nat) (accepted : QleisliKernel.Qft.matchCircuit width gates axes = true)
    (input choices : Bits) :
    pathWeight (runFrom gates choices (realize width (initial width) input choices)) =
      complexModel.halfRoot ^ width *
        Complex.exp (2 * Real.pi * Complex.I * value width input * value width choices /
          (2 : ℂ) ^ width) := by
  have bounded := (QleisliKernel.Qft.matchCircuit_conditions width gates axes accepted).2.1
  have count : (runFrom gates choices (realize width (initial width) input choices)).hadamards = width := by
    rw [QleisliKernel.Qft.matched_paths width gates axes accepted input choices]
    rfl
  rw [pathWeight, count, matched_phase width gates axes accepted input choices, root_mod, root_phase]
  congr 2
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have powers : (2 : ℂ) ^ (8 - width) * 2 ^ width = 256 := by
    rw [← pow_add, Nat.sub_add_cancel bounded]
    norm_num
  apply (eq_div_iff (pow_ne_zero width (by norm_num : (2 : ℂ) ≠ 0))).mpr
  calc
    (2 * Real.pi * Complex.I * (2 ^ (8 - width) * value width input * value width choices) / 256) *
        2 ^ width =
      (2 ^ (8 - width) * 2 ^ width) *
        (2 * Real.pi * Complex.I * value width input * value width choices) / 256 := by ring
    _ = _ := by rw [powers]; ring

noncomputable def gateFactor (choices : Bits) (state : PathState) :
    QleisliKernel.Interference.Gate → ℂ
  | .hadamard axis => complexModel.halfRoot *
      if state.bits axis && choices state.hadamards then -1 else 1
  | .diagonal terms => complexModel.root ^ PhasePolynomial.evaluate terms state.bits

noncomputable def pathProduct (choices : Bits) :
    List QleisliKernel.Interference.Gate → PathState → ℂ
  | [], _ => 1
  | gate :: rest, state => gateFactor choices state gate *
      pathProduct choices rest (PathSum.step choices state gate)

theorem pathProduct_weight (choices : Bits) (gates : List QleisliKernel.Interference.Gate)
    (state : PathState) :
    pathWeight (runFrom gates choices state) = pathWeight state * pathProduct choices gates state := by
  induction gates generalizing state with
  | nil => simp [runFrom, pathProduct]
  | cons gate rest ih =>
    simp only [runFrom, List.foldl_cons, pathProduct]
    rw [show rest.foldl (PathSum.step choices) (PathSum.step choices state gate) =
      runFrom rest choices (PathSum.step choices state gate) from rfl, ih]
    cases gate <;> simp only [gateFactor, hadamard_path_weight, diagonal_path_weight] <;> ring

def finiteBits {width : Nat} (bits : Fin width → Bool) : Bits :=
  fun i => if bound : i < width then bits ⟨i, bound⟩ else false

@[simp] theorem finiteBits_inside {width : Nat} (bits : Fin width → Bool) (i : Fin width) :
    finiteBits bits i = bits i := by simp [finiteBits, i.isLt]

/-- QFT-profile sum of primitive matrix-entry products, with exactly width H
outcomes. Matching establishes that this is the complete H-history space and
binds the final reversal. For other H counts this is not a general circuit
denotation. This proof-only sum is never evaluated by the matcher/compiler. -/
noncomputable def coefficient (width : Nat) (gates : List QleisliKernel.Interference.Gate)
    (input output : Fin width → Bool) : ℂ := by
  classical
  exact ∑ choices : Fin width → Bool,
    let state := realize width (initial width) (finiteBits input) (finiteBits choices)
    if (fun i : Fin width => (runFrom gates (finiteBits choices) state).bits
        (width - 1 - i)) = output then
      pathProduct (finiteBits choices) gates state else 0

theorem matched_coefficient (width : Nat) (gates : List QleisliKernel.Interference.Gate)
    (axes : List Nat) (accepted : QleisliKernel.Qft.matchCircuit width gates axes = true)
    (input output : Fin width → Bool) :
    coefficient width gates input output = complexModel.halfRoot ^ width *
      Complex.exp (2 * Real.pi * Complex.I * value width (finiteBits input) *
        value width (finiteBits output) / (2 : ℂ) ^ width) := by
  classical
  have endpoints (choices : Fin width → Bool) :
      (fun i : Fin width => (runFrom gates (finiteBits choices)
        (realize width (initial width) (finiteBits input) (finiteBits choices))).bits
        (width - 1 - i)) = choices := by
    funext i
    rw [QleisliKernel.Qft.matched_output width i i.isLt gates axes accepted]
    exact finiteBits_inside choices i
  simp only [coefficient, endpoints]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have product := pathProduct_weight (finiteBits output) gates
    (realize width (initial width) (finiteBits input) (finiteBits output))
  have initialWeight : pathWeight
      (realize width (initial width) (finiteBits input) (finiteBits output)) = 1 := by
    simp [pathWeight, realize, initial, PhasePolynomial.evaluate]
  rw [initialWeight, one_mul] at product
  rw [← product]
  exact matched_weight width gates axes accepted (finiteBits input) (finiteBits output)

theorem halfRoot_power (width : Nat) :
    complexModel.halfRoot ^ width = (Real.sqrt ((2 : ℝ) ^ width) : ℂ)⁻¹ := by
  have squareRoot : Real.sqrt ((2 : ℝ) ^ width) = (Real.sqrt 2) ^ width := by
    apply (Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)).mpr
    rw [← mul_pow, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  simp [complexModel, squareRoot]

/-- Positive Fourier coefficients for the actual matched circuit, with little-endian labels. -/
theorem matched_fourier (width : Nat) (gates : List QleisliKernel.Interference.Gate)
    (axes : List Nat) (accepted : QleisliKernel.Qft.matchCircuit width gates axes = true)
    (input output : Fin width → Bool) :
    coefficient width gates input output =
      Complex.exp (2 * Real.pi * Complex.I * value width (finiteBits input) *
        value width (finiteBits output) / (2 : ℂ) ^ width) /
      (Real.sqrt ((2 : ℝ) ^ width) : ℂ) := by
  rw [matched_coefficient width gates axes accepted input output, halfRoot_power]
  ring

/-- Arbitrary joint amplitudes, with no separability or eigenstate premise. -/
theorem matched_reference (width : Nat) (gates : List QleisliKernel.Interference.Gate)
    (axes : List Nat) (accepted : QleisliKernel.Qft.matchCircuit width gates axes = true)
    {R : Type} (joint : (Fin width → Bool) → R → ℂ) (reference : R)
    (output : Fin width → Bool) :
    (∑ input, coefficient width gates input output * joint input reference) =
      ∑ input, (Complex.exp (2 * Real.pi * Complex.I * value width (finiteBits input) *
        value width (finiteBits output) / (2 : ℂ) ^ width) /
        (Real.sqrt ((2 : ℝ) ^ width) : ℂ)) * joint input reference := by
  apply Finset.sum_congr rfl
  intro input _
  rw [matched_fourier width gates axes accepted input output]

/- Positive Fourier meaning for symbolic-path equality. No literal-template
premise is required; the phase profile remains bounded by eight qubits. -/
theorem compiled_matched_phase (width : Nat) (gates : List QleisliKernel.Interference.Gate)
    (axes : List Nat) (accepted : QleisliKernel.Qft.matchCompiledCircuit width gates axes = true)
    (input choices : Bits) :
    (runFrom gates choices (realize width (initial width) input choices)).phase =
      (2 ^ (8 - width) * value width input * value width choices) % 256 := by
  rw [QleisliKernel.Qft.compiled_matched_paths width gates axes accepted input choices]
  simp only [realize, QleisliKernel.Qft.expected, PhasePolynomial.normalize_sound]
  exact fourier_phase width (QleisliKernel.Qft.matchCompiledCircuit_conditions width gates axes accepted).2.1
    input choices

theorem compiled_matched_weight (width : Nat) (gates : List QleisliKernel.Interference.Gate)
    (axes : List Nat) (accepted : QleisliKernel.Qft.matchCompiledCircuit width gates axes = true)
    (input choices : Bits) :
    pathWeight (runFrom gates choices (realize width (initial width) input choices)) =
      complexModel.halfRoot ^ width *
        Complex.exp (2 * Real.pi * Complex.I * value width input * value width choices /
          (2 : ℂ) ^ width) := by
  have bounded := (QleisliKernel.Qft.matchCompiledCircuit_conditions width gates axes accepted).2.1
  have count : (runFrom gates choices (realize width (initial width) input choices)).hadamards = width := by
    rw [QleisliKernel.Qft.compiled_matched_paths width gates axes accepted input choices]
    rfl
  rw [pathWeight, count, compiled_matched_phase width gates axes accepted input choices, root_mod, root_phase]
  congr 2
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have powers : (2 : ℂ) ^ (8 - width) * 2 ^ width = 256 := by
    rw [← pow_add, Nat.sub_add_cancel bounded]
    norm_num
  apply (eq_div_iff (pow_ne_zero width (by norm_num : (2 : ℂ) ≠ 0))).mpr
  calc
    (2 * Real.pi * Complex.I * (2 ^ (8 - width) * value width input * value width choices) / 256) *
        2 ^ width =
      (2 ^ (8 - width) * 2 ^ width) *
        (2 * Real.pi * Complex.I * value width input * value width choices) / 256 := by ring
    _ = _ := by rw [powers]; ring

theorem compiled_matched_coefficient (width : Nat) (gates : List QleisliKernel.Interference.Gate)
    (axes : List Nat) (accepted : QleisliKernel.Qft.matchCompiledCircuit width gates axes = true)
    (input output : Fin width → Bool) :
    coefficient width gates input output = complexModel.halfRoot ^ width *
      Complex.exp (2 * Real.pi * Complex.I * value width (finiteBits input) *
        value width (finiteBits output) / (2 : ℂ) ^ width) := by
  classical
  have endpoints (choices : Fin width → Bool) :
      (fun i : Fin width => (runFrom gates (finiteBits choices)
        (realize width (initial width) (finiteBits input) (finiteBits choices))).bits
        (width - 1 - i)) = choices := by
    funext i
    rw [QleisliKernel.Qft.compiled_matched_output width i i.isLt gates axes accepted]
    exact finiteBits_inside choices i
  simp only [coefficient, endpoints]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have product := pathProduct_weight (finiteBits output) gates
    (realize width (initial width) (finiteBits input) (finiteBits output))
  have initialWeight : pathWeight
      (realize width (initial width) (finiteBits input) (finiteBits output)) = 1 := by
    simp [pathWeight, realize, initial, PhasePolynomial.evaluate]
  rw [initialWeight, one_mul] at product
  rw [← product]
  exact compiled_matched_weight width gates axes accepted (finiteBits input) (finiteBits output)

theorem compiled_matched_fourier (width : Nat) (gates : List QleisliKernel.Interference.Gate)
    (axes : List Nat) (accepted : QleisliKernel.Qft.matchCompiledCircuit width gates axes = true)
    (input output : Fin width → Bool) :
    coefficient width gates input output =
      Complex.exp (2 * Real.pi * Complex.I * value width (finiteBits input) *
        value width (finiteBits output) / (2 : ℂ) ^ width) /
      (Real.sqrt ((2 : ℝ) ^ width) : ℂ) := by
  rw [compiled_matched_coefficient width gates axes accepted input output, halfRoot_power]
  ring

theorem compiled_matched_reference (width : Nat) (gates : List QleisliKernel.Interference.Gate)
    (axes : List Nat) (accepted : QleisliKernel.Qft.matchCompiledCircuit width gates axes = true)
    {R : Type} (joint : (Fin width → Bool) → R → ℂ) (reference : R)
    (output : Fin width → Bool) :
    (∑ input, coefficient width gates input output * joint input reference) =
      ∑ input, (Complex.exp (2 * Real.pi * Complex.I * value width (finiteBits input) *
        value width (finiteBits output) / (2 : ℂ) ^ width) /
        (Real.sqrt ((2 : ℝ) ^ width) : ℂ)) * joint input reference := by
  apply Finset.sum_congr rfl
  intro input _
  rw [compiled_matched_fourier width gates axes accepted input output]

end Qleisli.Qft
