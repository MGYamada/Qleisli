import QleisliKernel.Exact
import Qleisli.Semantics.Exact
import Mathlib.Tactic
import Mathlib.NumberTheory.Real.Irrational

/-! Proofs about actual VM-23 executable definitions. Scalar arithmetic is proved
against independent complex meaning; general matrix soundness remains open.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.Exact
open QleisliKernel.Semantics.Exact
open QleisliKernel.Exact Qleisli.Semantics.Exact

theorem halve_preserves (x : Coefficient) (nonzero : x.exponent ≠ 0)
    (even : x.numerator % 2 = 0) :
    rational ⟨x.numerator / 2, x.exponent - 1⟩ = rational x := by
  have decomposition : x.numerator / 2 * 2 = x.numerator := by omega
  have cast : ((x.numerator / 2 : Int) : ℚ) * 2 = (x.numerator : ℚ) := by
    exact_mod_cast decomposition
  obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero nonzero
  simp only [rational, he, Nat.succ_sub_one, pow_succ]
  field_simp
  rw [← cast]

theorem normalize_preserves (fuel : Nat) (x : Coefficient) :
    rational (normalize fuel x) = rational x := by
  induction fuel generalizing x with
  | zero => rfl
  | succ fuel ih =>
    change rational (if x.numerator = 0 then Coefficient.integer 0 else
      if x.exponent = 0 || x.numerator % 2 ≠ 0 then x else
      normalize fuel ⟨x.numerator / 2, x.exponent - 1⟩) = rational x
    split
    · simp_all [rational, Coefficient.integer]
    · split
      · rfl
      · rename_i hn hs
        have both : x.exponent ≠ 0 ∧ x.numerator % 2 = 0 := by simpa using hs
        have he := both.1
        have hp := both.2
        rw [ih, halve_preserves x he hp]

theorem make_preserves (n : Int) (e : Nat) (x : Coefficient)
    (ok : Coefficient.make n e = .ok x) : rational x = (n : ℚ) / 2 ^ e := by
  unfold Coefficient.make at ok
  split at ok
  · cases ok
  · rename_i value checked
    have eq := checkedInt_value n value checked
    subst value
    split at ok
    · cases ok
    · dsimp only at ok
      split at ok
      · cases ok
        exact normalize_preserves 128 ⟨n, e⟩
      · cases ok

theorem canonical_coprime (x : Coefficient) (valid : Coefficient.valid x = true) :
    Nat.Coprime x.numerator.natAbs (2 ^ x.exponent) := by
  by_cases he : x.exponent = 0
  · simp [he]
  · have odd : x.numerator % 2 ≠ 0 := by
      simp only [Coefficient.valid, Bool.and_eq_true, decide_eq_true_eq] at valid
      by_cases hn : x.numerator = 0
      · simp [hn, he] at valid
      · simpa [hn, he] using valid.2
    apply Nat.Coprime.pow_right
    apply Nat.coprime_comm.mp
    apply Nat.prime_two.coprime_iff_not_dvd.mpr
    intro divisible
    exact odd (Int.emod_eq_zero_of_dvd (Int.natCast_dvd.mpr divisible))

theorem canonical_num (x : Coefficient) (valid : Coefficient.valid x = true) :
    (rational x).num = x.numerator := by
  have h := Rat.num_div_eq_of_coprime (a := x.numerator) (b := (2 : Int) ^ x.exponent)
    (by positivity) (by simpa using canonical_coprime x valid)
  simpa [rational] using h

theorem canonical_den (x : Coefficient) (valid : Coefficient.valid x = true) :
    (rational x).den = 2 ^ x.exponent := by
  have h := Rat.den_div_eq_of_coprime (a := x.numerator) (b := (2 : Int) ^ x.exponent)
    (by positivity) (by simpa using canonical_coprime x valid)
  exact_mod_cast (show ((rational x).den : Int) = 2 ^ x.exponent by simpa [rational] using h)

theorem canonical_injective (x y : Coefficient)
    (vx : Coefficient.valid x = true) (vy : Coefficient.valid y = true)
    (equal : rational x = rational y) : x = y := by
  have hn : x.numerator = y.numerator := by
    rw [← canonical_num x vx, ← canonical_num y vy, equal]
  have hp : (2 : Nat) ^ x.exponent = 2 ^ y.exponent := by
    rw [← canonical_den x vx, ← canonical_den y vy, equal]
  have he := Nat.pow_right_injective (by decide : 2 ≤ (2 : Nat)) hp
  cases x; cases y
  simp_all

theorem coefficient_equality_iff (x y : Coefficient)
    (vx : Coefficient.valid x = true) (vy : Coefficient.valid y = true) :
    (x == y) = true ↔ rational x = rational y := by
  constructor
  · intro equal
    have : x = y := by simpa using equal
    rw [this]
  · intro equal
    simp [canonical_injective x y vx vy equal]

/-- Exact structural equality preserves the full complex meaning. -/
theorem equality_preserves (x y : Scalar) (equal : (x == y) = true) :
    scalar x = scalar y := by
  have : x = y := by simpa using equal
  rw [this]

theorem irrational_pair_unique (a b c d : ℚ)
    (equal : (a : ℝ) + (b : ℝ) * Real.sqrt 2 = (c : ℝ) + (d : ℝ) * Real.sqrt 2) :
    a = c ∧ b = d := by
  by_cases h : b = d
  · subst d
    constructor
    · apply Rat.cast_injective (α := ℝ)
      linarith
    · rfl
  · have nonzero : ((b - d : ℚ) : ℝ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr h
    have impossible : Real.sqrt 2 = (((c - a) / (b - d) : ℚ) : ℝ) := by
      simp only [Rat.cast_div, Rat.cast_sub] at nonzero ⊢
      apply (eq_div_iff nonzero).mpr
      nlinarith
    exact (Irrational.ne_rat irrational_sqrt_two _ impossible).elim

theorem scalar_equality_iff (x y : Scalar)
    (vx : Scalar.valid x = true) (vy : Scalar.valid y = true) :
    (x == y) = true ↔ scalar x = scalar y := by
  constructor
  · exact equality_preserves x y
  · intro equal
    have real : (rational x.a : ℝ) + (rational x.b : ℝ) * Real.sqrt 2 =
        (rational y.a : ℝ) + (rational y.b : ℝ) * Real.sqrt 2 := by
      simpa [scalar] using congrArg Complex.re equal
    have imaginary : (rational x.c : ℝ) + (rational x.d : ℝ) * Real.sqrt 2 =
        (rational y.c : ℝ) + (rational y.d : ℝ) * Real.sqrt 2 := by
      simpa [scalar] using congrArg Complex.im equal
    obtain ⟨ha, hb⟩ := irrational_pair_unique _ _ _ _ real
    obtain ⟨hc, hd⟩ := irrational_pair_unique _ _ _ _ imaginary
    simp only [Scalar.valid, Bool.and_eq_true] at vx vy
    have ea := canonical_injective x.a y.a vx.1.1.1 vy.1.1.1 ha
    have eb := canonical_injective x.b y.b vx.1.1.2 vy.1.1.2 hb
    have ec := canonical_injective x.c y.c vx.1.2 vy.1.2 hc
    have ed := canonical_injective x.d y.d vx.2 vy.2 hd
    have : x = y := by cases x; cases y; simp_all
    simp [this]

theorem coefficient_neg_preserves (x z : Coefficient)
    (ok : Coefficient.neg x = .ok z) : rational z = -rational x := by
  simp only [Coefficient.neg, bind, Except.bind] at ok
  split at ok
  · cases ok
  · rename_i n checked
    have eq := checkedInt_value (-x.numerator) n checked
    simp only [pure, Except.pure, Except.ok.injEq] at ok
    subst z
    simp [rational, eq, neg_div]

theorem coefficient_mul_preserves (x y z : Coefficient)
    (ok : Coefficient.mul x y = .ok z) : rational z = rational x * rational y := by
  simp only [Coefficient.mul, bind, Except.bind] at ok
  split at ok
  · cases ok
  · rename_i n checked
    have eq := checkedInt_value (x.numerator * y.numerator) n checked
    rw [make_preserves n (x.exponent + y.exponent) z ok, eq]
    simp only [rational, Int.cast_mul, pow_add]
    ring

theorem checked_bind {α : Type} (n : Int) (next : Int → Except Error α) (z : α)
    (ok : (checkedInt n >>= next) = .ok z) : next n = .ok z := by
  simp only [bind, Except.bind] at ok
  split at ok
  · cases ok
  · rename_i value checked
    have eq := checkedInt_value n value checked
    simpa [eq] using ok

theorem align_preserves (n : Int) (e target : Nat) (le : e ≤ target) :
    (n : ℚ) * 2 ^ (target - e) / 2 ^ target = (n : ℚ) / 2 ^ e := by
  have power : (2 : ℚ) ^ target = 2 ^ (target - e) * 2 ^ e := by
    rw [← pow_add, Nat.sub_add_cancel le]
  rw [power]
  field_simp

theorem coefficient_add_preserves (x y z : Coefficient)
    (ok : Coefficient.add x y = .ok z) : rational z = rational x + rational y := by
  by_cases hx : x.numerator = 0
  · simp [Coefficient.add, hx, pure, Except.pure] at ok
    subst z
    simp [rational, hx]
  · by_cases hy : y.numerator = 0
    · simp [Coefficient.add, hx, hy, pure, Except.pure, bind, Except.bind] at ok
      subst z
      simp [rational, hy]
    · simp [Coefficient.add, hx, hy] at ok
      have h1 := checked_bind _ _ z ok
      have h2 := checked_bind _ _ z h1
      have h3 := checked_bind _ _ z h2
      have h4 := checked_bind _ _ z h3
      have h5 := checked_bind _ _ z h4
      rw [make_preserves _ _ z h5]
      simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, add_div]
      rw [align_preserves _ _ _ (Nat.le_max_left _ _),
          align_preserves _ _ _ (Nat.le_max_right _ _)]
      rfl

theorem scalar_add_preserves (x y z : Scalar) (ok : Scalar.add x y = .ok z) :
    scalar z = scalar x + scalar y := by
  obtain ⟨a, ha, h⟩ := bind_success _ _ z ok
  obtain ⟨b, hb, h⟩ := bind_success _ _ z h
  obtain ⟨c, hc, h⟩ := bind_success _ _ z h
  obtain ⟨d, hd, h⟩ := bind_success _ _ z h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst z
  simp only [scalar, coefficient_add_preserves _ _ _ ha,
    coefficient_add_preserves _ _ _ hb, coefficient_add_preserves _ _ _ hc,
    coefficient_add_preserves _ _ _ hd, Rat.cast_add]
  ring

theorem scalar_neg_preserves (x z : Scalar) (ok : Scalar.neg x = .ok z) :
    scalar z = -scalar x := by
  obtain ⟨a, ha, h⟩ := bind_success _ _ z ok
  obtain ⟨b, hb, h⟩ := bind_success _ _ z h
  obtain ⟨c, hc, h⟩ := bind_success _ _ z h
  obtain ⟨d, hd, h⟩ := bind_success _ _ z h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst z
  simp only [scalar, coefficient_neg_preserves _ _ ha,
    coefficient_neg_preserves _ _ hb, coefficient_neg_preserves _ _ hc,
    coefficient_neg_preserves _ _ hd, Rat.cast_neg]
  ring

theorem scalar_conjugate_preserves (x z : Scalar) (ok : Scalar.conjugate x = .ok z) :
    scalar z = star (scalar x) := by
  obtain ⟨c, hc, h⟩ := bind_success _ _ z ok
  obtain ⟨d, hd, h⟩ := bind_success _ _ z h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst z
  simp [scalar, coefficient_neg_preserves _ _ hc,
    coefficient_neg_preserves _ _ hd]
  ring


theorem scalar_set_meaning (x : Scalar) (i : Nat) (v : Coefficient) (bound : i < 4) :
    scalar (x.set i v) = scalar x +
      ((rational v - rational (x.get i) : ℚ) : ℂ) * basisWeight i := by
  interval_cases i <;> simp [Scalar.set, Scalar.get, scalar, basisWeight] <;> ring

theorem basis_product (i j : Nat) (hi : i < 4) (hj : j < 4) :
    basisWeight i * basisWeight j =
      (if i % 2 = 1 && j % 2 = 1 then (2 : ℂ) else 1) *
      (if i / 2 = 1 && j / 2 = 1 then (-1 : ℂ) else 1) * basisWeight (Nat.xor i j) := by
  have hs : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    norm_cast
    exact Real.mul_self_sqrt (by norm_num)
  interval_cases i <;> interval_cases j <;>
    norm_num [basisWeight, Nat.xor, Complex.I_mul_I] <;>
    ring_nf <;> simp [hs, pow_two, Complex.I_mul_I]; ring

theorem multiplyTerm_preserves (x y acc z : Scalar) (i j : Nat) (hi : i < 4) (hj : j < 4)
    (ok : multiplyTerm x y acc (i,j) = .ok z) :
    scalar z = scalar acc +
      (rational (x.get i) : ℂ) * basisWeight i *
      (rational (y.get j) : ℂ) * basisWeight j := by
  have hk : Nat.xor i j < 4 := by interval_cases i <;> interval_cases j <;> decide
  simp only [multiplyTerm, bind, Except.bind, pure, Except.pure] at ok
  split at ok
  · cases ok
  · rename_i product hp
    have vp := coefficient_mul_preserves _ _ _ hp
    have finish (signed : Coefficient)
        (h : (do let value ← Coefficient.add (acc.get (Nat.xor i j)) signed
                 pure (acc.set (Nat.xor i j) value)) = .ok z) :
        scalar z = scalar acc + (rational signed : ℂ) * basisWeight (Nat.xor i j) := by
      obtain ⟨value, hv, h⟩ := bind_success _ _ z h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst z
      rw [scalar_set_meaning acc _ _ hk, coefficient_add_preserves _ _ _ hv]
      simp
    have sign (scaled : Coefficient)
        (h : (if i / 2 = 1 && j / 2 = 1 then
                (do let signed ← Coefficient.neg scaled
                    let value ← Coefficient.add (acc.get (Nat.xor i j)) signed
                    pure (acc.set (Nat.xor i j) value))
              else (do let value ← Coefficient.add (acc.get (Nat.xor i j)) scaled
                       pure (acc.set (Nat.xor i j) value))) = .ok z) :
        scalar z = scalar acc + (rational scaled : ℂ) *
          (if i / 2 = 1 && j / 2 = 1 then (-1 : ℂ) else 1) * basisWeight (Nat.xor i j) := by
      split at h
      · rename_i cond
        obtain ⟨signed, hn, h⟩ := bind_success _ _ z h
        rw [finish signed h, coefficient_neg_preserves _ _ hn]
        simp [cond]
      · rename_i cond
        rw [finish scaled h]
        simp [cond]
    have scaled_result : scalar z = scalar acc + (rational product : ℂ) *
        (if i % 2 = 1 && j % 2 = 1 then (2 : ℂ) else 1) *
        (if i / 2 = 1 && j / 2 = 1 then (-1 : ℂ) else 1) * basisWeight (Nat.xor i j) := by
      split at ok
      · rename_i cond
        obtain ⟨scaled, hs, h⟩ := bind_success _ _ z ok
        rw [sign scaled h, coefficient_mul_preserves _ _ _ hs]
        simp [cond, rational, Coefficient.integer]
      · rename_i cond
        rw [sign product ok]
        simp [cond]
    rw [scaled_result, vp, Rat.cast_mul]
    calc
      _ = scalar acc + (rational (x.get i) : ℂ) * (rational (y.get j) : ℂ) *
          (basisWeight i * basisWeight j) := by rw [basis_product i j hi hj]; ring
      _ = _ := by ring

theorem scalar_mul_preserves (x y z : Scalar) (ok : Scalar.mul x y = .ok z) :
    scalar z = scalar x * scalar y := by
  let contribution := fun (ij : Nat × Nat) =>
    (rational (x.get ij.1) : ℂ) * basisWeight ij.1 *
    (rational (y.get ij.2) : ℂ) * basisWeight ij.2
  have fold_meaning (xs : List (Nat × Nat)) (initial result : Scalar)
      (bounds : ∀ ij ∈ xs, ij.1 < 4 ∧ ij.2 < 4)
      (success : xs.foldlM (multiplyTerm x y) initial = .ok result) :
      scalar result = scalar initial + (xs.map contribution).sum := by
    induction xs generalizing initial with
    | nil =>
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at success
      subst result
      simp
    | cons ij xs ih =>
      simp only [List.foldlM_cons] at success
      obtain ⟨next, hn, h⟩ := bind_success _ _ result success
      have b := bounds ij (by simp)
      have head := multiplyTerm_preserves x y initial next ij.1 ij.2 b.1 b.2 hn
      rw [ih next (fun p hp => bounds p (by simp [hp])) h, head]
      simp only [List.map_cons, List.sum_cons, contribution]
      ring
  have full := fold_meaning coefficientPairs Scalar.zero z
    (by simp [coefficientPairs]; intro a b i hi j hj ha hb; subst a; subst b; exact ⟨hi,hj⟩) ok
  rw [full]
  simp [coefficientPairs, List.range_succ, contribution, basisWeight, Scalar.get,
    scalar, Scalar.zero, rational, Coefficient.integer]
  ring

def halfRoot : Coefficient := ⟨1, 1⟩
def negativeHalfRoot : Coefficient := ⟨-1, 1⟩
def hadamard : Matrix := ⟨2, 2,
  [⟨.integer 0, halfRoot, .integer 0, .integer 0⟩,
   ⟨.integer 0, halfRoot, .integer 0, .integer 0⟩,
   ⟨.integer 0, halfRoot, .integer 0, .integer 0⟩,
   ⟨.integer 0, negativeHalfRoot, .integer 0, .integer 0⟩]⟩
def tGate : Matrix := ⟨2, 2, [Scalar.one, Scalar.zero, Scalar.zero, Scalar.phase 1]⟩
def ht : Matrix := ⟨2, 2,
  [⟨.integer 0, halfRoot, .integer 0, .integer 0⟩,
   ⟨.integer 0, halfRoot, .integer 0, .integer 0⟩,
   ⟨halfRoot, .integer 0, halfRoot, .integer 0⟩,
   ⟨negativeHalfRoot, .integer 0, negativeHalfRoot, .integer 0⟩]⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem ht_computed : Matrix.compose tGate hadamard 16 = (.ok ht, 0) := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem ht_isometry : Matrix.isometry ht 20 = (.ok true, 0) := by decide

theorem ht_full_amplitudes {R : Type} (joint : Nat → R → ℂ) (reference : R) :
    action ht joint 0 reference = (Real.sqrt 2 : ℂ) / 2 *
      (joint 0 reference + joint 1 reference) ∧
    action ht joint 1 reference = (1 + Complex.I) / 2 *
      (joint 0 reference - joint 1 reference) := by
  simp [action, entry, ht, Matrix.entry, scalar, rational, halfRoot,
    negativeHalfRoot, Coefficient.integer, List.range_succ]
  constructor <;> ring

theorem ht_norm_preserves {R : Type} (joint : Nat → R → ℂ) (reference : R) :
    Complex.normSq (action ht joint 0 reference) +
      Complex.normSq (action ht joint 1 reference) =
    Complex.normSq (joint 0 reference) + Complex.normSq (joint 1 reference) := by
  obtain ⟨row0, row1⟩ := ht_full_amplitudes joint reference
  rw [row0, row1, Complex.normSq_mul, Complex.normSq_mul]
  have h : Complex.normSq ((Real.sqrt 2 : ℂ) / 2) = (1 : ℝ) / 2 := by
    simp only [Complex.normSq_div, Complex.normSq_ofReal]
    rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have t : Complex.normSq ((1 + Complex.I) / 2) = (1 : ℝ) / 2 := by
    norm_num [Complex.normSq, Complex.add_re, Complex.add_im, Complex.div_re, Complex.div_im]
  rw [h, t, Complex.normSq_add, Complex.normSq_sub]
  ring

theorem unit_scalar_phase_retained : scalar (Scalar.phase 4) = -1 := by
  norm_num [Scalar.phase, scalar, rational, Coefficient.integer]

end Qleisli.Exact
