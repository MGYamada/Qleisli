import QleisliKernel.Exact

/-! Admission and machine-capacity facts for the actual VM-23 definitions.
These theorems delimit the common Rust/Lean input domain; they do not prove a
Rust compiler, native runtime or serialization adapter correct.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

namespace QleisliKernel.Exact
open Semantics.Exact

theorem checkedInt_admission (n : Int) :
    checkedInt n = .ok n ↔ minNumerator ≤ n ∧ n ≤ maxNumerator := by
  simp [checkedInt, numeratorValid]

theorem coefficient_valid_bounds (x : Coefficient) (valid : Coefficient.valid x = true) :
    minNumerator ≤ x.numerator ∧ x.numerator ≤ maxNumerator ∧
      x.exponent ≤ maxExponent := by
  simp only [Coefficient.valid, Bool.and_eq_true, numeratorValid,
    decide_eq_true_eq] at valid
  exact ⟨valid.1.1.1, valid.1.1.2, valid.1.2⟩

/-- A nonzero numerator with fewer than `fuel` magnitude bits cannot exhaust
the structural normalizer while another exact halving remains. -/
theorem normalize_nonzero_stops (fuel : Nat) (x : Coefficient)
    (nonzero : x.numerator ≠ 0)
    (lower : -((2 : Int) ^ fuel) < x.numerator)
    (upper : x.numerator < (2 : Int) ^ fuel) :
    (normalize fuel x).numerator ≠ 0 ∧
      ((normalize fuel x).exponent = 0 ∨ (normalize fuel x).numerator % 2 ≠ 0) := by
  induction fuel generalizing x with
  | zero => simp only [Int.pow_zero] at lower upper; omega
  | succ fuel ih =>
    by_cases stopped : x.exponent = 0 ∨ x.numerator % 2 ≠ 0
    · simp [normalize, nonzero, stopped]
    · have even : x.numerator % 2 = 0 := by omega
      have positive : 0 < (2 : Int) ^ fuel := Int.pow_pos (by decide)
      have nextLower : -((2 : Int) ^ fuel) < x.numerator / 2 := by
        rw [Int.pow_succ] at lower
        omega
      have nextUpper : x.numerator / 2 < (2 : Int) ^ fuel := by
        rw [Int.pow_succ] at upper
        omega
      have nextNonzero : x.numerator / 2 ≠ 0 := by omega
      have next := ih ⟨x.numerator / 2, x.exponent - 1⟩ nextNonzero nextLower nextUpper
      simpa [normalize, nonzero, stopped] using next

/-- The 128-step executable fuel covers every signed i128 input, independently
of the untrusted denominator exponent. Zero takes the explicit first branch. -/
theorem normalize_i128_stops (n : Int) (e : Nat) (valid : numeratorValid n = true) :
    let x := normalize 128 ⟨n, e⟩
    (x.numerator = 0 ∧ x.exponent = 0) ∨
      (x.numerator ≠ 0 ∧ (x.exponent = 0 ∨ x.numerator % 2 ≠ 0)) := by
  by_cases zero : n = 0
  · have result : normalize 128 ⟨n, e⟩ = Coefficient.integer 0 := by
      subst n
      rfl
    simp [result, Coefficient.integer]
  · have bounds := valid
    simp only [numeratorValid, Bool.and_eq_true, decide_eq_true_eq] at bounds
    have lower : -((2 : Int) ^ 128) < n := by
      have numeric : -((2 : Int) ^ 128) < minNumerator := by decide
      exact Int.lt_of_lt_of_le numeric bounds.1
    have upper : n < (2 : Int) ^ 128 := by
      have numeric : maxNumerator < (2 : Int) ^ 128 := by decide
      exact Int.lt_of_le_of_lt bounds.2 numeric
    exact Or.inr (normalize_nonzero_stops 128 ⟨n, e⟩ zero lower upper)

theorem normalize_numerator_valid (fuel : Nat) (x : Coefficient)
    (valid : numeratorValid x.numerator = true) :
    numeratorValid (normalize fuel x).numerator = true := by
  induction fuel generalizing x with
  | zero => exact valid
  | succ fuel ih =>
    by_cases zero : x.numerator = 0
    · simpa [normalize, zero, Coefficient.integer] using
        (show numeratorValid 0 = true by decide)
    · by_cases stopped : x.exponent = 0 ∨ x.numerator % 2 ≠ 0
      · simpa [normalize, zero, stopped] using valid
      · have nextValid : numeratorValid (x.numerator / 2) = true := by
          simp only [numeratorValid, Bool.and_eq_true, decide_eq_true_eq] at valid ⊢
          have lower : minNumerator ≤ 0 := by decide
          have upper : 0 ≤ maxNumerator := by decide
          constructor <;> omega
        simpa [normalize, zero, stopped] using
          ih ⟨x.numerator / 2, x.exponent - 1⟩ nextValid

/-- For signed i128 inputs the post-normalization exponent is the only
remaining canonical-capacity test; fuel exhaustion cannot cause rejection. -/
theorem normalized_capacity_iff (n : Int) (e : Nat) (valid : numeratorValid n = true) :
    Coefficient.valid (normalize 128 ⟨n, e⟩) = true ↔
      (normalize 128 ⟨n, e⟩).exponent ≤ maxExponent := by
  have numerator := normalize_numerator_valid 128 ⟨n, e⟩ valid
  have stopped := normalize_i128_stops n e valid
  rcases stopped with zero | nonzero
  · have zeroValid : numeratorValid 0 = true := by decide
    simp [Coefficient.valid, zero.1, zero.2, zeroValid]
  · simp [Coefficient.valid, numerator, nonzero.1, Bool.or_eq_true, nonzero.2]

theorem normalize_canonical (fuel : Nat) (x : Coefficient)
    (valid : Coefficient.valid x = true) : normalize fuel x = x := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    by_cases zero : x.numerator = 0
    · have exponent : x.exponent = 0 := by
        have facts := valid
        simp only [Coefficient.valid, zero, ↓reduceIte, Bool.and_eq_true,
          decide_eq_true_eq] at facts
        exact facts.2
      cases x
      simp_all [normalize, Coefficient.integer]
    · have stop : x.exponent = 0 ∨ x.numerator % 2 ≠ 0 := by
        have facts := valid
        simp only [Coefficient.valid, zero, ↓reduceIte, Bool.and_eq_true,
          Bool.or_eq_true, decide_eq_true_eq] at facts
        exact facts.2
      simp only [normalize, zero, ↓reduceIte]
      simp_all

/-- Canonical coefficients are representable without changing their spelling. -/
theorem make_canonical (x : Coefficient) (valid : Coefficient.valid x = true) :
    Coefficient.make x.numerator x.exponent = .ok x := by
  have bounds := coefficient_valid_bounds x valid
  have input : x.exponent ≤ maxInputExponent := by
    have bound : maxExponent ≤ maxInputExponent := by decide
    exact Nat.le_trans bounds.2.2 bound
  have numerator : checkedInt x.numerator = .ok x.numerator :=
    (checkedInt_admission x.numerator).mpr ⟨bounds.1, bounds.2.1⟩
  simp [Coefficient.make, numerator, Nat.not_lt.mpr input,
    normalize_canonical 128 x valid, valid]

/-- Construction checks original numerator and input exponent before normalization. -/
theorem make_admission (n : Int) (e : Nat) :
    Coefficient.make n e = .ok (normalize 128 ⟨n, e⟩) ↔
      numeratorValid n = true ∧ e ≤ maxInputExponent ∧
        Coefficient.valid (normalize 128 ⟨n, e⟩) = true := by
  by_cases numerator : numeratorValid n = true
  · by_cases exponent : e ≤ maxInputExponent
    · simp [Coefficient.make, checkedInt, numerator, exponent, Nat.not_lt.mpr exponent]
    · simp [Coefficient.make, checkedInt, numerator, Nat.lt_of_not_ge exponent,
        exponent]
  · have invalid : numeratorValid n = false := Bool.eq_false_iff.mpr numerator
    simp [Coefficient.make, checkedInt, invalid]

theorem make_i128_admission (n : Int) (e : Nat) (valid : numeratorValid n = true) :
    Coefficient.make n e = .ok (normalize 128 ⟨n, e⟩) ↔
      e ≤ maxInputExponent ∧ (normalize 128 ⟨n, e⟩).exponent ≤ maxExponent := by
  rw [make_admission, normalized_capacity_iff n e valid]
  simp [valid]

/-- Canonical exponent addition never exhausts Rust's u32 exponent type. -/
theorem coefficient_product_exponent_bound (x y : Coefficient)
    (vx : Coefficient.valid x = true) (vy : Coefficient.valid y = true) :
    x.exponent + y.exponent ≤ 252 ∧ x.exponent + y.exponent ≤ maxInputExponent := by
  have hx := coefficient_valid_bounds x vx
  have hy := coefficient_valid_bounds y vy
  have bound : 252 ≤ maxInputExponent := by decide
  simp only [maxExponent] at hx hy
  constructor <;> omega

theorem checked_power_success (shift : Nat) (bound : shift ≤ 126) :
    checkedInt ((2 : Int) ^ shift) = .ok ((2 : Int) ^ shift) := by
  apply (checkedInt_admission _).mpr
  have positive : 0 < (2 : Int) ^ shift := Int.pow_pos (by decide)
  have lower : minNumerator ≤ 0 := by decide
  have upper : (2 : Int) ^ shift < (2 : Int) ^ 127 :=
    Int.pow_lt_pow_of_lt (by decide) (by omega)
  constructor
  · omega
  · simp only [maxNumerator]
    omega

/-- A positive alignment factor of 2^127 must reject, even though -2^127 fits. -/
theorem checked_power_failure (shift : Nat) (bound : 127 ≤ shift) :
    checkedInt ((2 : Int) ^ shift) = .error .arithmeticCapacity := by
  have lower : (2 : Int) ^ 127 ≤ (2 : Int) ^ shift := by
    by_cases same : shift = 127
    · simp [same]
    · exact Int.le_of_lt (Int.pow_lt_pow_of_lt (by decide) (by omega))
  have invalid : numeratorValid ((2 : Int) ^ shift) = false := by
    apply Bool.eq_false_iff.mpr
    intro possible
    have bounds : minNumerator ≤ (2 : Int) ^ shift ∧
        (2 : Int) ^ shift ≤ maxNumerator := by
      simpa [numeratorValid] using possible
    simp only [maxNumerator] at bounds
    omega
  simp [checkedInt, invalid]

theorem matrix_admission (rows cols : Nat) (entries : List Scalar) :
    Matrix.make rows cols entries = .ok ⟨rows, cols, entries⟩ ↔
      1 ≤ rows ∧ rows ≤ maxDimension ∧ 1 ≤ cols ∧ cols ≤ maxDimension ∧
        entries.length = rows * cols := by
  have admission : Matrix.make rows cols entries = .ok ⟨rows, cols, entries⟩ ↔
      matrixValid rows cols = true ∧ entries.length = rows * cols := by
    by_cases valid : matrixValid rows cols = true
    · simp [Matrix.make, valid]
    · have invalid : matrixValid rows cols = false := Bool.eq_false_iff.mpr valid
      simp [Matrix.make, invalid]
  simpa [matrixValid, Bool.and_eq_true, and_assoc] using admission

theorem matrix_valid_bounds (rows cols : Nat) (valid : matrixValid rows cols = true) :
    1 ≤ rows ∧ rows ≤ 64 ∧ 1 ≤ cols ∧ cols ≤ 64 := by
  simpa [matrixValid, maxDimension, Bool.and_eq_true, and_assoc] using valid

/-- Every admitted matrix fits even the 32-bit Rust usize target's cell count. -/
theorem matrix_cells_bound (rows cols : Nat) (valid : matrixValid rows cols = true) :
    rows * cols ≤ 4096 := by
  have bounds := matrix_valid_bounds rows cols valid
  exact Nat.mul_le_mul bounds.2.1 bounds.2.2.2

/-- Tensor dimension products fit usize before the output-dimension guard,
including products rejected because they exceed the 64-dimensional profile. -/
theorem tensor_dimensions_bound (x y : Matrix)
    (vx : matrixValid x.rows x.cols = true) (vy : matrixValid y.rows y.cols = true) :
    x.rows * y.rows ≤ 4096 ∧ x.cols * y.cols ≤ 4096 := by
  have hx := matrix_valid_bounds x.rows x.cols vx
  have hy := matrix_valid_bounds y.rows y.cols vy
  exact ⟨Nat.mul_le_mul hx.2.1 hy.2.1,
    Nat.mul_le_mul hx.2.2.2 hy.2.2.2⟩

theorem matrix_row_major_bound (rows cols row col : Nat)
    (valid : matrixValid rows cols = true) (hr : row < rows) (hc : col < cols) :
    row * cols + col < rows * cols ∧ row * cols + col < 4096 := by
  have next := Nat.mul_le_mul_right cols (show row + 1 ≤ rows by omega)
  rw [Nat.add_mul, Nat.one_mul] at next
  have capacity := matrix_cells_bound rows cols valid
  constructor <;> omega

theorem compose_cost_bound (x y : Matrix)
    (vx : matrixValid x.rows x.cols = true) (vy : matrixValid y.rows y.cols = true) :
    2 * x.rows * x.cols * y.cols ≤ 524288 := by
  have hx := matrix_valid_bounds x.rows x.cols vx
  have hy := matrix_valid_bounds y.rows y.cols vy
  exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hx.2.1) hx.2.2.2)
    hy.2.2.2

theorem tensor_cost_bound (x y : Matrix)
    (output : matrixValid (x.rows * y.rows) (x.cols * y.cols) = true) :
    x.rows * y.rows * (x.cols * y.cols) ≤ 4096 :=
  matrix_cells_bound _ _ output

/-- Adjoint plus Gram composition cannot overflow a 32-bit work-cost expression. -/
theorem isometry_cost_bound (x : Matrix) (valid : matrixValid x.rows x.cols = true) :
    x.rows * x.cols + 2 * x.cols * x.rows * x.cols ≤ 528384 := by
  have bounds := matrix_valid_bounds x.rows x.cols valid
  have gram : 2 * x.cols * x.rows * x.cols ≤ 524288 :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 2 bounds.2.2.2) bounds.2.1)
      bounds.2.2.2
  exact Nat.add_le_add (matrix_cells_bound _ _ valid) gram

theorem matrix_cost_fits_usize32 : 528384 ≤ 2 ^ 32 - 1 := by decide

end QleisliKernel.Exact
