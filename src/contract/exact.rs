//! Bounded, exact arithmetic for finite semantic certificates.
//!
//! Scalars are represented canonically in `Z[1/2, sqrt(2), i]`, which equals
//! `Z[zeta_8, 1/2]`. No floating-point tolerance or equality modulo phase is
//! used. Capacity exhaustion rejects a computation; it never approximates it.

use std::error::Error;
use std::fmt;

/// Maximum row or column dimension admitted by the exact matrix kernel.
pub const MAX_MATRIX_DIMENSION: usize = 64;
/// Maximum denominator exponent of a nonzero canonical dyadic coefficient.
pub const MAX_DENOMINATOR_BITS: u32 = 126;

/// A malformed matrix, incompatible operation, or exhausted exact capacity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExactError {
    ArithmeticCapacity,
    WorkLimit,
    Dimension { rows: usize, cols: usize },
    EntryCount { expected: usize, actual: usize },
    ShapeMismatch,
}

impl fmt::Display for ExactError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ArithmeticCapacity => write!(f, "exact arithmetic capacity exhausted"),
            Self::WorkLimit => write!(f, "exact matrix work budget exhausted"),
            Self::Dimension { rows, cols } => write!(
                f,
                "matrix dimensions {rows} by {cols} must each be in 1..={MAX_MATRIX_DIMENSION}"
            ),
            Self::EntryCount { expected, actual } => {
                write!(f, "matrix requires {expected} entries, received {actual}")
            }
            Self::ShapeMismatch => write!(f, "incompatible matrix dimensions"),
        }
    }
}

impl Error for ExactError {}

/// A shared budget for exact scalar operations across an entire derivation.
///
/// Matrix operations charge their full conservative cost before doing work.
/// A failed arithmetic operation does not refund this charge.
#[derive(Clone, Debug)]
pub struct Budget {
    remaining: usize,
}

impl Budget {
    pub fn new(limit: usize) -> Self {
        Self { remaining: limit }
    }

    pub fn charge(&mut self, amount: usize) -> Result<(), ExactError> {
        self.remaining = self
            .remaining
            .checked_sub(amount)
            .ok_or(ExactError::WorkLimit)?;
        Ok(())
    }

    pub fn remaining(&self) -> usize {
        self.remaining
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct Dyadic {
    numerator: i128,
    denominator_bits: u32,
}

impl Dyadic {
    const fn integer(numerator: i128) -> Self {
        Self {
            numerator,
            denominator_bits: 0,
        }
    }

    fn new(mut numerator: i128, mut denominator_bits: u32) -> Result<Self, ExactError> {
        if numerator == 0 {
            return Ok(Self::integer(0));
        }
        // At most 127 iterations, even if an untrusted exponent is enormous.
        while denominator_bits != 0 && numerator % 2 == 0 {
            numerator /= 2;
            denominator_bits -= 1;
        }
        if denominator_bits > MAX_DENOMINATOR_BITS {
            return Err(ExactError::ArithmeticCapacity);
        }
        Ok(Self {
            numerator,
            denominator_bits,
        })
    }

    fn add(self, rhs: Self) -> Result<Self, ExactError> {
        if self.numerator == 0 {
            return Ok(rhs);
        }
        if rhs.numerator == 0 {
            return Ok(self);
        }
        let denominator_bits = self.denominator_bits.max(rhs.denominator_bits);
        let scale = |value: Self| {
            let shift = denominator_bits - value.denominator_bits;
            // Reject an unrepresentable positive power, including 2^127;
            // checked_shl only checks the shift count and can change the sign.
            let factor = 2_i128
                .checked_pow(shift)
                .ok_or(ExactError::ArithmeticCapacity)?;
            value
                .numerator
                .checked_mul(factor)
                .ok_or(ExactError::ArithmeticCapacity)
        };
        let numerator = scale(self)?
            .checked_add(scale(rhs)?)
            .ok_or(ExactError::ArithmeticCapacity)?;
        Self::new(numerator, denominator_bits)
    }

    fn mul(self, rhs: Self) -> Result<Self, ExactError> {
        let numerator = self
            .numerator
            .checked_mul(rhs.numerator)
            .ok_or(ExactError::ArithmeticCapacity)?;
        let denominator_bits = self
            .denominator_bits
            .checked_add(rhs.denominator_bits)
            .ok_or(ExactError::ArithmeticCapacity)?;
        Self::new(numerator, denominator_bits)
    }

    fn neg(self) -> Result<Self, ExactError> {
        Ok(Self {
            numerator: self
                .numerator
                .checked_neg()
                .ok_or(ExactError::ArithmeticCapacity)?,
            denominator_bits: self.denominator_bits,
        })
    }
}

/// An exact scalar `a + b sqrt(2) + i(c + d sqrt(2))`.
///
/// Each coefficient is a canonical signed dyadic rational. Numerators use
/// `i128`; nonzero denominator exponents are at most 126. Arithmetic can reject
/// intermediate overflow even when a different evaluation order would fit.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Exact {
    coefficients: [Dyadic; 4],
}

impl Exact {
    pub const fn zero() -> Self {
        Self::integer(0)
    }

    pub const fn one() -> Self {
        Self::integer(1)
    }

    pub const fn integer(value: i128) -> Self {
        Self {
            coefficients: [
                Dyadic::integer(value),
                Dyadic::integer(0),
                Dyadic::integer(0),
                Dyadic::integer(0),
            ],
        }
    }

    /// Construct `(a + b sqrt(2) + i(c + d sqrt(2))) / 2^denominator_bits`.
    pub fn new(coefficients: [i128; 4], denominator_bits: u32) -> Result<Self, ExactError> {
        let mut canonical = [Dyadic::integer(0); 4];
        for (output, numerator) in canonical.iter_mut().zip(coefficients) {
            *output = Dyadic::new(numerator, denominator_bits)?;
        }
        Ok(Self {
            coefficients: canonical,
        })
    }

    pub const fn inv_sqrt2() -> Self {
        Self {
            coefficients: [
                Dyadic::integer(0),
                Dyadic {
                    numerator: 1,
                    denominator_bits: 1,
                },
                Dyadic::integer(0),
                Dyadic::integer(0),
            ],
        }
    }

    /// The exact phase `exp(i pi k / 4)`, including its global phase.
    pub fn phase(k: i32) -> Self {
        let zero = Dyadic::integer(0);
        let one = Dyadic::integer(1);
        let minus_one = Dyadic::integer(-1);
        let half = Dyadic {
            numerator: 1,
            denominator_bits: 1,
        };
        let minus_half = Dyadic {
            numerator: -1,
            denominator_bits: 1,
        };
        let coefficients = match k.rem_euclid(8) {
            0 => [one, zero, zero, zero],
            1 => [zero, half, zero, half],
            2 => [zero, zero, one, zero],
            3 => [zero, minus_half, zero, half],
            4 => [minus_one, zero, zero, zero],
            5 => [zero, minus_half, zero, minus_half],
            6 => [zero, zero, minus_one, zero],
            _ => [zero, half, zero, minus_half],
        };
        Self { coefficients }
    }

    // Named fallible operations make every capacity check explicit at call sites.
    #[allow(clippy::should_implement_trait)]
    pub fn add(self, rhs: Self) -> Result<Self, ExactError> {
        let mut coefficients = [Dyadic::integer(0); 4];
        for (index, output) in coefficients.iter_mut().enumerate() {
            *output = self.coefficients[index].add(rhs.coefficients[index])?;
        }
        Ok(Self { coefficients })
    }

    #[allow(clippy::should_implement_trait)]
    pub fn neg(self) -> Result<Self, ExactError> {
        let mut coefficients = self.coefficients;
        for value in &mut coefficients {
            *value = value.neg()?;
        }
        Ok(Self { coefficients })
    }

    #[allow(clippy::should_implement_trait)]
    pub fn mul(self, rhs: Self) -> Result<Self, ExactError> {
        let mut coefficients = [Dyadic::integer(0); 4];
        for (left, a) in self.coefficients.iter().enumerate() {
            for (right, b) in rhs.coefficients.iter().enumerate() {
                let mut product = a.mul(*b)?;
                // Basis index bit 0 denotes sqrt(2), bit 1 denotes i.
                if left & right & 1 != 0 {
                    product = product.mul(Dyadic::integer(2))?;
                }
                if left & right & 2 != 0 {
                    product = product.neg()?;
                }
                let index = left ^ right;
                coefficients[index] = coefficients[index].add(product)?;
            }
        }
        Ok(Self { coefficients })
    }

    pub fn conjugate(self) -> Result<Self, ExactError> {
        let mut coefficients = self.coefficients;
        coefficients[2] = coefficients[2].neg()?;
        coefficients[3] = coefficients[3].neg()?;
        Ok(Self { coefficients })
    }

    pub(super) fn diagnostic(self) -> String {
        let mut terms = Vec::new();
        for (coefficient, basis) in self
            .coefficients
            .iter()
            .zip(["", "sqrt(2)", "i", "i*sqrt(2)"])
        {
            if coefficient.numerator == 0 {
                continue;
            }
            let mut term = coefficient.numerator.to_string();
            if coefficient.denominator_bits != 0 {
                term = format!("({term}/2^{})", coefficient.denominator_bits);
            }
            if !basis.is_empty() {
                term.push('*');
                term.push_str(basis);
            }
            terms.push(term);
        }
        if terms.is_empty() {
            "0".to_owned()
        } else {
            terms.join(" + ")
        }
    }

    // Numerical comparisons in tests never authorize a semantic certificate.
    #[cfg(test)]
    pub(crate) fn components_f64(self) -> (f64, f64) {
        let [a, b, c, d] = self.coefficients.map(|coefficient| {
            coefficient.numerator as f64 / 2_f64.powi(coefficient.denominator_bits as i32)
        });
        (
            a + b * std::f64::consts::SQRT_2,
            c + d * std::f64::consts::SQRT_2,
        )
    }
}

/// A validated, nonempty, row-major exact matrix with bounded dimensions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Matrix {
    rows: usize,
    cols: usize,
    entries: Vec<Exact>,
}

impl Matrix {
    pub fn new(rows: usize, cols: usize, entries: Vec<Exact>) -> Result<Self, ExactError> {
        Self::check_dimensions(rows, cols)?;
        let expected = rows * cols;
        if entries.len() != expected {
            return Err(ExactError::EntryCount {
                expected,
                actual: entries.len(),
            });
        }
        Ok(Self {
            rows,
            cols,
            entries,
        })
    }

    fn check_dimensions(rows: usize, cols: usize) -> Result<(), ExactError> {
        if rows == 0 || cols == 0 || rows > MAX_MATRIX_DIMENSION || cols > MAX_MATRIX_DIMENSION {
            Err(ExactError::Dimension { rows, cols })
        } else {
            Ok(())
        }
    }

    pub fn identity(dim: usize) -> Result<Self, ExactError> {
        Self::check_dimensions(dim, dim)?;
        let mut entries = vec![Exact::zero(); dim * dim];
        for index in 0..dim {
            entries[index * dim + index] = Exact::one();
        }
        Self::new(dim, dim, entries)
    }

    pub fn rows(&self) -> usize {
        self.rows
    }

    pub fn cols(&self) -> usize {
        self.cols
    }

    pub fn entries(&self) -> &[Exact] {
        &self.entries
    }

    pub fn get(&self, row: usize, col: usize) -> Option<Exact> {
        if row < self.rows && col < self.cols {
            Some(self.entries[row * self.cols + col])
        } else {
            None
        }
    }

    /// Return `self * rhs`: apply `rhs` first, then `self`.
    pub fn compose(&self, rhs: &Self, budget: &mut Budget) -> Result<Self, ExactError> {
        if self.cols != rhs.rows {
            return Err(ExactError::ShapeMismatch);
        }
        // Validated dimensions make every product below at most 2 * 64^3.
        budget.charge(2 * self.rows * self.cols * rhs.cols)?;
        let mut entries = vec![Exact::zero(); self.rows * rhs.cols];
        for row in 0..self.rows {
            for col in 0..rhs.cols {
                let mut sum = Exact::zero();
                for inner in 0..self.cols {
                    sum = sum.add(
                        self.entries[row * self.cols + inner]
                            .mul(rhs.entries[inner * rhs.cols + col])?,
                    )?;
                }
                entries[row * rhs.cols + col] = sum;
            }
        }
        Self::new(self.rows, rhs.cols, entries)
    }

    /// Tensor product with `self` as the low-order component.
    ///
    /// Input index is `self_column + self.cols() * rhs_column`; output index
    /// is `self_row + self.rows() * rhs_row`. This agrees with Qleisli's bit
    /// order rather than the usual displayed Kronecker-product ordering.
    pub fn tensor(&self, rhs: &Self, budget: &mut Budget) -> Result<Self, ExactError> {
        let rows = self.rows * rhs.rows;
        let cols = self.cols * rhs.cols;
        Self::check_dimensions(rows, cols)?;
        budget.charge(rows * cols)?;
        let mut entries = vec![Exact::zero(); rows * cols];
        for row in 0..rows {
            for col in 0..cols {
                entries[row * cols + col] = self.entries
                    [(row % self.rows) * self.cols + col % self.cols]
                    .mul(rhs.entries[(row / self.rows) * rhs.cols + col / self.cols])?;
            }
        }
        Self::new(rows, cols, entries)
    }

    pub fn adjoint(&self, budget: &mut Budget) -> Result<Self, ExactError> {
        budget.charge(self.rows * self.cols)?;
        let mut entries = vec![Exact::zero(); self.entries.len()];
        for row in 0..self.rows {
            for col in 0..self.cols {
                entries[col * self.rows + row] = self.entries[row * self.cols + col].conjugate()?;
            }
        }
        Self::new(self.cols, self.rows, entries)
    }

    /// Check `self† * self == I` exactly, including every off-diagonal entry.
    pub fn is_isometry(&self, budget: &mut Budget) -> Result<bool, ExactError> {
        if self.rows < self.cols {
            return Ok(false);
        }
        Ok(self.adjoint(budget)?.compose(self, budget)? == Self::identity(self.cols)?)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn budget() -> Budget {
        Budget::new(10_000_000)
    }

    fn h() -> Matrix {
        let s = Exact::inv_sqrt2();
        Matrix::new(2, 2, vec![s, s, s, s.neg().unwrap()]).unwrap()
    }

    fn x() -> Matrix {
        Matrix::new(
            2,
            2,
            vec![Exact::zero(), Exact::one(), Exact::one(), Exact::zero()],
        )
        .unwrap()
    }

    #[test]
    fn canonical_dyadics_and_irrational_components_remain_distinct() {
        assert_eq!(
            Exact::new([6, -2, 0, 4], 2).unwrap(),
            Exact::new([3, -1, 0, 2], 1).unwrap()
        );
        assert_eq!(Exact::new([0; 4], u32::MAX).unwrap(), Exact::zero());
        assert_ne!(Exact::one(), Exact::new([0, 1, 0, 0], 0).unwrap());
        assert_eq!(
            Exact::inv_sqrt2().mul(Exact::inv_sqrt2()).unwrap(),
            Exact::new([1, 0, 0, 0], 1).unwrap()
        );
    }

    #[test]
    fn all_eighth_root_products_and_conjugates_are_exact() {
        for a in -8..16 {
            assert_eq!(Exact::phase(a).conjugate().unwrap(), Exact::phase(-a));
            for b in -8..16 {
                assert_eq!(
                    Exact::phase(a).mul(Exact::phase(b)).unwrap(),
                    Exact::phase(a + b)
                );
            }
        }
        assert_ne!(Exact::phase(0), Exact::phase(4));
        assert_eq!(Exact::phase(i32::MIN), Exact::one());
    }

    #[test]
    fn exact_complex_algebra_includes_cross_terms() {
        let a = Exact::new([2, -3, 5, 7], 2).unwrap();
        let b = Exact::new([-11, 13, 17, -19], 3).unwrap();
        // Independent expansion in the basis (1, sqrt(2), i, i sqrt(2)).
        assert_eq!(
            a.mul(b).unwrap(),
            Exact::new([81, 35, 275, -101], 5).unwrap()
        );
        assert_eq!(
            a.mul(b).unwrap().conjugate().unwrap(),
            a.conjugate().unwrap().mul(b.conjugate().unwrap()).unwrap()
        );
        assert_eq!(a.add(a.neg().unwrap()).unwrap(), Exact::zero());
    }

    #[test]
    fn capacity_errors_never_wrap_or_approximate() {
        assert_eq!(
            Exact::integer(i128::MAX).add(Exact::one()),
            Err(ExactError::ArithmeticCapacity)
        );
        assert_eq!(
            Exact::integer(i128::MIN).neg(),
            Err(ExactError::ArithmeticCapacity)
        );
        assert_eq!(
            Exact::new([0, 0, i128::MIN, 0], 0).unwrap().conjugate(),
            Err(ExactError::ArithmeticCapacity)
        );
        let tiny = Exact::new([1, 0, 0, 0], MAX_DENOMINATOR_BITS).unwrap();
        assert_eq!(tiny.mul(tiny), Err(ExactError::ArithmeticCapacity));
        assert_eq!(
            Exact::new([1, 0, 0, 0], u32::MAX),
            Err(ExactError::ArithmeticCapacity)
        );
        assert_eq!(
            Exact::integer(i128::MAX).add(tiny),
            Err(ExactError::ArithmeticCapacity)
        );
        assert_eq!(
            Exact::integer(i128::MAX).mul(Exact::integer(2)),
            Err(ExactError::ArithmeticCapacity)
        );
    }

    #[test]
    fn denominator_alignment_preserves_sign_at_capacity() {
        let tiny = Exact::new([1, 0, 0, 0], 126).unwrap();
        assert_eq!(
            Exact::one().add(tiny).unwrap(),
            Exact::new([(1_i128 << 126) + 1, 0, 0, 0], 126).unwrap()
        );
        assert_eq!(
            Exact::integer(-2).add(tiny).unwrap(),
            Exact::new([i128::MIN + 1, 0, 0, 0], 126).unwrap()
        );
        assert_eq!(
            Exact::integer(2).add(tiny),
            Err(ExactError::ArithmeticCapacity)
        );
        assert_eq!(Exact::new([2, 0, 0, 0], 127).unwrap(), tiny);
        assert_eq!(
            Exact::new([1, 0, 0, 0], 127),
            Err(ExactError::ArithmeticCapacity)
        );

        // Even if a future profile admits this exponent, scaling by 2^127
        // must reject rather than silently multiply by the negative i128::MIN.
        let beyond_profile = Dyadic {
            numerator: 1,
            denominator_bits: 127,
        };
        assert_eq!(
            Dyadic::integer(1).add(beyond_profile),
            Err(ExactError::ArithmeticCapacity)
        );
    }

    #[test]
    fn hadamard_squared_and_phase_sensitive_adjoint() {
        let mut work = budget();
        assert!(h().is_isometry(&mut work).unwrap());
        assert_eq!(
            h().compose(&h(), &mut work).unwrap(),
            Matrix::identity(2).unwrap()
        );
        let t = Matrix::new(
            2,
            2,
            vec![Exact::one(), Exact::zero(), Exact::zero(), Exact::phase(1)],
        )
        .unwrap();
        assert!(t.is_isometry(&mut work).unwrap());
        assert_eq!(
            t.adjoint(&mut work)
                .unwrap()
                .compose(&t, &mut work)
                .unwrap(),
            Matrix::identity(2).unwrap()
        );
    }

    #[test]
    fn tensor_places_first_operand_on_low_bits() {
        let mut work = budget();
        let low_x = x()
            .tensor(&Matrix::identity(2).unwrap(), &mut work)
            .unwrap();
        let high_x = Matrix::identity(2)
            .unwrap()
            .tensor(&x(), &mut work)
            .unwrap();
        for col in 0..4 {
            for row in 0..4 {
                assert_eq!(
                    low_x.get(row, col).unwrap(),
                    Exact::integer(i128::from(row == col ^ 1))
                );
                assert_eq!(
                    high_x.get(row, col).unwrap(),
                    Exact::integer(i128::from(row == col ^ 2))
                );
            }
        }
        let zero = Matrix::new(2, 1, vec![Exact::one(), Exact::zero()]).unwrap();
        let encoding = Matrix::identity(2)
            .unwrap()
            .tensor(&zero, &mut work)
            .unwrap();
        assert_eq!((encoding.rows(), encoding.cols()), (4, 2));
        assert!(encoding.is_isometry(&mut work).unwrap());
        assert_eq!(encoding.get(1, 1), Some(Exact::one()));
        assert_eq!(encoding.get(3, 1), Some(Exact::zero()));
    }

    #[test]
    fn isometry_checks_cross_column_inner_products() {
        let mut work = budget();
        let repeated = Matrix::new(
            2,
            2,
            vec![Exact::one(), Exact::one(), Exact::zero(), Exact::zero()],
        )
        .unwrap();
        assert!(!repeated.is_isometry(&mut work).unwrap());
        let too_wide = Matrix::new(1, 2, vec![Exact::one(), Exact::zero()]).unwrap();
        assert!(!too_wide.is_isometry(&mut work).unwrap());
        let leaking = Matrix::new(2, 1, vec![Exact::one(), Exact::one()]).unwrap();
        assert!(!leaking.is_isometry(&mut work).unwrap());
    }

    #[test]
    fn dimensions_entries_and_getters_are_bounded() {
        for (rows, cols) in [(0, 1), (1, 0), (65, 1), (1, 65), (usize::MAX, 2)] {
            assert_eq!(
                Matrix::new(rows, cols, vec![]),
                Err(ExactError::Dimension { rows, cols })
            );
        }
        assert_eq!(
            Matrix::new(2, 2, vec![Exact::zero()]),
            Err(ExactError::EntryCount {
                expected: 4,
                actual: 1
            })
        );
        let identity = Matrix::identity(64).unwrap();
        assert_eq!(identity.entries().len(), 4096);
        assert_eq!(identity.get(usize::MAX, 0), None);
        assert_eq!(identity.get(0, usize::MAX), None);
        assert!(identity.tensor(&x(), &mut budget()).is_err());
        let column = Matrix::new(2, 1, vec![Exact::one(), Exact::zero()]).unwrap();
        assert_eq!(
            column.compose(&x(), &mut budget()),
            Err(ExactError::ShapeMismatch)
        );
    }

    #[test]
    fn shared_budget_cannot_be_reset_by_matrix_composition() {
        let mut work = Budget::new(16);
        assert_eq!(
            h().compose(&h(), &mut work).unwrap(),
            Matrix::identity(2).unwrap()
        );
        assert_eq!(work.remaining(), 0);
        assert_eq!(h().compose(&h(), &mut work), Err(ExactError::WorkLimit));
        assert_eq!(work.remaining(), 0);
        assert_eq!(h().adjoint(&mut work), Err(ExactError::WorkLimit));
        assert_eq!(h().tensor(&h(), &mut work), Err(ExactError::WorkLimit));
        assert_eq!(h().is_isometry(&mut work), Err(ExactError::WorkLimit));
    }
}
