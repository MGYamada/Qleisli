//! Classical postprocessing, separate from `.qli` quantum operations.
//! These routines cannot create or bypass a [`crate::VerifiedProgram`].

use std::fmt;

/// A checked nontrivial factor pair. Neither factor is claimed to be prime.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Factors {
    /// A verified even exponent r with a^r = 1 mod n, not necessarily minimal.
    pub period_candidate: u32,
    pub factor: u32,
    pub cofactor: u32,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PhaseInputError {
    Modulus,
    Base,
    Precision,
    Outcome,
}

impl fmt::Display for PhaseInputError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Modulus => "modulus must be odd and at least 3",
            Self::Base => "base must satisfy 1 < a < n and gcd(a, n) = 1",
            Self::Precision => "phase precision must be in 1..=32 bits",
            Self::Outcome => "phase outcome must be smaller than 2^phase_bits",
        })
    }
}

impl std::error::Error for PhaseInputError {}

fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

fn pow_mod(mut base: u64, mut exponent: u64, modulus: u64) -> u64 {
    let mut result = 1;
    while exponent != 0 {
        if exponent & 1 != 0 {
            result = result * base % modulus;
        }
        base = base * base % modulus;
        exponent >>= 1;
    }
    result
}

/// Try to extract a factor from one QPE outcome, interpreted as outcome/2^m.
///
/// `outcome` is an integer, not a displayed bit string. For a low-bit-first
/// phase register, bit i contributes `u32::from(bit) << i`; for example the
/// displayed phase bits `100` represent outcome 1, hence phase 1/8 at m=3.
/// The caller selects the phase-register bits from its classical output tuple.
///
/// Uses only continued-fraction convergents with a nonzero numerator and
/// denominator r < n. An even r must pass a^r mod n = 1 before gcd extraction.
/// Returns `None` when this sample supplies no usable candidate (retry with a
/// newly prepared state, or another base). Does not search multiples, combine
/// samples, choose bases, or promise successful recovery at arbitrary precision.
/// All arithmetic is exact; u32 inputs keep modular products within u64.
pub fn factor_from_phase(
    n: u32,
    a: u32,
    phase_bits: u8,
    outcome: u32,
) -> Result<Option<Factors>, PhaseInputError> {
    if n < 3 || n % 2 == 0 {
        return Err(PhaseInputError::Modulus);
    }
    let (n, a) = (u64::from(n), u64::from(a));
    if a <= 1 || a >= n || gcd(a, n) != 1 {
        return Err(PhaseInputError::Base);
    }
    if !(1..=32).contains(&phase_bits) {
        return Err(PhaseInputError::Precision);
    }
    let scale = 1u64 << phase_bits;
    if u64::from(outcome) >= scale {
        return Err(PhaseInputError::Outcome);
    }
    let (mut numerator, mut denominator) = (u64::from(outcome), scale);
    let (mut p0, mut p1) = (0, 1);
    let (mut q0, mut q1) = (1, 0);
    while denominator != 0 {
        let quotient = numerator / denominator;
        // Convergent numerators/denominators never exceed the original
        // numerator/denominator, which are at most 2^32.
        let (p, r) = (quotient * p1 + p0, quotient * q1 + q0);
        if r >= n {
            break;
        }
        if p != 0 && r % 2 == 0 && pow_mod(a, r, n) == 1 {
            let half = pow_mod(a, r / 2, n);
            // Coprimality ensures half is nonzero, so subtraction is safe.
            let factor = gcd(half - 1, n);
            if factor > 1 && factor < n {
                let cofactor = n / factor;
                return Ok(Some(Factors {
                    period_candidate: r as u32,
                    factor: factor.min(cofactor) as u32,
                    cofactor: factor.max(cofactor) as u32,
                }));
            }
        }
        (p0, p1) = (p1, p);
        (q0, q1) = (q1, r);
        (numerator, denominator) = (denominator, numerator % denominator);
    }
    Ok(None)
}
