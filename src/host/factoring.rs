use super::TrialDecision;
use std::fmt;

/// Successful classical prechecks are distinguished from quantum trials.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FactorPrecheck {
    Factors { factor: u32, cofactor: u32 },
    QuantumTrial,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FactorRetry {
    InvalidCandidate,
    OddPeriod,
    TrivialFactor,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PeriodFactors {
    /// The minimal positive order, after prime-divisor reduction.
    pub period: u32,
    pub factor: u32,
    pub cofactor: u32,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FactorTrialError {
    InvalidInput(&'static str),
    Limit,
}

impl fmt::Display for FactorTrialError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidInput(field) => write!(f, "invalid factor-trial input: {field}"),
            Self::Limit => f.write_str("factor-trial arithmetic limit or overflow"),
        }
    }
}
impl std::error::Error for FactorTrialError {}

struct Arithmetic {
    remaining: u64,
}
impl Arithmetic {
    fn step(&mut self) -> Result<(), FactorTrialError> {
        self.remaining = self
            .remaining
            .checked_sub(1)
            .ok_or(FactorTrialError::Limit)?;
        Ok(())
    }
    fn gcd(&mut self, mut a: u128, mut b: u128) -> Result<u128, FactorTrialError> {
        while b != 0 {
            self.step()?;
            (a, b) = (b, a % b);
        }
        Ok(a)
    }
    fn power(&mut self, mut a: u128, mut k: u128, n: u128) -> Result<u128, FactorTrialError> {
        let mut result = 1;
        while k > 0 {
            self.step()?;
            if k & 1 != 0 {
                result = a.checked_mul(result).ok_or(FactorTrialError::Limit)? % n;
            }
            a = a.checked_mul(a).ok_or(FactorTrialError::Limit)? % n;
            k >>= 1;
        }
        Ok(result)
    }
    fn reduce(&mut self, mut r: u128, a: u128, n: u128) -> Result<u128, FactorTrialError> {
        let mut rest = r;
        let mut p = 2;
        while p <= rest / p {
            self.step()?;
            if rest % p == 0 {
                while rest % p == 0 {
                    self.step()?;
                    rest /= p;
                }
                while r % p == 0 && self.power(a, r / p, n)? == 1 {
                    self.step()?;
                    r /= p;
                }
            }
            p += if p == 2 { 1 } else { 2 };
        }
        if rest > 1 {
            while r % rest == 0 && self.power(a, r / rest, n)? == 1 {
                self.step()?;
                r /= rest;
            }
        }
        Ok(r)
    }
}

fn factors(n: u128, p: u128) -> Option<(u32, u32)> {
    if p <= 1 || p >= n || n % p != 0 {
        return None;
    }
    let q = n / p;
    if q <= 1 || q >= n || p.checked_mul(q) != Some(n) {
        return None;
    }
    Some((p.min(q) as u32, p.max(q) as u32))
}

/// Classical even-modulus/gcd checks, without claiming any quantum trial.
pub fn factor_precheck(n: u32, a: u32) -> Result<FactorPrecheck, FactorTrialError> {
    if n < 2 {
        return Err(FactorTrialError::InvalidInput("modulus"));
    }
    if a <= 1 || a >= n {
        return Err(FactorTrialError::InvalidInput("base"));
    }
    let mut work = Arithmetic {
        remaining: 1_000_000,
    };
    let n = u128::from(n);
    let p = if n % 2 == 0 {
        2
    } else {
        work.gcd(u128::from(a), n)?
    };
    Ok(match factors(n, p) {
        Some((factor, cofactor)) => FactorPrecheck::Factors { factor, cofactor },
        None => FactorPrecheck::QuantumTrial,
    })
}

/// Validate continued-fraction candidates from one low-bit-first QPE outcome.
///
/// Domain: 2 <= n < 2^32, 1 < a < n, gcd(a,n)=1, 1 <= precision <= 32,
/// outcome < 2^precision. Convergents are visited in order; an order candidate
/// must pass modular exponentiation, then prime-divisor minimality reduction.
/// Failure to recover a useful period is a typed retry, not an execution error.
/// This bounded host algorithm neither supplies scalable modular circuitry nor
/// proves that any specified QPE precision will recover an order reliably.
pub fn factor_trial_from_phase(
    n: u32,
    a: u32,
    precision: u8,
    outcome: u32,
) -> Result<TrialDecision<PeriodFactors, FactorRetry>, FactorTrialError> {
    let mut work = Arithmetic {
        remaining: 1_000_000,
    };
    factor_trial(n, a, precision, outcome, &mut work)
}

fn factor_trial(
    n: u32,
    a: u32,
    precision: u8,
    outcome: u32,
    work: &mut Arithmetic,
) -> Result<TrialDecision<PeriodFactors, FactorRetry>, FactorTrialError> {
    if n < 2 {
        return Err(FactorTrialError::InvalidInput("modulus"));
    }
    if a <= 1 || a >= n {
        return Err(FactorTrialError::InvalidInput("base"));
    }
    if !(1..=32).contains(&precision) {
        return Err(FactorTrialError::InvalidInput("precision"));
    }
    let scale = 1_u128 << precision;
    if u128::from(outcome) >= scale {
        return Err(FactorTrialError::InvalidInput("outcome"));
    }
    let (n, a) = (u128::from(n), u128::from(a));
    if work.gcd(a, n)? != 1 {
        return Err(FactorTrialError::InvalidInput("coprimality"));
    }
    let (mut numerator, mut denominator) = (u128::from(outcome), scale);
    let (mut q0, mut q1) = (1_u128, 0_u128);
    while denominator != 0 {
        work.step()?;
        let quotient = numerator / denominator;
        let r = quotient
            .checked_mul(q1)
            .and_then(|x| x.checked_add(q0))
            .ok_or(FactorTrialError::Limit)?;
        if r >= n {
            break;
        }
        if r > 0 && work.power(a, r, n)? == 1 {
            let r = work.reduce(r, a, n)?;
            if r % 2 != 0 {
                return Ok(TrialDecision::Retry(FactorRetry::OddPeriod));
            }
            let half = work.power(a, r / 2, n)?;
            let before = half.checked_sub(1).ok_or(FactorTrialError::Limit)?;
            let after = half.checked_add(1).ok_or(FactorTrialError::Limit)?;
            for candidate in [before, after] {
                if let Some((factor, cofactor)) = factors(n, work.gcd(candidate, n)?) {
                    return Ok(TrialDecision::Accepted(PeriodFactors {
                        period: r as u32,
                        factor,
                        cofactor,
                    }));
                }
            }
            return Ok(TrialDecision::Retry(FactorRetry::TrivialFactor));
        }
        (q0, q1) = (q1, r);
        (numerator, denominator) = (denominator, numerator % denominator);
    }
    Ok(TrialDecision::Retry(FactorRetry::InvalidCandidate))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn minimality_and_work_exhaustion_are_checked() {
        let mut work = Arithmetic {
            remaining: 1_000_000,
        };
        assert_eq!(work.reduce(12, 2, 15).unwrap(), 4);
        assert_eq!(
            factor_trial(15, 2, 3, 2, &mut Arithmetic { remaining: 0 }),
            Err(FactorTrialError::Limit)
        );
    }
}
