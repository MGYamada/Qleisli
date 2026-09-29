//! Exact mathematical descriptions for bound finite leaves. Decoding is not
//! semantic verification. Copyright 2026 Masahiko G. Yamada, Apache-2.0.

use super::json::{self, Value};
use super::{Error, Result, contract_error};
use crate::contract::exact::{Budget, Exact, MAX_DENOMINATOR_BITS, MAX_MATRIX_DIMENSION, Matrix};
use crate::contract::{ContractError, DEFAULT_EXACT_WORK};

const FORMAT: &str = "qleisli.finite-matrix";
const DOMAIN: &str = "zeta8-dyadic-v1";

/// Encode all exact coefficients, including their independent exponents.
/// This adds no evidence and performs no equation or isometry check.
pub fn encode(matrix: &Matrix) -> Result<Vec<u8>> {
    let entries = matrix
        .entries()
        .iter()
        .map(|entry| {
            Value::Array(
                entry
                    .dyadics()
                    .into_iter()
                    .map(|(numerator, exponent)| {
                        Value::object([
                            ("numerator", Value::String(numerator.to_string())),
                            ("denominator_bits", Value::Number(u64::from(exponent))),
                        ])
                    })
                    .collect(),
            )
        })
        .collect();
    json::encode(&Value::object([
        ("format", Value::String(FORMAT.into())),
        ("version", Value::Number(1)),
        ("domain", Value::String(DOMAIN.into())),
        ("rows", Value::Number(matrix.rows() as u64)),
        ("cols", Value::Number(matrix.cols() as u64)),
        ("entries", Value::Array(entries)),
    ]))
}

fn dyadic(value: &Value) -> Result<(i128, u32)> {
    value.fields(&["numerator", "denominator_bits"])?;
    let numerator = value.field("numerator")?.text()?;
    let digits = numerator.strip_prefix('-').unwrap_or(numerator);
    if digits.is_empty()
        || !digits.bytes().all(|b| b.is_ascii_digit())
        || (digits.starts_with('0') && (digits.len() != 1 || numerator != "0"))
    {
        return Err(Error::format("expected canonical signed decimal numerator"));
    }
    let numerator: i128 = numerator
        .parse()
        .map_err(|_| Error::limit("exact numerator exceeds i128"))?;
    let exponent = value.field("denominator_bits")?.number()?;
    if exponent > u64::from(MAX_DENOMINATOR_BITS) {
        return Err(Error::limit("exact denominator exponent exceeds 126"));
    }
    if exponent != 0 && numerator % 2 == 0 {
        return Err(Error::format("expected a reduced dyadic coefficient"));
    }
    Ok((numerator, exponent as u32))
}

/// Read untrusted mathematical data under the caller's shared exact budget.
/// Charge four units per entry before scalar construction, with no refund on
/// failure. JSON tokenization is bounded separately by the transport limits.
pub fn decode(description: &[u8], budget: &mut Budget) -> Result<Matrix> {
    if budget.remaining() > DEFAULT_EXACT_WORK {
        return Err(Error::limit(
            "finite matrix budget exceeds the shared exact-work ceiling",
        ));
    }
    let value = json::parse(description)?;
    value.fields(&["format", "version", "domain", "rows", "cols", "entries"])?;
    if value.field("format")?.text()? != FORMAT
        || value.field("version")?.number()? != 1
        || value.field("domain")?.text()? != DOMAIN
    {
        return Err(Error::format(
            "unsupported exact matrix format, version or domain",
        ));
    }
    let dimension = |name: &str| -> Result<usize> {
        let n = value.field(name)?.number()?;
        if n == 0 || n > MAX_MATRIX_DIMENSION as u64 {
            return Err(
                Error::limit("exact matrix dimensions must be in 1..=64").at(format!("/{name}"))
            );
        }
        Ok(n as usize)
    };
    let rows = dimension("rows")?;
    let cols = dimension("cols")?;
    let entries = value.field("entries")?.array()?;
    if entries.len() != rows * cols {
        return Err(
            Error::format("exact matrix entry count differs from rows*cols").at("/entries"),
        );
    }
    budget
        .charge(4 * entries.len())
        .map_err(ContractError::from)
        .map_err(contract_error)?;
    let mut exact = Vec::with_capacity(entries.len());
    for (index, entry) in entries.iter().enumerate() {
        let coefficients = entry
            .array()
            .map_err(|e| e.at(format!("/entries/{index}")))?;
        if coefficients.len() != 4 {
            return Err(
                Error::format("exact scalar requires four dyadic coefficients")
                    .at(format!("/entries/{index}")),
            );
        }
        let mut decoded = [(0, 0); 4];
        for (j, (out, coefficient)) in decoded.iter_mut().zip(coefficients).enumerate() {
            *out = dyadic(coefficient).map_err(|e| e.at(format!("/entries/{index}/{j}")))?;
        }
        exact.push(
            Exact::from_dyadics(decoded)
                .map_err(ContractError::from)
                .map_err(contract_error)?,
        );
    }
    Matrix::new(rows, cols, exact)
        .map_err(ContractError::from)
        .map_err(contract_error)
}
