//! Separate engineering bounds between independently checked pure artifacts.
//! A bound, including zero, grants no exact equation, source preservation,
//! inverse/control capability, cleanup, target realization or resource evidence.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0

mod runtime;

use std::path::{Path, PathBuf};
use std::sync::Arc;

use super::codec::Codec;
use super::json::{self, Value};
use super::native::Kernel;
use super::pure_leaf::PureBoundary;
use super::{Encoder, Error, Result, Version};
use crate::AcceptedProgram;
use crate::contract::exact::{MAX_DENOMINATOR_BITS, Matrix};
use crate::contract::{BasisType, DEFAULT_EXACT_WORK, exact::Budget};
use crate::ir::QuantumPort;

const FORMAT: &str = "qleisli.engineering-pure-request";
const CLAIM_KIND: &str = "engineering";
const METRIC: &str = "pure-euclidean-operator-norm-v1";
const CHECKER_PROFILE: &str = "frobenius-r8-pure-leaf-v1";
const TARGET_PROFILE: &str = "qirf-r8-pure-v1";
const COMPOSITION: &str = "single-component-v1";
const ERROR_CATEGORY: &str = "implementation-distance";
const MAX_FILE_BYTES: usize = 16 << 20;

/// A finite nonnegative canonical dyadic engineering budget.
/// Construction checks data only; zero has the same engineering status.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct DyadicBound {
    numerator: i128,
    denominator_bits: u32,
}

impl DyadicBound {
    pub fn new(numerator: i128, denominator_bits: u32) -> Result<Self> {
        if numerator < 0
            || denominator_bits > MAX_DENOMINATOR_BITS
            || denominator_bits != 0 && numerator % 2 == 0
        {
            return Err(Error::format(
                "engineering epsilon must be a nonnegative reduced dyadic with exponent at most 126",
            ));
        }
        Ok(Self {
            numerator,
            denominator_bits,
        })
    }

    pub fn numerator(self) -> i128 {
        self.numerator
    }

    pub fn denominator_bits(self) -> u32 {
        self.denominator_bits
    }
}

/// Data describing two independent body equations and one engineering budget.
/// Matching tree/shape validation adds no semantic acceptance authority.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EngineeringPureRequest {
    actual_boundary: PureBoundary,
    actual_meaning: Matrix,
    ideal_boundary: PureBoundary,
    ideal_meaning: Matrix,
    epsilon: DyadicBound,
}

impl EngineeringPureRequest {
    pub fn new(
        actual_boundary: PureBoundary,
        actual_meaning: Matrix,
        ideal_boundary: PureBoundary,
        ideal_meaning: Matrix,
        epsilon: DyadicBound,
    ) -> Result<Self> {
        if actual_boundary.domain() != ideal_boundary.domain()
            || actual_boundary.codomain() != ideal_boundary.codomain()
        {
            return Err(Error::format(
                "engineering pure comparison requires identical full domain and codomain trees",
            ));
        }
        for (boundary, matrix) in [
            (&actual_boundary, &actual_meaning),
            (&ideal_boundary, &ideal_meaning),
        ] {
            let dimension = |bits: usize| {
                u32::try_from(bits)
                    .ok()
                    .and_then(|bits| 1usize.checked_shl(bits))
            };
            if dimension(boundary.domain().bits().map_err(super::contract_error)?)
                != Some(matrix.cols())
                || dimension(boundary.codomain().bits().map_err(super::contract_error)?)
                    != Some(matrix.rows())
            {
                return Err(Error::format(
                    "engineering pure matrices must match the independently requested full types",
                ));
            }
        }
        Ok(Self {
            actual_boundary,
            actual_meaning,
            ideal_boundary,
            ideal_meaning,
            epsilon,
        })
    }

    pub fn actual_boundary(&self) -> &PureBoundary {
        &self.actual_boundary
    }

    pub fn actual_meaning(&self) -> &Matrix {
        &self.actual_meaning
    }

    pub fn ideal_boundary(&self) -> &PureBoundary {
        &self.ideal_boundary
    }

    pub fn ideal_meaning(&self) -> &Matrix {
        &self.ideal_meaning
    }

    pub fn epsilon(&self) -> DyadicBound {
        self.epsilon
    }
}

/// One immutable invocation, retained without sharing the exact acceptance
/// module's Subject, Prepared, NativeChecked or accepted-handle constructors.
#[derive(Debug)]
struct Subject {
    actual: AcceptedProgram,
    ideal: AcceptedProgram,
    request: EngineeringPureRequest,
    request_bytes: Arc<[u8]>,
    checker: PathBuf,
}

#[derive(Debug)]
struct Decision {
    subject: Arc<Subject>,
    exact_work: usize,
}

/// A fresh engineering decision bound to both original graphs and requests.
/// No serialized success, zero budget or this report can construct an exact
/// accepted program, Meaning, capability, cleanup or resource certificate.
///
/// ```compile_fail
/// use qleisli::{AcceptedProgram, interchange::engineering_pure::EngineeringPureReport};
/// fn promote(report: EngineeringPureReport) -> AcceptedProgram { report.into() }
/// ```
/// ```compile_fail
/// use qleisli::interchange::engineering_pure::EngineeringPureReport;
/// fn deserialize_success() -> EngineeringPureReport {
///     EngineeringPureReport { exact_work: 0 }
/// }
/// ```
#[derive(Debug)]
pub struct EngineeringPureReport {
    subject: Arc<Subject>,
    exact_work: usize,
}

impl EngineeringPureReport {
    pub fn actual_artifact(&self) -> &[u8] {
        self.subject.actual.artifact()
    }

    pub fn ideal_artifact(&self) -> &[u8] {
        self.subject.ideal.artifact()
    }

    pub fn request(&self) -> &EngineeringPureRequest {
        &self.subject.request
    }

    pub fn request_bytes(&self) -> &[u8] {
        &self.subject.request_bytes
    }

    pub fn exact_work(&self) -> usize {
        self.exact_work
    }

    /// Canonical path selected for this invocation, without binary attestation.
    pub fn checker(&self) -> &Path {
        &self.subject.checker
    }

    pub fn metric(&self) -> &'static str {
        METRIC
    }

    pub fn claim_kind(&self) -> &'static str {
        CLAIM_KIND
    }

    pub fn composition(&self) -> &'static str {
        COMPOSITION
    }

    pub fn error_category(&self) -> &'static str {
        ERROR_CATEGORY
    }

    pub fn checker_profile(&self) -> &'static str {
        CHECKER_PROFILE
    }

    /// An IR profile, not a hardware target or realizability claim.
    pub fn target_profile(&self) -> &'static str {
        TARGET_PROFILE
    }
}

impl Subject {
    fn prepare(
        kernel: &Kernel,
        actual: &AcceptedProgram,
        ideal: &AcceptedProgram,
        request: &EngineeringPureRequest,
    ) -> Result<Arc<Self>> {
        let request_bytes = encode_request(request, ideal.artifact())?;
        Self::prepare_bytes(kernel, actual, ideal, request, request_bytes.into())
    }

    fn prepare_bytes(
        kernel: &Kernel,
        actual: &AcceptedProgram,
        ideal: &AcceptedProgram,
        request: &EngineeringPureRequest,
        request_bytes: Arc<[u8]>,
    ) -> Result<Arc<Self>> {
        for bytes in [actual.artifact(), ideal.artifact(), &request_bytes] {
            if bytes.is_empty() || bytes.len() > MAX_FILE_BYTES {
                return Err(Error::limit(
                    "engineering input must contain 1..16777216 bytes per file",
                ));
            }
        }
        let checker = std::fs::canonicalize(kernel.checker_path())
            .map_err(|e| Error::new("io", format!("cannot resolve Lean checker: {e}")))?;
        Ok(Arc::new(Self {
            actual: actual.clone(),
            ideal: ideal.clone(),
            request: request.clone(),
            request_bytes,
            checker,
        }))
    }

    fn packet(&self) -> Result<Vec<u8>> {
        let actual = self.actual.artifact();
        let request = &self.request_bytes;
        let mut original = Vec::with_capacity(12 + actual.len() + request.len());
        original.extend_from_slice(b"QLV1");
        original.extend_from_slice(&(actual.len() as u32).to_le_bytes());
        original.extend_from_slice(&(request.len() as u32).to_le_bytes());
        original.extend_from_slice(actual);
        original.extend_from_slice(request);
        let graph = super::execution_view::finite::engineering_pure::complete(
            &self.request,
            &self.ideal,
            &self.actual,
        )?;
        let (packet, scope) = super::native_packet::encode(
            &original,
            Some(super::native_packet::View {
                graph: &graph,
                caller: None,
            }),
        )?;
        if scope != super::native_packet::Scope::Execution {
            return Err(Error::format(
                "engineering requires an execution comparison",
            ));
        }
        Ok(packet)
    }

    fn bind(self: Arc<Self>, decision: Decision) -> Result<EngineeringPureReport> {
        if !Arc::ptr_eq(&self, &decision.subject) {
            return Err(Error::new(
                "kernel",
                "engineering decision belongs to a different subject",
            ));
        }
        Ok(EngineeringPureReport {
            subject: self,
            exact_work: decision.exact_work,
        })
    }
}

/// Check both original immutable artifacts freshly in the engineering mode.
/// The checker uses each body's own exact equation and Gram check before
/// bounding their difference. Failure never falls back to exact acceptance.
pub fn check_with_kernel(
    kernel: &Kernel,
    actual: &AcceptedProgram,
    ideal: &AcceptedProgram,
    request: &EngineeringPureRequest,
) -> Result<EngineeringPureReport> {
    let subject = Subject::prepare(kernel, actual, ideal, request)?;
    submit(subject)
}

fn submit(subject: Arc<Subject>) -> Result<EngineeringPureReport> {
    let exact_work = runtime::check(&subject.checker, subject.packet()?)?;
    let decision = Decision {
        subject: Arc::clone(&subject),
        exact_work,
    };
    subject.bind(decision)
}

/// Decode a bounded untrusted engineering request, check both original
/// artifacts for ordinary validity, then freshly check the engineering bound.
/// QDV1 is walked from typed requests and the retained checked graphs, never
/// from the JSON syntax or a deserialized success report. The original request
/// bytes are retained unchanged, including insignificant whitespace.
pub fn check_serialized_with_kernel(
    kernel: &Kernel,
    actual_artifact: &[u8],
    request_bytes: &[u8],
) -> Result<EngineeringPureReport> {
    if actual_artifact.is_empty() || actual_artifact.len() > MAX_FILE_BYTES {
        return Err(Error::limit(
            "engineering actual artifact must contain 1..16777216 bytes",
        ));
    }
    let (request, expected_artifact) = decode_request(request_bytes)?;
    let actual = kernel.check(actual_artifact, None)?.into_program();
    let ideal = kernel
        .check(expected_artifact.as_bytes(), None)?
        .into_program();
    submit(Subject::prepare_bytes(
        kernel,
        &actual,
        &ideal,
        &request,
        Arc::from(request_bytes),
    )?)
}

/// Explicit environment selection, with no fallback or automatic download.
pub fn check(
    actual: &AcceptedProgram,
    ideal: &AcceptedProgram,
    request: &EngineeringPureRequest,
) -> Result<EngineeringPureReport> {
    check_with_kernel(&Kernel::selected()?, actual, ideal, request)
}

fn encode_request(request: &EngineeringPureRequest, expected_artifact: &[u8]) -> Result<Vec<u8>> {
    let expected_artifact = std::str::from_utf8(expected_artifact)
        .map_err(|_| Error::format("engineering ideal artifact requires UTF-8"))?;
    let mut encoder = Encoder::new(Version::V2);
    let leaf = |boundary: &PureBoundary, meaning: &Matrix, encoder: &mut Encoder| {
        Ok::<_, Error>(Value::object([
            ("input", boundary.input().write(encoder)?),
            ("output", boundary.output().write(encoder)?),
            (
                "matrix",
                json::parse(&super::finite_matrix::encode(meaning)?)?,
            ),
        ]))
    };
    json::encode(&Value::object([
        ("format", Value::String(FORMAT.into())),
        ("version", Value::Number(1)),
        ("claim_kind", Value::String(CLAIM_KIND.into())),
        ("metric", Value::String(METRIC.into())),
        ("checker_profile", Value::String(CHECKER_PROFILE.into())),
        ("target_profile", Value::String(TARGET_PROFILE.into())),
        ("composition", Value::String(COMPOSITION.into())),
        ("error_category", Value::String(ERROR_CATEGORY.into())),
        (
            "domain",
            request.actual_boundary.domain().write(&mut encoder)?,
        ),
        (
            "codomain",
            request.actual_boundary.codomain().write(&mut encoder)?,
        ),
        (
            "actual",
            leaf(
                &request.actual_boundary,
                &request.actual_meaning,
                &mut encoder,
            )?,
        ),
        (
            "ideal",
            leaf(
                &request.ideal_boundary,
                &request.ideal_meaning,
                &mut encoder,
            )?,
        ),
        (
            "epsilon",
            Value::object([
                (
                    "numerator",
                    Value::String(request.epsilon.numerator.to_string()),
                ),
                (
                    "denominator_bits",
                    Value::Number(u64::from(request.epsilon.denominator_bits)),
                ),
            ]),
        ),
        ("expected_artifact", Value::String(expected_artifact.into())),
    ]))
}

fn decode_request(bytes: &[u8]) -> Result<(EngineeringPureRequest, String)> {
    let value = json::parse(bytes)?;
    value.fields(&[
        "format",
        "version",
        "claim_kind",
        "metric",
        "checker_profile",
        "target_profile",
        "composition",
        "error_category",
        "domain",
        "codomain",
        "actual",
        "ideal",
        "epsilon",
        "expected_artifact",
    ])?;
    if value.field("version")?.number()? != 1 {
        return Err(Error::format("unknown engineering request version"));
    }
    for (field, expected) in [
        ("format", FORMAT),
        ("claim_kind", CLAIM_KIND),
        ("metric", METRIC),
        ("checker_profile", CHECKER_PROFILE),
        ("target_profile", TARGET_PROFILE),
        ("composition", COMPOSITION),
        ("error_category", ERROR_CATEGORY),
    ] {
        if value.field(field)?.text()? != expected {
            return Err(Error::format(format!(
                "unknown engineering request {field}"
            )));
        }
    }
    let decoder = super::Decoder { evidence: &[] };
    let domain = BasisType::read(value.field("domain")?, &decoder)?;
    let codomain = BasisType::read(value.field("codomain")?, &decoder)?;
    let mut budget = Budget::new(DEFAULT_EXACT_WORK);
    let mut leaf = |name: &str| -> Result<(PureBoundary, Matrix)> {
        let value = value.field(name)?;
        value.fields(&["input", "output", "matrix"])?;
        let boundary = PureBoundary::new(
            domain.clone(),
            codomain.clone(),
            QuantumPort::read(value.field("input")?, &decoder)?,
            QuantumPort::read(value.field("output")?, &decoder)?,
        )?;
        let matrix =
            super::finite_matrix::decode(&json::encode(value.field("matrix")?)?, &mut budget)?;
        Ok((boundary, matrix))
    };
    let (actual_boundary, actual_meaning) = leaf("actual")?;
    let (ideal_boundary, ideal_meaning) = leaf("ideal")?;
    let epsilon = value.field("epsilon")?;
    epsilon.fields(&["numerator", "denominator_bits"])?;
    let numerator = epsilon.field("numerator")?.text()?;
    if numerator.is_empty()
        || !numerator.bytes().all(|b| b.is_ascii_digit())
        || numerator.len() > 1 && numerator.starts_with('0')
    {
        return Err(Error::format(
            "noncanonical nonnegative engineering numerator",
        ));
    }
    let numerator = numerator
        .parse()
        .map_err(|_| Error::limit("engineering numerator exceeds i128"))?;
    let denominator_bits = u32::try_from(epsilon.field("denominator_bits")?.number()?)
        .map_err(|_| Error::limit("engineering denominator exponent exceeds u32"))?;
    let epsilon = DyadicBound::new(numerator, denominator_bits)?;
    let expected_artifact = value.field("expected_artifact")?.text()?;
    if expected_artifact.is_empty() || expected_artifact.len() > MAX_FILE_BYTES {
        return Err(Error::limit(
            "engineering ideal artifact must contain 1..16777216 bytes",
        ));
    }
    Ok((
        EngineeringPureRequest::new(
            actual_boundary,
            actual_meaning,
            ideal_boundary,
            ideal_meaning,
            epsilon,
        )?,
        expected_artifact.to_owned(),
    ))
}

#[cfg(test)]
mod tests;
