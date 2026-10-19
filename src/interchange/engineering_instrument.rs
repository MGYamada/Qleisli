//! Engineering bounds for complete observing instruments and finite references.
//! This protocol cannot issue exact equation, control, cleanup, source, target
//! realization or resource evidence, including when its budget is zero.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0

mod runtime;

use std::path::{Path, PathBuf};
use std::sync::Arc;

use super::codec::Codec;
use super::engineering_pure::DyadicBound;
use super::json::{self, Value};
use super::native::Kernel;
use super::{Encoder, Error, Result, Version};
use crate::AcceptedProgram;
use crate::contract::exact::Budget;
use crate::contract::function::{RetainedIdentity, validate_identity};
use crate::contract::{
    BasisType, DEFAULT_EXACT_WORK, FunctionIdentity, InstrumentResult, InstrumentSignature,
};

const FORMAT: &str = "qleisli.engineering-instrument-request";
const CLAIM_KIND: &str = "engineering-instrument-bound";
const METRIC: &str = "complete-adjoint-euclidean-operator-norm-v1";
const CHECKER_PROFILE: &str = "choi-l1-r8-instrument-v1";
const TARGET_PROFILE: &str = "qirf-r8-instrument-v1";
const COMPOSITION: &str = "single-component-v1";
const ERROR_CATEGORY: &str = "implementation-distance";
const MAX_FILE_BYTES: usize = 16 << 20;

/// Two complete requested signatures, original identity data and an unsquared
/// bound with coefficient majorants. Construction validates data only. Public
/// labels and matrices are freshly derived by Lean from the original bodies.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EngineeringInstrumentRequest {
    actual_signature: InstrumentSignature,
    expected_signature: InstrumentSignature,
    identity: FunctionIdentity,
    epsilon: DyadicBound,
    majorants: Vec<DyadicBound>,
}

impl EngineeringInstrumentRequest {
    pub fn new(
        actual_signature: InstrumentSignature,
        expected_signature: InstrumentSignature,
        identity: FunctionIdentity,
        epsilon: DyadicBound,
        majorants: Vec<DyadicBound>,
    ) -> Result<Self> {
        if actual_signature != expected_signature {
            return Err(Error::format(
                "engineering instrument comparison requires identical full signature trees",
            ));
        }
        let mut budget = Budget::new(DEFAULT_EXACT_WORK);
        actual_signature
            .inner()
            .validate(&mut budget)
            .map_err(super::contract_error)?;
        expected_signature
            .inner()
            .validate(&mut budget)
            .map_err(super::contract_error)?;
        let retained_identity = RetainedIdentity::Owned(identity);
        validate_identity(&retained_identity, &mut budget).map_err(super::contract_error)?;
        let RetainedIdentity::Owned(identity) = retained_identity else {
            unreachable!()
        };
        // Every successful one-cell checker necessarily spends at least 256
        // work units. This existing work cap bounds copies before serialization.
        if majorants.len() > DEFAULT_EXACT_WORK / 256 {
            return Err(Error::limit(
                "instrument witnesses exceed the shared work capacity",
            ));
        }
        Ok(Self {
            actual_signature,
            expected_signature,
            identity,
            epsilon,
            majorants,
        })
    }

    pub fn actual_signature(&self) -> &InstrumentSignature {
        &self.actual_signature
    }
    pub fn expected_signature(&self) -> &InstrumentSignature {
        &self.expected_signature
    }
    pub fn identity(&self) -> &FunctionIdentity {
        &self.identity
    }
    pub fn epsilon(&self) -> DyadicBound {
        self.epsilon
    }
    pub fn majorants(&self) -> &[DyadicBound] {
        &self.majorants
    }
}

#[derive(Debug)]
struct Subject {
    edition: crate::edition::Edition,
    actual: AcceptedProgram,
    ideal: AcceptedProgram,
    request: EngineeringInstrumentRequest,
    request_bytes: Arc<[u8]>,
    checker: PathBuf,
}

#[derive(Debug)]
struct Decision {
    context: super::native_context::CheckedContext,
    subject: Arc<Subject>,
    exact_work: usize,
}

/// A fresh engineering-only decision bound to both immutable original graphs.
/// It has no deserializer or conversion into exact acceptance or capabilities.
///
/// ```compile_fail
/// use qleisli::{AcceptedProgram, interchange::engineering_instrument::EngineeringInstrumentReport};
/// fn promote(report: EngineeringInstrumentReport) -> AcceptedProgram { report.into() }
/// ```
/// ```compile_fail
/// use qleisli::{contract::FunctionEvidence, interchange::engineering_instrument::EngineeringInstrumentReport};
/// fn promote(report: EngineeringInstrumentReport) -> FunctionEvidence { report.into() }
/// ```
/// ```compile_fail
/// use qleisli::interchange::engineering_instrument::EngineeringInstrumentReport;
/// fn deserialize_success() -> EngineeringInstrumentReport {
///     EngineeringInstrumentReport { exact_work: 0 }
/// }
/// ```
#[derive(Debug)]
pub struct EngineeringInstrumentReport {
    context: super::native_context::CheckedContext,
    subject: Arc<Subject>,
    exact_work: usize,
}

impl EngineeringInstrumentReport {
    pub fn edition(&self) -> crate::edition::Edition {
        self.context.edition()
    }
    pub fn actual_artifact(&self) -> &[u8] {
        self.subject.actual.artifact()
    }
    pub fn ideal_artifact(&self) -> &[u8] {
        self.subject.ideal.artifact()
    }
    pub fn request(&self) -> &EngineeringInstrumentRequest {
        &self.subject.request
    }
    pub fn request_bytes(&self) -> &[u8] {
        &self.subject.request_bytes
    }
    pub fn exact_work(&self) -> usize {
        self.exact_work
    }
    /// Canonical selected path, without binary attestation.
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
    /// An IR profile, not a physical target or realizability claim.
    pub fn target_profile(&self) -> &'static str {
        TARGET_PROFILE
    }
    pub fn instrument_bound_verified(&self) -> bool {
        true
    }
}

impl Subject {
    fn prepare(
        kernel: &Kernel,
        actual: &AcceptedProgram,
        ideal: &AcceptedProgram,
        request: &EngineeringInstrumentRequest,
    ) -> Result<Arc<Self>> {
        let bytes = encode_request(request, ideal.artifact())?;
        Self::prepare_bytes(kernel, actual, ideal, request, bytes.into())
    }

    fn prepare_bytes(
        kernel: &Kernel,
        actual: &AcceptedProgram,
        ideal: &AcceptedProgram,
        request: &EngineeringInstrumentRequest,
        request_bytes: Arc<[u8]>,
    ) -> Result<Arc<Self>> {
        for bytes in [actual.artifact(), ideal.artifact(), &request_bytes] {
            if bytes.is_empty() || bytes.len() > MAX_FILE_BYTES {
                return Err(Error::limit(
                    "engineering input must contain 1..16777216 bytes per file",
                ));
            }
        }
        if [actual, ideal]
            .iter()
            .any(|p| p.edition() != kernel.edition())
        {
            return Err(Error::new(
                "edition",
                "engineering inputs belong to a different edition",
            ));
        }
        let checker = std::fs::canonicalize(kernel.checker_path())
            .map_err(|e| Error::new("io", format!("cannot resolve Lean checker: {e}")))?;
        Ok(Arc::new(Self {
            edition: kernel.edition(),
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
        let graph = super::execution_view::finite::engineering_instrument::complete(
            &self.request,
            &self.actual,
            &self.ideal,
        )?;
        let (packet, scope) = super::native_packet::encode(
            self.edition,
            &original,
            Some(super::native_packet::View {
                graph: &graph,
                caller: None,
            }),
        )?;
        if scope != super::native_packet::Scope::Execution {
            return Err(Error::format(
                "engineering instruments require an execution comparison",
            ));
        }
        Ok(packet)
    }

    fn bind(self: Arc<Self>, decision: Decision) -> Result<EngineeringInstrumentReport> {
        if !Arc::ptr_eq(&self, &decision.subject) || decision.context.edition() != self.edition {
            return Err(Error::new(
                "kernel",
                "engineering instrument decision belongs to a different subject",
            ));
        }
        Ok(EngineeringInstrumentReport {
            context: decision.context,
            subject: self,
            exact_work: decision.exact_work,
        })
    }
}

/// Freshly reconstruct both original bodies and check their complete instrument
/// difference. Independent exact acceptance still concerns each body's meaning.
pub fn check_with_kernel(
    kernel: &Kernel,
    actual: &AcceptedProgram,
    ideal: &AcceptedProgram,
    request: &EngineeringInstrumentRequest,
) -> Result<EngineeringInstrumentReport> {
    submit(Subject::prepare(kernel, actual, ideal, request)?)
}

fn submit(subject: Arc<Subject>) -> Result<EngineeringInstrumentReport> {
    let native = runtime::check(&subject.checker, subject.packet()?, subject.edition)?;
    let decision = Decision {
        subject: Arc::clone(&subject),
        exact_work: native.exact_work,
        context: native.context,
    };
    subject.bind(decision)
}

/// Strictly decode untrusted request data, freshly check both original graphs,
/// then submit their independently walked typed views. Retain original bytes.
pub fn check_serialized_with_kernel(
    kernel: &Kernel,
    actual_artifact: &[u8],
    request_bytes: &[u8],
) -> Result<EngineeringInstrumentReport> {
    if actual_artifact.is_empty() || actual_artifact.len() > MAX_FILE_BYTES {
        return Err(Error::limit(
            "engineering actual artifact must contain 1..16777216 bytes",
        ));
    }
    let (request, expected) = decode_request(request_bytes)?;
    let actual = kernel.check(actual_artifact, None)?.into_program();
    let ideal = kernel.check(expected.as_bytes(), None)?.into_program();
    submit(Subject::prepare_bytes(
        kernel,
        &actual,
        &ideal,
        &request,
        Arc::from(request_bytes),
    )?)
}

/// Explicit environment selection, without fallback or download.
pub fn check(
    actual: &AcceptedProgram,
    ideal: &AcceptedProgram,
    request: &EngineeringInstrumentRequest,
) -> Result<EngineeringInstrumentReport> {
    check_with_kernel(&Kernel::selected(actual.edition())?, actual, ideal, request)
}

fn dyadic_value(value: DyadicBound) -> Value {
    Value::object([
        ("numerator", Value::String(value.numerator().to_string())),
        (
            "denominator_bits",
            Value::Number(u64::from(value.denominator_bits())),
        ),
    ])
}

pub(super) fn encode_request(
    request: &EngineeringInstrumentRequest,
    expected: &[u8],
) -> Result<Vec<u8>> {
    let expected = std::str::from_utf8(expected)
        .map_err(|_| Error::format("engineering ideal artifact requires UTF-8"))?;
    let mut encoder = Encoder::new(Version::V2);
    let identity = request.identity();
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
            "actual_signature",
            super::native::instrument_signature(request.actual_signature.inner(), &mut encoder)?,
        ),
        (
            "expected_signature",
            super::native::instrument_signature(request.expected_signature.inner(), &mut encoder)?,
        ),
        (
            "identity",
            Value::object([
                (
                    "implementation",
                    Value::String(identity.implementation.clone()),
                ),
                (
                    "specification",
                    Value::String(identity.specification.clone()),
                ),
                (
                    "sources",
                    Value::Array(
                        identity
                            .sources
                            .iter()
                            .map(|(path, text)| {
                                Value::object([
                                    ("path", Value::String(path.clone())),
                                    ("text", Value::String(text.clone())),
                                ])
                            })
                            .collect(),
                    ),
                ),
            ]),
        ),
        ("epsilon", dyadic_value(request.epsilon)),
        (
            "majorants",
            Value::Array(
                request
                    .majorants
                    .iter()
                    .copied()
                    .map(dyadic_value)
                    .collect(),
            ),
        ),
        ("expected_artifact", Value::String(expected.into())),
    ]))
}

fn dyadic(value: &Value) -> Result<DyadicBound> {
    value.fields(&["numerator", "denominator_bits"])?;
    let numerator = value.field("numerator")?.text()?;
    if numerator.is_empty()
        || numerator.len() > 39
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
    let exponent = u32::try_from(value.field("denominator_bits")?.number()?)
        .map_err(|_| Error::limit("engineering denominator exponent exceeds u32"))?;
    DyadicBound::new(numerator, exponent)
}

fn signature(value: &Value) -> Result<InstrumentSignature> {
    value.fields(&["input", "result"])?;
    let decoder = super::Decoder { evidence: &[] };
    let input = BasisType::read(value.field("input")?, &decoder)?;
    let mut result = Vec::new();
    let mut pending = vec![(value.field("result")?, 1usize)];
    while let Some((value, depth)) = pending.pop() {
        if depth > 64 || result.len() + pending.len() >= 4096 {
            return Err(Error::limit(
                "instrument result exceeds 4096 nodes or depth 64",
            ));
        }
        let atom = match value.field("tag")?.text()? {
            "unit" => {
                value.fields(&["tag"])?;
                InstrumentResult::Unit
            }
            "bit" => {
                value.fields(&["tag"])?;
                InstrumentResult::Bit
            }
            "bits" => {
                value.fields(&["tag", "width"])?;
                InstrumentResult::Bits(
                    u32::try_from(value.field("width")?.number()?)
                        .map_err(|_| Error::limit("instrument width exceeds u32"))?,
                )
            }
            "quantum" => {
                value.fields(&["tag", "basis"])?;
                InstrumentResult::Quantum(BasisType::read(value.field("basis")?, &decoder)?)
            }
            "pair" => {
                value.fields(&["tag", "left", "right"])?;
                if result.len() + pending.len() + 3 > 4096 {
                    return Err(Error::limit("instrument result exceeds 4096 nodes"));
                }
                pending.extend([
                    (value.field("right")?, depth + 1),
                    (value.field("left")?, depth + 1),
                ]);
                InstrumentResult::Pair
            }
            "tuple" => {
                value.fields(&["tag", "fields"])?;
                let children = value.field("fields")?.array()?;
                if children.len() < 3
                    || children.len() > 4095
                    || result.len() + pending.len() + 1 + children.len() > 4096
                {
                    return Err(Error::limit("instrument tuple exceeds result capacity"));
                }
                pending.extend(children.iter().rev().map(|child| (child, depth + 1)));
                InstrumentResult::Tuple(children.len())
            }
            _ => return Err(Error::format("unknown instrument result")),
        };
        result.push(atom);
    }
    InstrumentSignature::new(input, result).map_err(super::contract_error)
}

pub(super) fn decode_request(bytes: &[u8]) -> Result<(EngineeringInstrumentRequest, String)> {
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
        "actual_signature",
        "expected_signature",
        "identity",
        "epsilon",
        "majorants",
        "expected_artifact",
    ])?;
    if value.field("version")?.number()? != 1 {
        return Err(Error::format(
            "unknown engineering instrument request version",
        ));
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
    let actual = signature(value.field("actual_signature")?)?;
    let expected = signature(value.field("expected_signature")?)?;
    let identity = value.field("identity")?;
    identity.fields(&["implementation", "specification", "sources"])?;
    let sources = identity.field("sources")?.array()?;
    if sources.len() > crate::contract::function::MAX_FUNCTION_SOURCES {
        return Err(Error::limit("instrument source count exceeds 128"));
    }
    let identity = FunctionIdentity {
        implementation: identity.field("implementation")?.text()?.into(),
        specification: identity.field("specification")?.text()?.into(),
        sources: sources
            .iter()
            .map(|source| {
                source.fields(&["path", "text"])?;
                Ok((
                    source.field("path")?.text()?.into(),
                    source.field("text")?.text()?.into(),
                ))
            })
            .collect::<Result<_>>()?,
    };
    let majorants = value.field("majorants")?.array()?;
    if majorants.len() > DEFAULT_EXACT_WORK / 256 {
        return Err(Error::limit(
            "instrument witnesses exceed the shared work capacity",
        ));
    }
    let majorants = majorants.iter().map(dyadic).collect::<Result<_>>()?;
    let epsilon = dyadic(value.field("epsilon")?)?;
    let expected_artifact = value.field("expected_artifact")?.text()?;
    if expected_artifact.is_empty() || expected_artifact.len() > MAX_FILE_BYTES {
        return Err(Error::limit(
            "engineering ideal artifact must contain 1..16777216 bytes",
        ));
    }
    Ok((
        EngineeringInstrumentRequest::new(actual, expected, identity, epsilon, majorants)?,
        expected_artifact.into(),
    ))
}

#[cfg(test)]
mod tests;
