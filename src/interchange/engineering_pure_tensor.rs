//! Engineering composition for exactly two ordered pure tensor components.
//! Fresh original-body equations and component bounds do not issue exact
//! source, inverse/control, cleanup, target-realization or resource evidence.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0

mod runtime;

use std::path::{Path, PathBuf};
use std::sync::Arc;

use super::codec::Codec;
use super::engineering_pure::{DyadicBound, EngineeringPureRequest};
use super::json::{self, Value};
use super::native::Kernel;
use super::pure_leaf::PureBoundary;
use super::{Encoder, Error, Result, Version};
use crate::AcceptedProgram;
use crate::contract::exact::{Budget, Matrix};
use crate::contract::{BasisType, DEFAULT_EXACT_WORK};
use crate::ir::QuantumPort;

const FORMAT: &str = "qleisli.engineering-pure-tensor-request";
const CLAIM_KIND: &str = "engineering-pure-tensor-bound";
const METRIC: &str = "pure-euclidean-operator-norm-v1";
const CHECKER_PROFILE: &str = "tensor-additive-r8-pure-leaf-v1";
const TARGET_PROFILE: &str = "qirf-r8-pure-v1";
const COMPOSITION: &str = "ordered-tensor-two-v1";
const ERROR_CATEGORY: &str = "implementation-distance";
const MAX_FILE_BYTES: usize = 16 << 20;

/// Original parent equations, two ordered component equations, and their
/// declared budgets. Construction checks data shape only. Native checking
/// establishes both parent tensor equations and exact addition of the budgets.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EngineeringPureTensorRequest {
    parent: EngineeringPureRequest,
    left: EngineeringPureRequest,
    right: EngineeringPureRequest,
}

impl EngineeringPureTensorRequest {
    pub fn new(
        parent: EngineeringPureRequest,
        left: EngineeringPureRequest,
        right: EngineeringPureRequest,
    ) -> Result<Self> {
        let domain = BasisType::Pair(
            Box::new(left.actual_boundary().domain().clone()),
            Box::new(right.actual_boundary().domain().clone()),
        );
        let codomain = BasisType::Pair(
            Box::new(left.actual_boundary().codomain().clone()),
            Box::new(right.actual_boundary().codomain().clone()),
        );
        if parent.actual_boundary().domain() != &domain
            || parent.actual_boundary().codomain() != &codomain
        {
            return Err(Error::format(
                "engineering tensor parent requires the exact ordered pair of component type trees",
            ));
        }
        Ok(Self {
            parent,
            left,
            right,
        })
    }

    pub fn parent(&self) -> &EngineeringPureRequest {
        &self.parent
    }

    pub fn left(&self) -> &EngineeringPureRequest {
        &self.left
    }

    pub fn right(&self) -> &EngineeringPureRequest {
        &self.right
    }
}

/// One immutable engineering invocation. Artifact order is parent actual,
/// parent ideal, left actual, left ideal, right actual, right ideal.
#[derive(Debug)]
struct Subject {
    programs: [AcceptedProgram; 6],
    request: EngineeringPureTensorRequest,
    request_bytes: Arc<[u8]>,
    checker: PathBuf,
}

#[derive(Debug)]
struct Decision {
    subject: Arc<Subject>,
    exact_work: usize,
}

/// A fresh private engineering result bound to all six original graphs and
/// all component/total budget data. Zero never promotes it to exact evidence.
///
/// ```compile_fail
/// use qleisli::{AcceptedProgram, interchange::engineering_pure_tensor::EngineeringPureTensorReport};
/// fn promote(report: EngineeringPureTensorReport) -> AcceptedProgram { report.into() }
/// ```
/// ```compile_fail
/// use qleisli::interchange::engineering_pure_tensor::EngineeringPureTensorReport;
/// fn deserialize_success() -> EngineeringPureTensorReport {
///     EngineeringPureTensorReport { exact_work: 0 }
/// }
/// ```
#[derive(Debug)]
pub struct EngineeringPureTensorReport {
    subject: Arc<Subject>,
    exact_work: usize,
}

impl EngineeringPureTensorReport {
    /// Original bytes in the fixed order parent actual/ideal, left
    /// actual/ideal, right actual/ideal; never a re-encoded graph.
    pub fn artifacts(&self) -> [&[u8]; 6] {
        self.subject
            .programs
            .each_ref()
            .map(AcceptedProgram::artifact)
    }

    pub fn request(&self) -> &EngineeringPureTensorRequest {
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
        programs: [&AcceptedProgram; 6],
        request: &EngineeringPureTensorRequest,
    ) -> Result<Arc<Self>> {
        let request_bytes = encode_request(request, programs.map(AcceptedProgram::artifact))?;
        Self::prepare_bytes(kernel, programs, request, request_bytes.into())
    }

    fn prepare_bytes(
        kernel: &Kernel,
        programs: [&AcceptedProgram; 6],
        request: &EngineeringPureTensorRequest,
        request_bytes: Arc<[u8]>,
    ) -> Result<Arc<Self>> {
        for bytes in programs
            .iter()
            .map(|program| program.artifact())
            .chain([request_bytes.as_ref()])
        {
            check_input(bytes)?;
        }
        let checker = std::fs::canonicalize(kernel.checker_path())
            .map_err(|e| Error::new("io", format!("cannot resolve Lean checker: {e}")))?;
        Ok(Arc::new(Self {
            programs: programs.map(Clone::clone),
            request: request.clone(),
            request_bytes,
            checker,
        }))
    }

    fn packet(&self) -> Result<Vec<u8>> {
        let actual = self.programs[0].artifact();
        let request = &self.request_bytes;
        let mut original = Vec::with_capacity(12 + actual.len() + request.len());
        original.extend_from_slice(b"QLV1");
        original.extend_from_slice(&(actual.len() as u32).to_le_bytes());
        original.extend_from_slice(&(request.len() as u32).to_le_bytes());
        original.extend_from_slice(actual);
        original.extend_from_slice(request);
        let graph = super::execution_view::finite::engineering_pure_tensor::complete(
            &self.request,
            self.programs.each_ref(),
        )?;
        let (packet, scope) = super::native_packet::encode(
            &original,
            Some(super::native_packet::View {
                graph: &graph,
                caller: None,
            }),
        )?;
        if scope != super::native_packet::Scope::Execution {
            return Err(Error::format("engineering tensor requires execution scope"));
        }
        Ok(packet)
    }

    fn bind(self: Arc<Self>, decision: Decision) -> Result<EngineeringPureTensorReport> {
        if !Arc::ptr_eq(&self, &decision.subject) {
            return Err(Error::new(
                "kernel",
                "engineering tensor decision belongs to a different subject",
            ));
        }
        Ok(EngineeringPureTensorReport {
            subject: self,
            exact_work: decision.exact_work,
        })
    }
}

/// Freshly check six original artifacts in fixed order parent actual/ideal,
/// left actual/ideal, right actual/ideal. The result consumes component bounds
/// through the ordered tensor rule; it does not repeat a parent Frobenius test.
pub fn check_with_kernel(
    kernel: &Kernel,
    programs: [&AcceptedProgram; 6],
    request: &EngineeringPureTensorRequest,
) -> Result<EngineeringPureTensorReport> {
    submit(Subject::prepare(kernel, programs, request)?)
}

fn submit(subject: Arc<Subject>) -> Result<EngineeringPureTensorReport> {
    let exact_work = runtime::check(&subject.checker, subject.packet()?)?;
    let decision = Decision {
        subject: Arc::clone(&subject),
        exact_work,
    };
    subject.bind(decision)
}

/// Decode a bounded untrusted request and ordinarily check all six originals
/// before independently checking the tensor engineering claim. The original
/// request bytes are retained unchanged, including insignificant whitespace.
pub fn check_serialized_with_kernel(
    kernel: &Kernel,
    actual_artifact: &[u8],
    request_bytes: &[u8],
) -> Result<EngineeringPureTensorReport> {
    check_input(actual_artifact)?;
    let (request, other_artifacts) = decode_request(request_bytes)?;
    let mut programs = Vec::with_capacity(6);
    programs.push(kernel.check(actual_artifact, None)?.into_program());
    for artifact in &other_artifacts {
        programs.push(kernel.check(artifact.as_bytes(), None)?.into_program());
    }
    let programs: [AcceptedProgram; 6] = programs
        .try_into()
        .map_err(|_| Error::format("engineering tensor requires exactly six original artifacts"))?;
    submit(Subject::prepare_bytes(
        kernel,
        programs.each_ref(),
        &request,
        Arc::from(request_bytes),
    )?)
}

/// Explicit environment selection, with no fallback or automatic download.
pub fn check(
    programs: [&AcceptedProgram; 6],
    request: &EngineeringPureTensorRequest,
) -> Result<EngineeringPureTensorReport> {
    check_with_kernel(&Kernel::selected()?, programs, request)
}

fn check_input(bytes: &[u8]) -> Result<()> {
    if bytes.is_empty() || bytes.len() > MAX_FILE_BYTES {
        return Err(Error::limit(
            "engineering tensor input must contain 1..16777216 bytes per file",
        ));
    }
    Ok(())
}

fn leaf(boundary: &PureBoundary, meaning: &Matrix, encoder: &mut Encoder) -> Result<Value> {
    Ok(Value::object([
        ("input", boundary.input().write(encoder)?),
        ("output", boundary.output().write(encoder)?),
        (
            "matrix",
            json::parse(&super::finite_matrix::encode(meaning)?)?,
        ),
    ]))
}

fn dyadic(bound: DyadicBound) -> Value {
    Value::object([
        ("numerator", Value::String(bound.numerator().to_string())),
        (
            "denominator_bits",
            Value::Number(u64::from(bound.denominator_bits())),
        ),
    ])
}

fn encode_request(
    request: &EngineeringPureTensorRequest,
    artifacts: [&[u8]; 6],
) -> Result<Vec<u8>> {
    let text = |bytes: &[u8]| {
        check_input(bytes)?;
        std::str::from_utf8(bytes)
            .map(str::to_owned)
            .map_err(|_| Error::format("engineering tensor artifacts require UTF-8"))
    };
    let mut encoder = Encoder::new(Version::V2);
    let mut component = |request: &EngineeringPureRequest, actual: &[u8], ideal: &[u8]| {
        Ok::<_, Error>(Value::object([
            (
                "domain",
                request.actual_boundary().domain().write(&mut encoder)?,
            ),
            (
                "codomain",
                request.actual_boundary().codomain().write(&mut encoder)?,
            ),
            (
                "actual",
                leaf(
                    request.actual_boundary(),
                    request.actual_meaning(),
                    &mut encoder,
                )?,
            ),
            (
                "ideal",
                leaf(
                    request.ideal_boundary(),
                    request.ideal_meaning(),
                    &mut encoder,
                )?,
            ),
            ("epsilon", dyadic(request.epsilon())),
            ("actual_artifact", Value::String(text(actual)?)),
            ("expected_artifact", Value::String(text(ideal)?)),
        ]))
    };
    let left = component(request.left(), artifacts[2], artifacts[3])?;
    let right = component(request.right(), artifacts[4], artifacts[5])?;
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
            "actual",
            leaf(
                request.parent().actual_boundary(),
                request.parent().actual_meaning(),
                &mut encoder,
            )?,
        ),
        (
            "ideal",
            leaf(
                request.parent().ideal_boundary(),
                request.parent().ideal_meaning(),
                &mut encoder,
            )?,
        ),
        ("epsilon", dyadic(request.parent().epsilon())),
        ("left", left),
        ("right", right),
        ("expected_artifact", Value::String(text(artifacts[1])?)),
    ]))
}

fn decode_dyadic(value: &Value) -> Result<DyadicBound> {
    value.fields(&["numerator", "denominator_bits"])?;
    let numerator = value.field("numerator")?.text()?;
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
    let denominator_bits = u32::try_from(value.field("denominator_bits")?.number()?)
        .map_err(|_| Error::limit("engineering denominator exponent exceeds u32"))?;
    DyadicBound::new(numerator, denominator_bits)
}

fn decode_pair(
    value: &Value,
    domain: BasisType,
    codomain: BasisType,
    budget: &mut Budget,
) -> Result<EngineeringPureRequest> {
    let decoder = super::Decoder { evidence: &[] };
    let mut leaf = |name: &str| -> Result<(PureBoundary, Matrix)> {
        let value = value.field(name)?;
        value.fields(&["input", "output", "matrix"])?;
        let boundary = PureBoundary::new(
            domain.clone(),
            codomain.clone(),
            QuantumPort::read(value.field("input")?, &decoder)?,
            QuantumPort::read(value.field("output")?, &decoder)?,
        )?;
        let matrix = super::finite_matrix::decode(&json::encode(value.field("matrix")?)?, budget)?;
        Ok((boundary, matrix))
    };
    let (actual_boundary, actual_meaning) = leaf("actual")?;
    let (ideal_boundary, ideal_meaning) = leaf("ideal")?;
    EngineeringPureRequest::new(
        actual_boundary,
        actual_meaning,
        ideal_boundary,
        ideal_meaning,
        decode_dyadic(value.field("epsilon")?)?,
    )
}

fn decode_request(bytes: &[u8]) -> Result<(EngineeringPureTensorRequest, [String; 5])> {
    check_input(bytes)?;
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
        "actual",
        "ideal",
        "epsilon",
        "left",
        "right",
        "expected_artifact",
    ])?;
    if value.field("version")?.number()? != 1 {
        return Err(Error::format("unknown engineering tensor request version"));
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
                "unknown engineering tensor request {field}"
            )));
        }
    }
    let decoder = super::Decoder { evidence: &[] };
    let mut budget = Budget::new(DEFAULT_EXACT_WORK);
    let mut component = |name| {
        let component = value.field(name)?;
        component.fields(&[
            "domain",
            "codomain",
            "actual",
            "ideal",
            "epsilon",
            "actual_artifact",
            "expected_artifact",
        ])?;
        let domain = BasisType::read(component.field("domain")?, &decoder)?;
        let codomain = BasisType::read(component.field("codomain")?, &decoder)?;
        decode_pair(component, domain, codomain, &mut budget)
    };
    let left = component("left")?;
    let right = component("right")?;
    let domain = BasisType::Pair(
        Box::new(left.actual_boundary().domain().clone()),
        Box::new(right.actual_boundary().domain().clone()),
    );
    let codomain = BasisType::Pair(
        Box::new(left.actual_boundary().codomain().clone()),
        Box::new(right.actual_boundary().codomain().clone()),
    );
    let parent = decode_pair(&value, domain, codomain, &mut budget)?;
    let mut artifacts = Vec::with_capacity(5);
    for artifact in [
        value.field("expected_artifact")?,
        value.field("left")?.field("actual_artifact")?,
        value.field("left")?.field("expected_artifact")?,
        value.field("right")?.field("actual_artifact")?,
        value.field("right")?.field("expected_artifact")?,
    ] {
        let artifact = artifact.text()?;
        check_input(artifact.as_bytes())?;
        artifacts.push(artifact.to_owned());
    }
    Ok((
        EngineeringPureTensorRequest::new(parent, left, right)?,
        artifacts
            .try_into()
            .map_err(|_| Error::format("expected five embedded artifacts"))?,
    ))
}

#[cfg(test)]
mod tests;
