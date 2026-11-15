//! Engineering comparison of literal canonical OpenQASM target bytes with an
//! independent original ideal instrument. This is a closed terminal profile,
//! not an open pure operation or a source/export-preservation certificate.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0

mod runtime;
mod target;

use std::path::{Path, PathBuf};
use std::sync::Arc;

use super::engineering_instrument::{self, EngineeringInstrumentRequest};
use super::json::{self, Value};
use super::native::Kernel;
use super::{Error, Result};
use crate::AcceptedProgram;
use crate::contract::{BasisType, InstrumentResult};

const FORMAT: &str = "qleisli.engineering-openqasm-request";
const CLAIM_KIND: &str = "engineering-target-instrument-bound";
const RESOURCE_CLAIM_KIND: &str = "engineering-target-instrument-resource-bound";
pub const RESOURCE_MODEL: &str = "openqasm3-one-qubit-literal-gates-v1";
const METRIC: &str = "complete-adjoint-euclidean-operator-norm-v1";
const CHECKER_PROFILE: &str = "canonical-target-choi-l1-r8-v1";
const TARGET_PROFILE: &str = "openqasm3-canonical-one-qubit-terminal-r8-v1";
const COMPOSITION: &str = "single-component-v1";
const ERROR_CATEGORY: &str = "implementation-distance";
const MAX_FILE_BYTES: usize = 16 << 20;

/// Total literal gate lines and the T/TDG subset in the one-qubit terminal model.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct GateCounts {
    pub gates: usize,
    pub t_gates: usize,
}

/// Closed request data, with the exact Unit input owner and one classical Bit
/// result. The underlying instrument signature, identity and dyadic witnesses
/// are data, not a semantic receipt or an assertion of source correspondence.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EngineeringOpenQasmRequest {
    contract: EngineeringInstrumentRequest,
    resource_limits: Option<GateCounts>,
}

impl EngineeringOpenQasmRequest {
    pub fn new(contract: EngineeringInstrumentRequest) -> Result<Self> {
        for signature in [contract.actual_signature(), contract.expected_signature()] {
            if signature.input() != &BasisType::Unit
                || signature.result() != [InstrumentResult::Bit]
            {
                return Err(Error::format(
                    "canonical OpenQASM engineering requires exactly Unit -> classical Bit signatures",
                ));
            }
        }
        Ok(Self {
            contract,
            resource_limits: None,
        })
    }

    pub fn contract(&self) -> &EngineeringInstrumentRequest {
        &self.contract
    }

    /// Require Lean to check finite gate limits on the same decoded target.
    pub fn with_resource_limits(mut self, limits: GateCounts) -> Result<Self> {
        if limits.gates > target::MAX_TARGET_GATES || limits.t_gates > target::MAX_TARGET_GATES {
            return Err(Error::limit(
                "OpenQASM resource limits must be at most eight",
            ));
        }
        self.resource_limits = Some(limits);
        Ok(self)
    }

    pub fn resource_limits(&self) -> Option<GateCounts> {
        self.resource_limits
    }

    pub(crate) fn claim_kind(&self) -> &'static str {
        if self.resource_limits.is_some() {
            RESOURCE_CLAIM_KIND
        } else {
            CLAIM_KIND
        }
    }
}

#[derive(Debug)]
struct Subject {
    edition: crate::edition::Edition,
    actual: target::Decoded,
    ideal: AcceptedProgram,
    request: EngineeringOpenQasmRequest,
    request_bytes: Arc<[u8]>,
    checker: PathBuf,
}

#[derive(Debug)]
struct Decision {
    context: super::native_context::CheckedContext,
    subject: Arc<Subject>,
    exact_work: usize,
}

/// A fresh allocation-bound engineering decision over the literal target
/// bytes and original ideal. It cannot issue exact acceptance or capabilities,
/// including when the engineering budget is zero.
///
/// ```compile_fail
/// use qleisli::{AcceptedProgram, interchange::engineering_openqasm::EngineeringOpenQasmReport};
/// fn promote(report: EngineeringOpenQasmReport) -> AcceptedProgram { report.into() }
/// ```
/// ```compile_fail
/// use qleisli::{contract::FunctionEvidence, interchange::engineering_openqasm::EngineeringOpenQasmReport};
/// fn promote(report: EngineeringOpenQasmReport) -> FunctionEvidence { report.into() }
/// ```
/// ```compile_fail
/// use qleisli::interchange::engineering_openqasm::EngineeringOpenQasmReport;
/// fn deserialize_success() -> EngineeringOpenQasmReport { EngineeringOpenQasmReport { exact_work: 0 } }
/// ```
#[derive(Debug)]
pub struct EngineeringOpenQasmReport {
    context: super::native_context::CheckedContext,
    subject: Arc<Subject>,
    exact_work: usize,
}

impl EngineeringOpenQasmReport {
    pub fn edition(&self) -> crate::edition::Edition {
        self.context.edition()
    }
    pub fn target_bytes(&self) -> &[u8] {
        self.subject.actual.original()
    }
    pub fn ideal_artifact(&self) -> &[u8] {
        self.subject.ideal.artifact()
    }
    pub fn request(&self) -> &EngineeringOpenQasmRequest {
        &self.subject.request
    }
    pub fn request_bytes(&self) -> &[u8] {
        &self.subject.request_bytes
    }
    pub fn gate_word(&self) -> impl ExactSizeIterator<Item = &'static str> + '_ {
        self.subject.actual.gate_word()
    }
    pub fn exact_work(&self) -> usize {
        self.exact_work
    }
    /// Canonical selected path, without native binary attestation.
    pub fn checker(&self) -> &Path {
        &self.subject.checker
    }
    pub fn metric(&self) -> &'static str {
        METRIC
    }
    pub fn claim_kind(&self) -> &'static str {
        self.request().claim_kind()
    }
    /// Count the retained literal word compared with Lean's independently
    /// decoded word. This receipt exists only when Lean also checked the limits.
    pub fn checked_gate_counts(&self) -> Option<GateCounts> {
        self.request().resource_limits().map(|_| GateCounts {
            gates: self.gate_word().len(),
            t_gates: self
                .gate_word()
                .filter(|gate| matches!(*gate, "t" | "tdg"))
                .count(),
        })
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
    pub fn target_profile(&self) -> &'static str {
        TARGET_PROFILE
    }
}

impl Subject {
    fn prepare(
        kernel: &Kernel,
        target: &[u8],
        ideal: &AcceptedProgram,
        request: &EngineeringOpenQasmRequest,
    ) -> Result<Arc<Self>> {
        let bytes = encode_request(request, ideal.artifact())?;
        Self::prepare_bytes(kernel, target, ideal, request, bytes.into())
    }

    fn prepare_bytes(
        kernel: &Kernel,
        target: &[u8],
        ideal: &AcceptedProgram,
        request: &EngineeringOpenQasmRequest,
        request_bytes: Arc<[u8]>,
    ) -> Result<Arc<Self>> {
        let actual = target::Decoded::new(target)?;
        for bytes in [ideal.artifact(), request_bytes.as_ref()] {
            check_input(bytes)?;
        }
        if ideal.edition() != kernel.edition() {
            return Err(Error::new(
                "edition",
                "engineering inputs belong to a different edition",
            ));
        }
        let checker = std::fs::canonicalize(kernel.checker_path())
            .map_err(|e| Error::new("io", format!("cannot resolve Lean checker: {e}")))?;
        Ok(Arc::new(Self {
            edition: kernel.edition(),
            actual,
            ideal: ideal.clone(),
            request: request.clone(),
            request_bytes,
            checker,
        }))
    }

    fn packet(&self) -> Result<Vec<u8>> {
        let actual = self.actual.original();
        let request = &self.request_bytes;
        let mut original = Vec::with_capacity(12 + actual.len() + request.len());
        original.extend_from_slice(b"QLV1");
        original.extend_from_slice(&(actual.len() as u32).to_le_bytes());
        original.extend_from_slice(&(request.len() as u32).to_le_bytes());
        original.extend_from_slice(actual);
        original.extend_from_slice(request);
        let word = self.actual.gate_word().collect::<Vec<_>>();
        let graph = super::execution_view::finite::engineering_openqasm::complete(
            &self.request,
            self.actual.original(),
            &word,
            self.actual.graph(),
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
                "OpenQASM engineering requires execution scope",
            ));
        }
        Ok(packet)
    }

    fn bind(self: Arc<Self>, decision: Decision) -> Result<EngineeringOpenQasmReport> {
        if !Arc::ptr_eq(&self, &decision.subject) || decision.context.edition() != self.edition {
            return Err(Error::new(
                "kernel",
                "OpenQASM engineering decision belongs to a different subject",
            ));
        }
        Ok(EngineeringOpenQasmReport {
            context: decision.context,
            subject: self,
            exact_work: decision.exact_work,
        })
    }
}

/// Independently decode the actual canonical target bytes, retain the host
/// data graph, and freshly compare it with Lean's own decoding and the original
/// ideal instrument. No host-generated graph receives acceptance authority.
pub fn check_with_kernel(
    kernel: &Kernel,
    target: &[u8],
    ideal: &AcceptedProgram,
    request: &EngineeringOpenQasmRequest,
) -> Result<EngineeringOpenQasmReport> {
    submit(Subject::prepare(kernel, target, ideal, request)?)
}

fn submit(subject: Arc<Subject>) -> Result<EngineeringOpenQasmReport> {
    let native = runtime::check(&subject.checker, subject.packet()?, subject.edition)?;
    let decision = Decision {
        subject: Arc::clone(&subject),
        exact_work: native.exact_work,
        context: native.context,
    };
    subject.bind(decision)
}

/// Decode an untrusted closed request, ordinarily check the original ideal,
/// then run a fresh target-bound engineering invocation. Original target and
/// request bytes are retained, without whitespace rewriting or success reuse.
pub fn check_serialized_with_kernel(
    kernel: &Kernel,
    target: &[u8],
    request_bytes: &[u8],
) -> Result<EngineeringOpenQasmReport> {
    target::Decoded::new(target)?;
    let (request, ideal) = decode_request(request_bytes)?;
    let ideal = kernel.check(ideal.as_bytes(), None)?.into_program();
    submit(Subject::prepare_bytes(
        kernel,
        target,
        &ideal,
        &request,
        Arc::from(request_bytes),
    )?)
}

/// Explicit environment selection without automatic download or fallback.
pub fn check(
    target: &[u8],
    ideal: &AcceptedProgram,
    request: &EngineeringOpenQasmRequest,
) -> Result<EngineeringOpenQasmReport> {
    check_with_kernel(&Kernel::selected(ideal.edition())?, target, ideal, request)
}

fn check_input(bytes: &[u8]) -> Result<()> {
    if bytes.is_empty() || bytes.len() > MAX_FILE_BYTES {
        return Err(Error::limit(
            "OpenQASM engineering request and ideal require 1..16777216 bytes",
        ));
    }
    Ok(())
}

const PROFILES: [(&str, &str, &str); 6] = [
    ("format", FORMAT, "qleisli.engineering-instrument-request"),
    (
        "metric",
        METRIC,
        "complete-adjoint-euclidean-operator-norm-v1",
    ),
    (
        "checker_profile",
        CHECKER_PROFILE,
        "choi-l1-r8-instrument-v1",
    ),
    ("target_profile", TARGET_PROFILE, "qirf-r8-instrument-v1"),
    ("composition", COMPOSITION, "single-component-v1"),
    ("error_category", ERROR_CATEGORY, "implementation-distance"),
];

fn encode_request(request: &EngineeringOpenQasmRequest, ideal: &[u8]) -> Result<Vec<u8>> {
    check_input(ideal)?;
    let bytes = engineering_instrument::encode_request(request.contract(), ideal)?;
    let mut value = json::parse(&bytes)?;
    let Value::Object(fields) = &mut value else {
        return Err(Error::format("expected engineering request object"));
    };
    for (name, profile, _) in PROFILES {
        fields.insert(name.into(), Value::String(profile.into()));
    }
    fields.insert(
        "claim_kind".into(),
        Value::String(request.claim_kind().into()),
    );
    if let Some(limits) = request.resource_limits() {
        fields.insert("version".into(), Value::Number(2));
        fields.insert(
            "resource_limits".into(),
            Value::object([
                ("model", Value::String(RESOURCE_MODEL.into())),
                ("gates", Value::Number(limits.gates as u64)),
                ("t_gates", Value::Number(limits.t_gates as u64)),
            ]),
        );
    }
    json::encode(&value)
}

fn decode_request(bytes: &[u8]) -> Result<(EngineeringOpenQasmRequest, String)> {
    check_input(bytes)?;
    let mut value = json::parse(bytes)?;
    for (name, profile, _) in PROFILES {
        if value.field(name)?.text()? != profile {
            return Err(Error::format(format!(
                "unknown OpenQASM engineering request {name}"
            )));
        }
    }
    let limits = match value.field("version")?.number()? {
        1 if value.field("claim_kind")?.text()? == CLAIM_KIND => None,
        2 if value.field("claim_kind")?.text()? == RESOURCE_CLAIM_KIND => {
            let limits = value.field("resource_limits")?;
            limits.fields(&["model", "gates", "t_gates"])?;
            if limits.field("model")?.text()? != RESOURCE_MODEL {
                return Err(Error::format("unknown OpenQASM engineering resource model"));
            }
            let count = |field| -> Result<usize> {
                let count = limits.field(field)?.number()?;
                usize::try_from(count)
                    .map_err(|_| Error::limit("OpenQASM resource limit out of range"))
            };
            Some(GateCounts {
                gates: count("gates")?,
                t_gates: count("t_gates")?,
            })
        }
        _ => {
            return Err(Error::format(
                "unknown OpenQASM engineering request version or claim",
            ));
        }
    };
    let Value::Object(fields) = &mut value else {
        return Err(Error::format("expected engineering request object"));
    };
    // This untrusted codec adapter changes only the already-checked fixed
    // profile names. The existing closed-field/signature/identity/dyadic
    // decoder still validates every request field; no semantic decision occurs.
    for (name, _, profile) in PROFILES {
        fields.insert(name.into(), Value::String(profile.into()));
    }
    fields.insert(
        "claim_kind".into(),
        Value::String("engineering-instrument-bound".into()),
    );
    if limits.is_some() {
        fields.insert("version".into(), Value::Number(1));
        fields.remove("resource_limits");
    }
    let (contract, ideal) = engineering_instrument::decode_request(&json::encode(&value)?)?;
    let request = EngineeringOpenQasmRequest::new(contract)?;
    Ok((
        match limits {
            Some(limits) => request.with_resource_limits(limits)?,
            None => request,
        },
        ideal,
    ))
}

#[cfg(test)]
mod tests;
