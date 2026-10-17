//! One native acceptance boundary for immutable QIRF proposals.
//! Lean compares Rust's retained decoded data before authorizing execution.
//! Rust issues no ownership, equation or isometry decision; walker coverage and
//! numerical runtime correspondence remain explicit assumptions.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0

mod binding;
mod reporting;
mod runtime;

pub(crate) use reporting::DecisionLog;
pub use reporting::NativeDecisionSummary;

use std::path::{Path, PathBuf};
use std::sync::Arc;

use super::{Encoder, Error, Imported, Result, RootInterface, Version};
use crate::ir::RawProgram;

/// Fresh native acceptance of immutable QIRF/request bytes. This report carries
/// no decoded execution view and cannot be deserialized from a success receipt.
/// Native compilation and transport remain explicit deployment assumptions.
#[derive(Clone, Debug)]
pub struct NativeChecked {
    subject: Arc<Subject>,
    exact_work: usize,
    scope: super::native_packet::Scope,
}

/// Immutable invocation inputs, without an acceptance decision. Construction
/// stays in this module; staged dependency caches retain this same allocation.
#[derive(Debug)]
pub(crate) struct Subject {
    artifact: Arc<[u8]>,
    request: Option<Arc<[u8]>>,
    checker: PathBuf,
    decisions: Option<DecisionLog>,
}

impl Subject {
    pub(crate) fn artifact(&self) -> &[u8] {
        &self.artifact
    }
    pub(crate) fn checker(&self) -> &Path {
        &self.checker
    }
}

impl NativeChecked {
    pub fn artifact(&self) -> &[u8] {
        self.subject.artifact()
    }
    pub fn request(&self) -> Option<&[u8]> {
        self.subject.request.as_deref()
    }
    pub fn exact_work(&self) -> usize {
        self.exact_work
    }
    /// Canonical path used for this invocation, not a binary attestation.
    pub fn checker(&self) -> &Path {
        self.subject.checker()
    }
}

/// Private pre-decision materialization. Neither this container nor any of its
/// cached dependency objects may escape before a fresh decision for `subject`.
/// Binding moves these exact allocations into the public accepted handle.
struct Prepared {
    subject: Arc<Subject>,
    decoded: Arc<super::DecodedGraph>,
    derived_effect: crate::ir::Effect,
    output_ports: Vec<crate::ir::QuantumPort>,
}

impl Prepared {
    fn new(subject: Arc<Subject>) -> Result<Self> {
        let mut budget = crate::contract::exact::Budget::new(crate::contract::DEFAULT_EXACT_WORK);
        let decoded = Arc::new(super::decode_subject(&subject, &mut budget)?);
        let (derived_effect, output_ports) = view::metadata(&decoded.programs[decoded.root])?;
        Ok(Self {
            subject,
            decoded,
            derived_effect,
            output_ports,
        })
    }

    fn bind(self, native: NativeChecked) -> Result<Checked> {
        if !Arc::ptr_eq(&self.subject, &native.subject) {
            return Err(Error::new(
                "kernel",
                "native decision belongs to a different subject",
            ));
        }
        if native.scope == super::native_packet::Scope::Inspection {
            return Err(Error::new(
                "kernel",
                "inspection does not authorize an execution view",
            ));
        }
        let root_interface = self.decoded.interface.clone();
        let imported = Imported {
            program: AcceptedProgram {
                native: Arc::new(native.clone()),
                decoded: self.decoded,
                interface: root_interface.clone(),
                derived_effect: self.derived_effect,
                output_ports: self.output_ports,
                source_instruments: Arc::from([]),
                source_instrument_calls: Arc::from([]),
                source_pure_equations: Arc::from([]),
                source_computed_normalizations: Arc::from([]),
            },
            root_interface,
            request_checked: native.request().is_some(),
            exact_work: native.exact_work,
        };
        Ok(Checked {
            artifact: Arc::clone(&native.subject.artifact),
            request: native.subject.request.clone(),
            imported,
            native_exact_work: native.exact_work,
        })
    }
}

/// An explicitly selected native checker; no PATH search or runtime download.
#[derive(Clone, Debug)]
pub struct Kernel {
    executable: PathBuf,
    decisions: Option<DecisionLog>,
}

/// Metadata for a fresh native decision and its decoded execution view.
/// This wrapper contains the same AcceptedProgram authority, never a second verifier.
#[derive(Debug)]
pub struct Checked {
    artifact: Arc<[u8]>,
    request: Option<Arc<[u8]>>,
    pub(super) imported: Imported,
    native_exact_work: usize,
}

impl Kernel {
    /// Selected path only; resolving it does not attest the native binary.
    pub(in crate::interchange) fn checker_path(&self) -> &Path {
        &self.executable
    }

    /// Explicit environment selection for convenience APIs. No PATH search,
    /// development-tree guess, automatic download or Rust fallback is used.
    pub fn selected() -> Result<Self> {
        let path = std::env::var_os("QLEISLI_KERNEL")
            .filter(|p| !p.is_empty())
            .ok_or_else(|| {
                Error::new(
                    "kernel",
                    "select the matching Lean checker with --lean-kernel=PATH or QLEISLI_KERNEL",
                )
            })?;
        Ok(Self::new(path))
    }

    pub fn new(executable: impl AsRef<Path>) -> Self {
        Self {
            executable: executable.as_ref().to_owned(),
            decisions: None,
        }
    }

    /// Observe fresh successful native decisions for one diagnostic operation.
    /// The observer carries no acceptance authority and does not pin a binary.
    pub(crate) fn recording(&self) -> (Self, DecisionLog) {
        let decisions = DecisionLog::new();
        (
            Self {
                executable: self.executable.clone(),
                decisions: Some(decisions.clone()),
            },
            decisions,
        )
    }

    /// The native checker must accept the same complete input. Any rejection,
    /// unsupported form, exhausted capacity or transport failure blocks use.
    /// A separate request is optional and checked independently by Lean.
    pub fn check(&self, artifact: &[u8], request: Option<&[u8]>) -> Result<Checked> {
        self.check_mode(artifact, request, "--qirf-native")
            .map_err(|mut failure| {
                // Diagnose only an already rejected artifact. The native code and
                // message remain authoritative, including for request-only failures.
                if matches!(failure.code, "format" | "invalid_ir")
                    && failure.message == runtime::REJECTION_MESSAGE
                {
                    if let Err(detail) = super::json::parse(artifact)
                        .and_then(|value| super::envelope(&value).map(|_| ()))
                    {
                        failure.json_pointer = detail.json_pointer;
                    }
                }
                failure
            })
    }

    fn check_mode(&self, artifact: &[u8], request: Option<&[u8]>, mode: &str) -> Result<Checked> {
        self.check_bound(artifact, request, mode, Prepared::description, None)
    }

    /// Verify manually built IR through the same original-QIRF boundary as
    /// imported IR. Serialization does not call the legacy verifier first.
    pub fn verify(&self, program: &RawProgram) -> Result<Checked> {
        self.check_raw(program, None, Version::V2, None)
    }

    /// Check an existing source/foreign/host result with a freshly reconstructed
    /// artifact. All nested evidence and both branch arms reach the kernel.
    pub fn check_program(&self, program: &AcceptedProgram) -> Result<Checked> {
        self.verify(program.raw())
    }

    /// Explicit QIRF version, type trees and independent request for raw callers.
    /// Returned bytes are exactly those accepted; no post-check reserialization.
    pub fn check_raw(
        &self,
        program: &RawProgram,
        interface: Option<&RootInterface>,
        version: Version,
        request: Option<&[u8]>,
    ) -> Result<Checked> {
        let (bytes, caller) = super::encode_caller(program, interface, Encoder::new(version))?;
        self.check_bound(
            &bytes,
            request,
            "--qirf-native",
            Prepared::description,
            Some(&caller),
        )
        .map_err(|mut failure| {
            // An explanation is optional and cannot reverse Lean's rejection.
            if failure.code == "contract" {
                if let Some((pointer, detail)) = rejected_contract_detail(program) {
                    failure.message.push_str(": ");
                    failure.message.push_str(&detail);
                    failure.json_pointer = pointer;
                }
            }
            failure
        })
    }

    /// Retain the caller's meaning entries while checking their complete graph.
    pub fn check_with_meanings(
        &self,
        program: &AcceptedProgram,
        interface: Option<&RootInterface>,
        meanings: &[crate::contract::meaning::MeaningEvidence],
        request: Option<&[u8]>,
    ) -> Result<Checked> {
        let mut encoder = Encoder::new(Version::V2);
        for meaning in meanings {
            encoder.meanings.insert(
                Arc::clone(meaning.receipt().snapshot_key()),
                meaning.target().clone(),
            );
        }
        let (bytes, caller) = super::encode_caller(program.raw(), interface, encoder)?;
        self.check_bound(
            &bytes,
            request,
            "--qirf-native",
            Prepared::description,
            Some(&caller),
        )
    }

    /// Check both original and converted artifacts against the same request.
    /// A target format that cannot represent a meaning entry rejects explicitly.
    pub fn convert(
        &self,
        artifact: &[u8],
        version: Version,
        request: Option<&[u8]>,
    ) -> Result<Checked> {
        let original = self.check(artifact, request)?;
        let converted = super::convert_proposal(original.artifact(), version)?;
        self.check(&converted, original.request())
    }

    /// Native-only inspection does not call Rust semantic acceptance. Execution views use `check`.
    pub fn inspect(&self, artifact: &[u8], request: Option<&[u8]>) -> Result<NativeChecked> {
        self.inspect_mode(artifact, request, "--qirf-native")
    }

    fn inspect_mode(
        &self,
        artifact: &[u8],
        request: Option<&[u8]>,
        mode: &str,
    ) -> Result<NativeChecked> {
        Self::inspect_subject(self.subject(artifact, request)?, mode)
    }

    fn subject(&self, artifact: &[u8], request: Option<&[u8]>) -> Result<Arc<Subject>> {
        if artifact.is_empty()
            || artifact.len() > 16 << 20
            || request.is_some_and(|r| r.is_empty() || r.len() > 16 << 20)
        {
            return Err(Error::limit(
                "native input must contain 1..16777216 bytes per file",
            ));
        }
        let checker = std::fs::canonicalize(&self.executable)
            .map_err(|e| Error::new("io", format!("cannot resolve Lean checker: {e}")))?;
        Ok(Arc::new(Subject {
            artifact: Arc::from(artifact),
            request: request.map(Arc::from),
            checker,
            decisions: self.decisions.clone(),
        }))
    }

    fn inspect_subject(subject: Arc<Subject>, mode: &str) -> Result<NativeChecked> {
        Self::submit_subject(subject, mode, None)
    }

    fn submit_subject(
        subject: Arc<Subject>,
        mode: &str,
        view: Option<super::native_packet::View<'_>>,
    ) -> Result<NativeChecked> {
        let artifact = &subject.artifact;
        let request = &subject.request;
        let mut packet =
            Vec::with_capacity(12 + artifact.len() + request.as_ref().map_or(0, |r| r.len()));
        packet.extend_from_slice(b"QLV1");
        packet.extend_from_slice(&(artifact.len() as u32).to_le_bytes());
        packet.extend_from_slice(&(request.as_ref().map_or(0, |r| r.len()) as u32).to_le_bytes());
        packet.extend_from_slice(artifact);
        if let Some(request) = request {
            packet.extend_from_slice(request);
        }
        let (packet, scope) = super::native_packet::encode(&packet, view)?;
        let native_exact_work =
            runtime::check_mode(subject.checker(), packet, request.is_some(), mode, scope)?;
        if let Some(decisions) = &subject.decisions {
            decisions.record(subject.checker(), mode, request.is_some(), scope);
        }
        Ok(NativeChecked {
            subject,
            exact_work: native_exact_work,
            scope,
        })
    }
}

impl Checked {
    pub fn artifact(&self) -> &[u8] {
        &self.artifact
    }
    pub fn request(&self) -> Option<&[u8]> {
        self.request.as_deref()
    }
    pub fn imported(&self) -> &Imported {
        &self.imported
    }
    pub fn program(&self) -> &AcceptedProgram {
        &self.imported.program
    }
    pub fn native_exact_work(&self) -> usize {
        self.native_exact_work
    }
    /// Consume the report, retaining the exact reconstructed executable body.
    pub fn into_program(self) -> AcceptedProgram {
        self.imported.program
    }
}

mod contracts;
pub(in crate::interchange) use contracts::instrument_signature;
mod view;

/// Immutable untrusted bytes. Constructing or serializing a proposal grants no authority.
#[derive(Clone, Debug)]
pub struct Proposal {
    artifact: Arc<[u8]>,
    request: Option<Arc<[u8]>>,
}
impl Proposal {
    pub fn new(artifact: &[u8], request: Option<&[u8]>) -> Result<Self> {
        if artifact.is_empty()
            || artifact.len() > 16 << 20
            || request.is_some_and(|r| r.is_empty() || r.len() > 16 << 20)
        {
            return Err(Error::limit(
                "proposal files must contain 1..16777216 bytes",
            ));
        }
        Ok(Self {
            artifact: Arc::from(artifact),
            request: request.map(Arc::from),
        })
    }
    pub fn from_raw(
        program: &RawProgram,
        interface: Option<&RootInterface>,
        version: Version,
        request: Option<&[u8]>,
    ) -> Result<Self> {
        Self::new(
            &super::encode_proposal(program, interface, Encoder::new(version))?,
            request,
        )
    }
    pub fn artifact(&self) -> &[u8] {
        &self.artifact
    }
    pub fn request(&self) -> Option<&[u8]> {
        self.request.as_deref()
    }
}

/// An immutable execution view authorized only by a fresh Lean decision.
///
/// ```compile_fail
/// use qleisli::interchange::native::{AcceptedProgram, Proposal};
/// fn bypass(proposal: Proposal) -> AcceptedProgram { proposal.into() }
/// ```
#[derive(Clone, Debug)]
pub struct AcceptedProgram {
    native: Arc<NativeChecked>,
    // Retain the complete actual graph for #362's native comparison. Execution
    // reads the root Arc in this graph; it is never decoded again to run.
    decoded: Arc<super::DecodedGraph>,
    interface: Option<RootInterface>,
    derived_effect: crate::ir::Effect,
    output_ports: Vec<crate::ir::QuantumPort>,
    // Inert retention for a future source-to-artifact replay/audit consumer
    // (#356): no current replay, execution or export path reads these two fields.
    // Equations are checked before attachment; retention grants no authority,
    // adds no whole-root request and does not prove source preservation.
    source_instruments: Arc<[Arc<crate::contract::instrument::InstrumentEvidence>]>,
    source_instrument_calls: Arc<[crate::contract::instrument::InstrumentCall]>,
    // Separate source-associated pure equations, exposed by the getter below
    // and inspected by the rectangular Meaning regressions.
    source_pure_equations: Arc<[Arc<super::pure_leaf::SourcePureEquation>]>,
    // Inert exact equations for the actual local ancilla fragments normalized
    // to protected diagonal use. Native decisions precede attachment; this is
    // neither execution input nor a whole-source preservation certificate.
    source_computed_normalizations: Arc<[Arc<super::finite_leaf::SourceUnitaryEquation>]>,
}
impl AcceptedProgram {
    pub fn artifact(&self) -> &[u8] {
        self.native.artifact()
    }
    pub fn request(&self) -> Option<&[u8]> {
        self.native.request()
    }
    pub fn raw(&self) -> &RawProgram {
        &self.decoded.programs[self.decoded.root]
    }
    pub fn program(&self) -> &RawProgram {
        self.raw()
    }
    pub fn root_interface(&self) -> Option<&RootInterface> {
        self.interface.as_ref()
    }
    pub fn native_exact_work(&self) -> usize {
        self.native.exact_work()
    }
    pub fn checker(&self) -> &Path {
        self.native.checker()
    }
    pub fn derived_effect(&self) -> crate::ir::Effect {
        self.derived_effect
    }
    pub fn output_ports(&self) -> &[crate::ir::QuantumPort] {
        &self.output_ports
    }
    pub(super) fn execution_view_graph(&self) -> super::execution_view::finite::Graph<'_> {
        super::execution_view::finite::Graph {
            graph: &self.decoded,
            root: self.raw(),
            interface: self.interface.as_ref(),
            effect: self.derived_effect,
            outputs: &self.output_ports,
        }
    }
    #[cfg(test)]
    pub(super) fn execution_view_description(&self) -> Result<Vec<u8>> {
        super::execution_view::finite::graph(
            &self.decoded,
            self.raw(),
            self.interface.as_ref(),
            self.derived_effect,
            &self.output_ports,
        )
    }
    /// Source-associated equations retain original bodies and requests. They
    /// do not establish a whole-program source or runtime preservation theorem.
    pub fn source_pure_equations(&self) -> &[Arc<super::pure_leaf::SourcePureEquation>] {
        &self.source_pure_equations
    }
    pub(crate) fn retain_pure_equations(
        mut self,
        equations: Vec<Arc<super::pure_leaf::SourcePureEquation>>,
    ) -> Self {
        self.source_pure_equations = equations.into();
        self
    }
    /// Exact local equations retain the proposed original fragment and its
    /// canonical diagonal reference. They do not prove whole-source lowering,
    /// computed-scope cleanup, or target/resource preservation.
    pub fn source_computed_normalizations(
        &self,
    ) -> &[Arc<super::finite_leaf::SourceUnitaryEquation>] {
        &self.source_computed_normalizations
    }
    pub(crate) fn retain_computed_normalizations(
        mut self,
        equations: Vec<Arc<super::finite_leaf::SourceUnitaryEquation>>,
    ) -> Self {
        self.source_computed_normalizations = equations.into();
        self
    }
    pub(crate) fn kernel(&self) -> Kernel {
        Kernel {
            executable: self.checker().to_owned(),
            decisions: self.native.subject.decisions.clone(),
        }
    }
    pub(crate) fn retain_instruments(
        mut self,
        pairs: Vec<Arc<crate::contract::instrument::InstrumentEvidence>>,
    ) -> Self {
        self.source_instruments = pairs.into();
        self
    }
    pub(crate) fn retain_instrument_calls(
        mut self,
        calls: Vec<crate::contract::instrument::InstrumentCall>,
    ) -> Self {
        self.source_instrument_calls = calls.into();
        self
    }
}
impl Kernel {
    pub fn accept(&self, proposal: &Proposal) -> Result<AcceptedProgram> {
        self.check(proposal.artifact(), proposal.request())
            .map(Checked::into_program)
    }
    pub fn accept_raw(&self, program: RawProgram) -> Result<AcceptedProgram> {
        self.verify(&program).map(Checked::into_program)
    }
    pub(crate) fn accept_raw_with_budget(
        &self,
        program: RawProgram,
        budget: &mut crate::contract::exact::Budget,
    ) -> Result<AcceptedProgram> {
        let accepted = self.accept_raw(program)?;
        budget
            .charge(accepted.native_exact_work())
            .map_err(crate::contract::ContractError::from)
            .map_err(super::contract_error)?;
        Ok(accepted)
    }

    pub(crate) fn function_evidence(
        &self,
        signature: &crate::contract::BasisType,
        implementation: &RawProgram,
        specification: &RawProgram,
        identity: crate::contract::function::RetainedIdentity,
        budget: &mut crate::contract::exact::Budget,
    ) -> Result<crate::contract::FunctionEvidence> {
        use super::{codec::Codec, json::Value};
        use crate::ir::*;
        let bits = signature.bits().map_err(super::contract_error)?;
        let mut encoder = Encoder::new(Version::V2);
        encoder.entries.push(Value::Null);
        encoder.evidence_fields(
            0,
            signature,
            implementation,
            specification,
            identity.parts(),
            None,
        )?;
        // An untrusted call root makes the proposed evidence a reachable graph
        // dependency. No staged FunctionEvidence escapes before Lean accepts.
        let root_raw = RawProgram {
            quantum_inputs: vec![QuantumPort {
                token: TokenId(0),
                wires: (0..bits as u32).map(WireId).collect(),
                shape: BasisShape { bits: bits as u8 },
            }],
            classical_inputs: vec![],
            operations: vec![],
            quantum_outputs: vec![TokenId(1)],
            classical_outputs: vec![],
            declared_effect: Effect::Unitary,
        };
        let mut root_value = root_raw.write(&mut encoder)?;
        let Value::Object(ref mut fields) = root_value else {
            unreachable!()
        };
        fields.insert(
            "operations".into(),
            Value::Array(vec![Value::object([
                ("tag", Value::String("apply_unitary".into())),
                ("input", Value::Number(0)),
                ("output", Value::Number(1)),
                (
                    "steps",
                    Value::Array(vec![Value::object([
                        ("controls", Value::Array(vec![])),
                        (
                            "action",
                            Value::object([
                                ("tag", Value::String("contract".into())),
                                (
                                    "indices",
                                    Value::Array(
                                        (0..bits).map(|n| Value::Number(n as u64)).collect(),
                                    ),
                                ),
                                ("evidence", Value::Number(0)),
                                ("adjoint", Value::Bool(false)),
                            ]),
                        ),
                    ])]),
                ),
            ])]),
        );
        let root = encoder.programs.len();
        encoder.programs.push(root_value);
        let bytes = super::finish_proposal(root, None, encoder)?;
        let accepted = self.accept(&Proposal::new(&bytes, None)?)?;
        budget
            .charge(accepted.native_exact_work())
            .map_err(crate::contract::ContractError::from)
            .map_err(super::contract_error)?;
        let RawOp::ApplyUnitary { steps, .. } = &accepted.raw().operations[0] else {
            return Err(Error::format("native function view missing call"));
        };
        let CircuitAction::Contract { evidence, .. } = &steps[0].action else {
            return Err(Error::format("native function view missing evidence"));
        };
        evidence
            .as_ref()
            .clone()
            .retain_identity(identity)
            .map_err(super::contract_error)
    }
}

fn rejected_contract_detail(raw: &RawProgram) -> Option<(String, String)> {
    use crate::ir::RawOp;
    fn visit(
        ops: &[RawOp],
        prefix: &str,
        budget: &mut crate::contract::exact::Budget,
    ) -> Option<(String, String)> {
        for (index, op) in ops.iter().enumerate() {
            if budget.charge(1).is_err() {
                return None;
            }
            let pointer = format!("{prefix}/{index}");
            match op {
                RawOp::CertifiedCompute {
                    function,
                    use_steps,
                    logical_steps,
                    ..
                } if function.len().is_power_of_two() => {
                    let bits = function.len().trailing_zeros() as usize;
                    if let Err(diagnostic) = crate::contract::check_computed_diagnostic_with_budget(
                        bits,
                        function,
                        use_steps,
                        logical_steps,
                        budget,
                    ) {
                        if diagnostic.error == crate::contract::ContractError::EquationMismatch {
                            return Some((pointer, diagnostic.to_string()));
                        }
                    }
                }
                RawOp::ClassicalBranch {
                    then_ops, else_ops, ..
                } => {
                    if let Some(found) = visit(then_ops, &format!("{pointer}/then_ops"), budget)
                        .or_else(|| visit(else_ops, &format!("{pointer}/else_ops"), budget))
                    {
                        return Some(found);
                    }
                }
                _ => {}
            }
        }
        None
    }
    visit(
        &raw.operations,
        "/operations",
        &mut crate::contract::exact::Budget::new(crate::contract::DEFAULT_EXACT_WORK),
    )
}

#[cfg(test)]
mod preparation_tests {
    use super::*;
    use crate::interchange::json::{self, Value};

    fn artifact(name: &str) -> Vec<u8> {
        let rows = json::parse(include_bytes!(
            "../../tests/fixtures/verification_v030/execution-view-binding/finite-graph-vectors.json"
        ))
        .unwrap();
        let row = rows
            .array()
            .unwrap()
            .iter()
            .find(|row| row.field("name").unwrap().text().unwrap() == name)
            .unwrap();
        json::encode(row.field("artifact").unwrap()).unwrap()
    }

    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    #[test]
    fn binding_retains_predecision_root_and_every_dependency_allocation() {
        let kernel = Kernel::selected().unwrap();
        let mut bytes = artifact("non-topological-evidence-indices");
        let original = bytes.clone();
        let subject = kernel.subject(&bytes, None).unwrap();
        let prepared = Prepared::new(Arc::clone(&subject)).unwrap();
        let graph = Arc::clone(&prepared.decoded);
        assert_eq!(graph.evidence.len(), 2);
        let root = Arc::clone(&graph.programs[graph.root]);
        let dependencies = graph.evidence.clone();
        // Caller buffers are no longer involved in either decoding or IO.
        bytes.fill(0);
        let view = prepared.description().unwrap();
        let native = Kernel::submit_subject(
            Arc::clone(&subject),
            "--qirf-native",
            Some(super::super::native_packet::View {
                graph: &view,
                caller: None,
            }),
        )
        .unwrap();
        let accepted = prepared.bind(native).unwrap().into_program();
        assert_eq!(accepted.artifact(), original);
        assert!(Arc::ptr_eq(&accepted.native.subject, &subject));
        assert!(Arc::ptr_eq(&accepted.decoded, &graph));
        assert!(Arc::ptr_eq(&accepted.decoded.programs[graph.root], &root));
        for (before, after) in dependencies.iter().zip(&accepted.decoded.evidence) {
            assert!(Arc::ptr_eq(before, after));
        }
        assert_eq!(accepted.raw(), root.as_ref());
        assert!(accepted.native_exact_work() > 0);
    }

    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    #[test]
    fn equal_bytes_from_another_fresh_invocation_cannot_bind_prepared_data() {
        let kernel = Kernel::selected().unwrap();
        let bytes = artifact("phase-graph");
        let subject = kernel.subject(&bytes, None).unwrap();
        let prepared = Prepared::new(Arc::clone(&subject)).unwrap();
        let other = kernel.inspect(&bytes, None).unwrap();
        assert_eq!(subject.artifact(), other.artifact());
        assert!(!Arc::ptr_eq(&subject, &other.subject));
        let failure = prepared.bind(other).unwrap_err();
        assert_eq!(failure.code, "kernel");
        assert_eq!(
            failure.message,
            "native decision belongs to a different subject"
        );
    }

    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    #[test]
    fn inspection_of_the_same_subject_cannot_authorize_execution() {
        let kernel = Kernel::selected().unwrap();
        let subject = kernel.subject(&artifact("phase-graph"), None).unwrap();
        let prepared = Prepared::new(Arc::clone(&subject)).unwrap();
        let native = Kernel::inspect_subject(subject, "--qirf-native").unwrap();
        let error = prepared.bind(native).unwrap_err();
        assert_eq!(error.code, "kernel");
        assert_eq!(
            error.message,
            "inspection does not authorize an execution view"
        );
    }

    #[test]
    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    fn divergent_actual_decoded_root_is_rejected_while_original_inspection_succeeds() {
        let kernel = Kernel::selected().unwrap();
        let subject = kernel.subject(&artifact("phase-graph"), None).unwrap();
        let mut prepared = Prepared::new(Arc::clone(&subject)).unwrap();
        let graph = Arc::get_mut(&mut prepared.decoded).unwrap();
        let root = Arc::make_mut(&mut graph.programs[graph.root]);
        let crate::ir::RawOp::Gate { gate, .. } = &mut root.operations[2] else {
            panic!("the phase fixture must retain its original T gate")
        };
        assert_eq!(*gate, crate::ir::SingleGate::T);
        *gate = crate::ir::SingleGate::Z;
        let view = prepared.description().unwrap();
        Kernel::inspect_subject(Arc::clone(&subject), "--qirf-native").unwrap();
        let error = Kernel::submit_subject(
            subject,
            "--qirf-native",
            Some(super::super::native_packet::View {
                graph: &view,
                caller: None,
            }),
        )
        .unwrap_err();
        assert_eq!(error.code, "decoded_view");
    }

    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    #[test]
    fn materialization_is_not_acceptance_and_native_rejections_stay_authoritative() {
        let kernel = Kernel::selected().unwrap();
        let mut value = json::parse(&artifact("hidden-discard-graph")).unwrap();
        let Value::Object(fields) = &mut value else {
            panic!("object")
        };
        let Value::Array(programs) = fields.get_mut("programs").unwrap() else {
            panic!("array")
        };
        let Value::Object(root) = &mut programs[0] else {
            panic!("program")
        };
        root.insert("declared_effect".into(), Value::String("unitary".into()));
        let bytes = json::encode(&value).unwrap();
        let prepared = Prepared::new(kernel.subject(&bytes, None).unwrap()).unwrap();
        assert_eq!(prepared.derived_effect, crate::ir::Effect::Observe);
        let inspection = kernel.inspect(&bytes, None).unwrap_err();
        let execution = kernel.check(&bytes, None).unwrap_err();
        assert_eq!(execution.code, "invalid_ir");
        assert_eq!(execution.code, inspection.code);
        assert_eq!(execution.message, inspection.message);

        // A simultaneous decoder failure must not replace Lean's refusal.
        assert!(Prepared::new(kernel.subject(b"{", None).unwrap()).is_err());
        let inspection = kernel.inspect(b"{", None).unwrap_err();
        let execution = kernel.check(b"{", None).unwrap_err();
        assert_eq!(execution.code, inspection.code);
        assert_eq!(execution.message, inspection.message);
    }
}
