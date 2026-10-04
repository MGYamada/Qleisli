//! One native acceptance boundary for immutable QIRF proposals.
//! Rust decodes the exact accepted bytes for execution; it issues no ownership,
//! equation or isometry decision. Decoder/runtime correspondence remains explicit.
// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

mod runtime;

use std::path::{Path, PathBuf};
use std::sync::Arc;

use super::{Encoder, Error, Imported, Result, RootInterface, Version};
use crate::ir::RawProgram;

/// Fresh native acceptance of immutable QIRF/request bytes. This report carries
/// no decoded execution view and cannot be deserialized from a success receipt.
/// Native compilation and transport remain explicit deployment assumptions.
#[derive(Clone, Debug)]
pub struct NativeChecked {
    artifact: Arc<[u8]>,
    request: Option<Arc<[u8]>>,
    exact_work: usize,
    checker: PathBuf,
}

impl NativeChecked {
    pub fn artifact(&self) -> &[u8] {
        &self.artifact
    }
    pub fn request(&self) -> Option<&[u8]> {
        self.request.as_deref()
    }
    pub fn exact_work(&self) -> usize {
        self.exact_work
    }
    /// Canonical path used for this invocation, not a binary attestation.
    pub fn checker(&self) -> &Path {
        &self.checker
    }
}

/// An explicitly selected native checker; no PATH search or runtime download.
#[derive(Clone, Debug)]
pub struct Kernel {
    executable: PathBuf,
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
        }
    }

    /// The native checker must accept the same complete input. Any rejection,
    /// unsupported form, exhausted capacity or transport failure blocks use.
    /// A separate request is optional and checked independently by Lean.
    pub fn check(&self, artifact: &[u8], request: Option<&[u8]>) -> Result<Checked> {
        let native = self.inspect(artifact, request).map_err(|mut failure| {
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
        })?;
        Self::decode_checked(native)
    }

    fn decode_checked(native: NativeChecked) -> Result<Checked> {
        let mut budget = crate::contract::exact::Budget::new(crate::contract::DEFAULT_EXACT_WORK);
        let (program, root_interface, _) = super::decode_native(&native, &mut budget)?;
        let (derived_effect, output_ports) = view::metadata(&program)?;
        let imported = Imported {
            program: AcceptedProgram {
                native: Arc::new(native.clone()),
                program: Arc::new(program),
                interface: root_interface.clone(),
                derived_effect,
                output_ports,
            },
            root_interface,
            request_checked: native.request().is_some(),
            exact_work: native.exact_work,
        };
        Ok(Checked {
            artifact: native.artifact,
            request: native.request,
            imported,
            native_exact_work: native.exact_work,
        })
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
        let bytes = super::encode_proposal(program, interface, Encoder::new(version))?;
        self.check(&bytes, request).map_err(|mut failure| {
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
        let bytes = super::encode_proposal(program.raw(), interface, encoder)?;
        self.check(&bytes, request)
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
        if artifact.is_empty()
            || artifact.len() > 16 << 20
            || request.is_some_and(|r| r.is_empty() || r.len() > 16 << 20)
        {
            return Err(Error::limit(
                "native input must contain 1..16777216 bytes per file",
            ));
        }
        let artifact: Arc<[u8]> = Arc::from(artifact);
        let request: Option<Arc<[u8]>> = request.map(Arc::from);
        let mut packet =
            Vec::with_capacity(12 + artifact.len() + request.as_ref().map_or(0, |r| r.len()));
        packet.extend_from_slice(b"QLV1");
        packet.extend_from_slice(&(artifact.len() as u32).to_le_bytes());
        packet.extend_from_slice(&(request.as_ref().map_or(0, |r| r.len()) as u32).to_le_bytes());
        packet.extend_from_slice(&artifact);
        if let Some(request) = &request {
            packet.extend_from_slice(request);
        }
        let executable = std::fs::canonicalize(&self.executable)
            .map_err(|e| Error::new("io", format!("cannot resolve Lean checker: {e}")))?;
        let native_exact_work = runtime::check_mode(&executable, packet, request.is_some(), mode)?;
        Ok(NativeChecked {
            artifact,
            request,
            exact_work: native_exact_work,
            checker: executable,
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
    program: Arc<RawProgram>,
    interface: Option<RootInterface>,
    derived_effect: crate::ir::Effect,
    output_ports: Vec<crate::ir::QuantumPort>,
}
impl AcceptedProgram {
    pub fn artifact(&self) -> &[u8] {
        self.native.artifact()
    }
    pub fn request(&self) -> Option<&[u8]> {
        self.native.request()
    }
    pub fn raw(&self) -> &RawProgram {
        &self.program
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
    pub(crate) fn kernel(&self) -> Kernel {
        Kernel::new(self.checker())
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
        // dependency. No FunctionEvidence value exists before Lean accepts.
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
