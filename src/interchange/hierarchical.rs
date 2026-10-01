//! Fresh conditional hierarchy inspection and finite reconstruction.
//! Additive checked-request reports are not production VerifiedProgram values.
//! Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

mod bridge;
mod runtime;
use runtime::Mode;
pub mod execution;

use std::path::{Path, PathBuf};
use std::sync::Arc;

use super::finite_leaf::{
    CheckedSerializedUnitaryLeaf, UnitaryBoundary, check_serialized_unitary, check_unitary,
};
use super::json::Value;
use super::{Error, Result, contract_error};
use crate::contract::exact::{Budget, Exact, Matrix};
use crate::contract::{BasisType, ContractError, DEFAULT_EXACT_WORK};
use crate::ir::{BasisShape, QuantumPort, TokenId, WireId};

/// Explicitly selected native dependency. The caller must select a built and
/// audited Qleisli kernel; arbitrary executable paths are not evidence.
#[derive(Clone, Debug)]
pub struct Kernel {
    executable: PathBuf,
}

/// A completed reconstruction report for the supported conditional profile.
/// No independently requested root or source-adequacy claim is included.
#[derive(Debug)]
pub struct Reconstructed {
    payload: Arc<[u8]>,
    leaves: Vec<(usize, CheckedSerializedUnitaryLeaf)>,
    structural_work: usize,
    exact_work: usize,
}

impl Reconstructed {
    fn new(
        payload: &[u8],
        leaves: Vec<(usize, CheckedSerializedUnitaryLeaf)>,
        structural_work: usize,
        budget: &Budget,
    ) -> Self {
        Self {
            payload: Arc::from(payload),
            leaves,
            structural_work,
            exact_work: DEFAULT_EXACT_WORK - budget.remaining(),
        }
    }

    pub fn payload(&self) -> &[u8] {
        &self.payload
    }
    pub fn leaves(&self) -> &[(usize, CheckedSerializedUnitaryLeaf)] {
        &self.leaves
    }
    pub fn structural_work(&self) -> usize {
        self.structural_work
    }
    pub fn exact_work(&self) -> usize {
        self.exact_work
    }
}

impl Kernel {
    pub fn new(executable: impl Into<PathBuf>) -> Self {
        Self {
            executable: executable.into(),
        }
    }

    pub fn executable(&self) -> &Path {
        &self.executable
    }

    /// Run a fresh native conditional check, then reconstruct every requested
    /// finite equation from this same immutable decoded artifact. No runtime
    /// response or producer success flag is accepted as an API argument.
    pub fn inspect(&self, payload: &[u8]) -> Result<Reconstructed> {
        let decoded = bridge::decode(payload)?;
        let response = runtime::check(&self.executable, decoded.bridge, Mode::Inspect)?;
        let mut budget = Budget::new(DEFAULT_EXACT_WORK);
        let leaves = reconstruct(&decoded.value, response.indices, &mut budget)?;
        Ok(Reconstructed::new(payload, leaves, response.work, &budget))
    }
}

fn reconstruct(
    value: &Value,
    indices: Vec<usize>,
    budget: &mut Budget,
) -> Result<Vec<(usize, CheckedSerializedUnitaryLeaf)>> {
    let proofs = value.field("proofs")?.array()?;
    let definitions = value.field("definitions")?.array()?;
    let meanings = value.field("meanings")?.array()?;
    let mut leaves = Vec::with_capacity(indices.len());
    let mut seen = vec![false; proofs.len()];
    for index in indices {
        let proof = proofs
            .get(index)
            .ok_or_else(|| Error::format("runtime returned an invalid proof index"))?;
        if seen[index] || proof.field("rule")?.field("tag")?.text()? != "finite" {
            return Err(Error::format(
                "runtime returned duplicate or non-finite proof index",
            ));
        }
        seen[index] = true;
        let definition = &definitions[bridge::number(proof.field("implementation")?)? as usize];
        let meaning = &meanings[bridge::number(proof.field("meaning")?)? as usize];
        let db = definition.field("body")?;
        let mb = meaning.field("body")?;
        if db.field("tag")?.text()? != "leaf" || mb.field("tag")?.text()? != "finite" {
            return Err(Error::new(
                "contract",
                "finite request does not name actual finite bodies",
            ));
        }
        let program = db.field("program")?.text()?.as_bytes();
        let description = mb.field("description")?.text()?.as_bytes();
        let boundary = boundary(definition.field("interface")?)?;
        let checked = check_serialized_unitary(program, &boundary, description, budget)?;
        leaves.push((index, checked));
    }
    // Every proof is checked by the pure pass, not just the root chain.
    for (index, proof) in proofs.iter().enumerate() {
        if proof.field("rule")?.field("tag")?.text()? == "finite" && !seen[index] {
            return Err(Error::format(
                "runtime omitted a finite reconstruction obligation",
            ));
        }
    }
    Ok(leaves)
}

/// A fresh checked match against caller-supplied meaning for the supported
/// conditional profile. Finite reconstruction retains its Rust correspondence
/// premise; this is not a complete production hierarchy or source guarantee.
#[derive(Debug)]
pub struct CheckedRequest {
    reconstruction: Reconstructed,
    request: Arc<[u8]>,
}

impl CheckedRequest {
    pub fn reconstruction(&self) -> &Reconstructed {
        &self.reconstruction
    }
    pub fn request(&self) -> &[u8] {
        &self.request
    }
}

impl Kernel {
    /// Check the same immutable artifact against an independent request.
    /// The caller must choose the request independently of the proposed IR;
    /// neither serialized success flags nor cached pair results are inputs.
    pub fn check_against(&self, payload: &[u8], request: &[u8]) -> Result<CheckedRequest> {
        let decoded = bridge::decode_request(payload, request)?;
        let mode = if decoded.fourier_width.is_some() {
            Mode::Fourier
        } else {
            Mode::Request
        };
        let response = runtime::check(&self.executable, decoded.bridge, mode)?;
        let mut budget = Budget::new(DEFAULT_EXACT_WORK);
        let leaves = reconstruct(&decoded.actual, response.indices, &mut budget)?;
        if let Some(width) = decoded.fourier_width {
            reconstruct_hadamards(&decoded.actual, width, response.pairs, &mut budget)?;
        } else {
            reconstruct_pairs(
                &decoded.actual,
                &decoded.request,
                &decoded.pairs,
                response.pairs,
                &mut budget,
            )?;
        }
        Ok(CheckedRequest {
            reconstruction: Reconstructed::new(payload, leaves, response.work, &budget),
            request: Arc::from(request),
        })
    }
}

fn reconstruct_pairs(
    actual: &Value,
    required: &Value,
    pairs: &[(usize, usize)],
    indices: Vec<usize>,
    budget: &mut Budget,
) -> Result<()> {
    let actual = actual.field("meanings")?.array()?;
    let required = required.field("meanings")?.array()?;
    let mut seen = vec![false; pairs.len()];
    for index in indices {
        let &(a, r) = pairs
            .get(index)
            .ok_or_else(|| Error::format("runtime returned invalid meaning pair index"))?;
        if seen[index] {
            return Err(Error::format(
                "runtime returned duplicate meaning pair index",
            ));
        }
        seen[index] = true;
        let a = actual[a].field("body")?;
        let r = required[r].field("body")?;
        if a.field("tag")?.text()? != "finite" || r.field("tag")?.text()? != "finite" {
            return Err(Error::format("runtime returned non-finite meaning pair"));
        }
        let a = super::finite_matrix::decode(a.field("description")?.text()?.as_bytes(), budget)?;
        let r = super::finite_matrix::decode(r.field("description")?.text()?.as_bytes(), budget)?;
        budget
            .charge(a.entries().len())
            .map_err(ContractError::from)
            .map_err(contract_error)?;
        if a != r {
            return Err(Error::new(
                "contract",
                "finite meaning differs from independently requested matrix",
            ));
        }
    }
    for (i, &(a, r)) in pairs.iter().enumerate() {
        if actual[a].field("body")?.field("tag")?.text()? == "finite"
            && required[r].field("body")?.field("tag")?.text()? == "finite"
            && !seen[i]
        {
            return Err(Error::format(
                "runtime omitted finite meaning equality obligation",
            ));
        }
    }
    Ok(())
}

/// A composed initialization, pure circuit and readout report bound to the
/// caller's explicit request. All finite obligations have been reconstructed.
/// This experimental report is not a production `VerifiedProgram`, a source
/// preservation proof, or a proof of a named algorithm such as QPE.
#[derive(Debug)]
pub struct CheckedInstrument {
    reconstruction: Reconstructed,
    request: Arc<[u8]>,
}

impl CheckedInstrument {
    /// Retains the full immutable instrument payload, finite circuit leaves
    /// and work counts for the fresh composed check.
    pub fn reconstruction(&self) -> &Reconstructed {
        &self.reconstruction
    }
    pub fn request(&self) -> &[u8] {
        &self.request
    }
}

impl Kernel {
    /// Check initialization, the independently selected unitary equation and
    /// ordered readout together. No component success flag or cached report
    /// can be supplied in place of a fresh native check.
    pub fn check_instrument(&self, payload: &[u8], request: &[u8]) -> Result<CheckedInstrument> {
        let decoded = bridge::decode_instrument(payload, request)?;
        let response = runtime::check(&self.executable, decoded.bridge, Mode::Instrument)?;
        let mut budget = Budget::new(DEFAULT_EXACT_WORK);
        let leaves = reconstruct(&decoded.pure.actual, response.indices, &mut budget)?;
        reconstruct_pairs(
            &decoded.pure.actual,
            &decoded.pure.request,
            &decoded.pure.pairs,
            response.pairs,
            &mut budget,
        )?;
        Ok(CheckedInstrument {
            reconstruction: Reconstructed::new(payload, leaves, response.work, &budget),
            request: Arc::from(request),
        })
    }

    /// Fresh named-QPE component checking against an independently chosen
    /// provider/layout request and an untrusted structural candidate. All
    /// finite equations, provider pairs and phase-fixed H roles are discharged
    /// under one exact budget. This is not production verification authority
    /// or a source-preservation theorem; the audited native runtime and Rust
    /// finite adapter remain explicit correspondence premises.
    pub fn check_qpe_instrument(
        &self,
        payload: &[u8],
        request: &[u8],
        candidate: &[u8],
    ) -> Result<CheckedQpeInstrument> {
        let decoded = bridge::decode_qpe_instrument(payload, request, candidate)?;
        let response = runtime::check(&self.executable, decoded.bridge, Mode::QpeInstrument)?;
        let mut budget = Budget::new(DEFAULT_EXACT_WORK);
        let leaves = reconstruct(&decoded.provider.actual, response.indices, &mut budget)?;
        reconstruct_pairs(
            &decoded.provider.actual,
            &decoded.provider.request,
            &decoded.provider.pairs,
            response.pairs,
            &mut budget,
        )?;
        let returned: std::collections::BTreeSet<_> = response.hadamards.iter().copied().collect();
        if returned.len() != response.hadamards.len() || returned != decoded.hadamards {
            return Err(Error::format(
                "runtime omitted, duplicated or substituted QPE Hadamard obligations",
            ));
        }
        for index in response.hadamards {
            reconstruct_hadamards(&decoded.provider.actual, 1, vec![index], &mut budget)?;
        }
        Ok(CheckedQpeInstrument {
            instrument: CheckedInstrument {
                reconstruction: Reconstructed::new(payload, leaves, response.work, &budget),
                request: Arc::from(request),
            },
            candidate: Arc::from(candidate),
        })
    }
}

/// Checked named-QPE component report with a distinct independent provider
/// request and retained candidate bytes. The contained instrument supports the
/// existing bounded numerical execution/sampling APIs; no external schema,
/// production `VerifiedProgram`, or source theorem is created.
#[derive(Debug)]
pub struct CheckedQpeInstrument {
    instrument: CheckedInstrument,
    candidate: Arc<[u8]>,
}

impl CheckedQpeInstrument {
    pub fn instrument(&self) -> &CheckedInstrument {
        &self.instrument
    }
    pub fn candidate(&self) -> &[u8] {
        &self.candidate
    }
}

/// Additional obligations use the exact mathematical H target, never a matrix
/// supplied by the producer. Complete artifact and request bytes remain retained.
fn reconstruct_hadamards(
    value: &Value,
    width: usize,
    indices: Vec<usize>,
    budget: &mut Budget,
) -> Result<()> {
    if !(1..=8).contains(&width) || indices.len() != width {
        return Err(Error::format(
            "runtime omitted Fourier Hadamard obligations",
        ));
    }
    let r = Exact::inv_sqrt2();
    let negative = r
        .neg()
        .map_err(ContractError::from)
        .map_err(contract_error)?;
    let expected = Matrix::new(2, 2, vec![r, r, r, negative])
        .map_err(ContractError::from)
        .map_err(contract_error)?;
    let definitions = value.field("definitions")?.array()?;
    let mut seen = vec![false; definitions.len()];
    for index in indices {
        let d = definitions
            .get(index)
            .ok_or_else(|| Error::format("runtime returned invalid H definition index"))?;
        if seen[index] || d.field("body")?.field("tag")?.text()? != "leaf" {
            return Err(Error::format(
                "runtime returned duplicate or non-leaf H index",
            ));
        }
        seen[index] = true;
        let program = d.field("body")?.field("program")?.text()?.as_bytes();
        check_unitary(
            program,
            &boundary(d.field("interface")?)?,
            &expected,
            budget,
        )?;
    }
    Ok(())
}

fn legacy(value: &Value) -> Result<BasisType> {
    let mut stack = Vec::new();
    for atom in value.array()?.iter().rev() {
        match atom.field("tag")?.text()? {
            "unit" => stack.push(BasisType::Unit),
            "bit" => stack.push(BasisType::Bit),
            "tuple" => {
                let arity = bridge::number(atom.field("arity")?)? as usize;
                if arity < 2 || arity > stack.len() {
                    return Err(Error::format("invalid finite type tree"));
                }
                let fields = (0..arity).map(|_| stack.pop().unwrap()).collect();
                stack.push(BasisType::Tuple(fields));
            }
            _ => {
                return Err(Error::new(
                    "contract",
                    "finite boundary requires an explicit legacy type",
                ));
            }
        }
    }
    if stack.len() != 1 {
        return Err(Error::format(
            "finite boundary is not one complete type tree",
        ));
    }
    Ok(stack.pop().unwrap())
}

fn boundary(value: &Value) -> Result<UnitaryBoundary> {
    let port = |side: &Value| -> Result<(BasisType, QuantumPort)> {
        let ports = side.field("quantum")?.array()?;
        if ports.len() != 1 || !side.field("classical")?.array()?.is_empty() {
            return Err(Error::new(
                "contract",
                "finite unitary request requires unary quantum endpoints",
            ));
        }
        let p = &ports[0];
        let ty = legacy(p.field("basis")?)?;
        let bits = ty.bits().map_err(contract_error)?;
        let wires = p
            .field("axes")?
            .array()?
            .iter()
            .map(|v| bridge::number(v).map(WireId))
            .collect::<Result<_>>()?;
        Ok((
            ty,
            QuantumPort {
                token: TokenId(bridge::number(p.field("owner")?)?),
                wires,
                shape: BasisShape { bits: bits as u8 },
            },
        ))
    };
    let (input_type, input) = port(value.field("inputs")?)?;
    let (output_type, output) = port(value.field("outputs")?)?;
    if input_type != output_type {
        return Err(Error::new("contract", "finite endpoint type trees differ"));
    }
    UnitaryBoundary::new(input_type, input, output)
}
