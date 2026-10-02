//! Fresh conditional hierarchy inspection and finite reconstruction.
//! Additive checked-request reports are not production VerifiedProgram values.
//! Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

mod bridge;
mod runtime;
use runtime::Mode;
pub mod execution;

use std::path::{Path, PathBuf};
use std::sync::Arc;

use super::finite_leaf::{CheckedSerializedUnitaryLeaf, UnitaryBoundary, check_serialized_unitary};
use super::json::Value;
use super::{Error, Result, contract_error};
use crate::contract::exact::{Budget, Matrix};
use crate::contract::{BasisType, DEFAULT_EXACT_WORK};
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
    native_exact_work: usize,
}

impl Reconstructed {
    fn new(
        payload: &[u8],
        leaves: Vec<(usize, CheckedSerializedUnitaryLeaf)>,
        structural_work: usize,
        native_exact_work: usize,
        budget: &Budget,
    ) -> Self {
        Self {
            payload: Arc::from(payload),
            leaves,
            structural_work,
            exact_work: DEFAULT_EXACT_WORK - budget.remaining(),
            native_exact_work,
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
    /// Native original-QIRF, request and H work under its own shared ceiling.
    /// Compatibility Rust handles are independently rebuilt, not double charged
    /// into this budget. `exact_work` reports that separate legacy work.
    pub fn native_exact_work(&self) -> usize {
        self.native_exact_work
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
        Ok(Reconstructed::new(
            payload,
            leaves,
            response.work,
            response.exact_work,
            &budget,
        ))
    }
}

/// Experimental native-only report. It retains immutable inputs but creates no
/// Rust `VerifiedProgram` or executable finite-leaf handle. Decoder/native
/// correspondence and the selected audited executable remain assumptions.
#[derive(Debug)]
pub struct NativeChecked {
    payload: Arc<[u8]>,
    request: Option<Arc<[u8]>>,
    candidate: Option<Arc<[u8]>>,
    structural_work: usize,
    exact_work: usize,
}

impl NativeChecked {
    fn new(
        payload: &[u8],
        request: Option<&[u8]>,
        candidate: Option<&[u8]>,
        response: &runtime::Response,
    ) -> Self {
        Self {
            payload: Arc::from(payload),
            request: request.map(Arc::from),
            candidate: candidate.map(Arc::from),
            structural_work: response.work,
            exact_work: response.exact_work,
        }
    }
    pub fn payload(&self) -> &[u8] {
        &self.payload
    }
    pub fn request(&self) -> Option<&[u8]> {
        self.request.as_deref()
    }
    pub fn candidate(&self) -> Option<&[u8]> {
        self.candidate.as_deref()
    }
    pub fn structural_work(&self) -> usize {
        self.structural_work
    }
    pub fn exact_work(&self) -> usize {
        self.exact_work
    }
}

impl Kernel {
    /// Check all actual QIRF leaves natively, without invoking Rust acceptance.
    pub fn inspect_native(&self, payload: &[u8]) -> Result<NativeChecked> {
        let decoded = bridge::decode(payload)?;
        let response = runtime::check(&self.executable, decoded.bridge, Mode::Inspect)?;
        validate_leaves(&decoded.value, &response.indices)?;
        Ok(NativeChecked::new(payload, None, None, &response))
    }

    /// Native original-QIRF/request checking, including phase-fixed Fourier H.
    pub fn check_against_native(&self, payload: &[u8], request: &[u8]) -> Result<NativeChecked> {
        let decoded = bridge::decode_request(payload, request)?;
        let mode = if decoded.fourier_width.is_some() {
            Mode::Fourier
        } else {
            Mode::Request
        };
        let response = runtime::check(&self.executable, decoded.bridge, mode)?;
        validate_leaves(&decoded.actual, &response.indices)?;
        if let Some(width) = decoded.fourier_width {
            validate_hadamards(&decoded.actual, width, response.pairs.clone())?;
        } else {
            validate_pairs(
                &decoded.actual,
                &decoded.request,
                &decoded.pairs,
                response.pairs.clone(),
            )?;
        }
        Ok(NativeChecked::new(payload, Some(request), None, &response))
    }

    /// Native composed initialization, finite circuit request and readout.
    pub fn check_instrument_native(&self, payload: &[u8], request: &[u8]) -> Result<NativeChecked> {
        let decoded = bridge::decode_instrument(payload, request)?;
        let response = runtime::check(&self.executable, decoded.bridge, Mode::Instrument)?;
        validate_leaves(&decoded.pure.actual, &response.indices)?;
        validate_pairs(
            &decoded.pure.actual,
            &decoded.pure.request,
            &decoded.pure.pairs,
            response.pairs.clone(),
        )?;
        Ok(NativeChecked::new(payload, Some(request), None, &response))
    }

    /// Native named-QPE provider, schedule and exact H checks. No production
    /// verification authority, source theorem or external schema is enabled.
    pub fn check_qpe_instrument_native(
        &self,
        payload: &[u8],
        request: &[u8],
        candidate: &[u8],
    ) -> Result<NativeChecked> {
        let decoded = bridge::decode_qpe_instrument(payload, request, candidate)?;
        let response = runtime::check(&self.executable, decoded.bridge, Mode::QpeInstrument)?;
        validate_leaves(&decoded.provider.actual, &response.indices)?;
        validate_pairs(
            &decoded.provider.actual,
            &decoded.provider.request,
            &decoded.provider.pairs,
            response.pairs.clone(),
        )?;
        let returned: std::collections::BTreeSet<_> = response.hadamards.iter().copied().collect();
        if returned.len() != response.hadamards.len() || returned != decoded.hadamards {
            return Err(Error::format(
                "runtime omitted, duplicated or substituted QPE Hadamard obligations",
            ));
        }
        for &index in &response.hadamards {
            validate_hadamards(&decoded.provider.actual, 1, vec![index])?;
        }
        Ok(NativeChecked::new(
            payload,
            Some(request),
            Some(candidate),
            &response,
        ))
    }
}

fn validate_leaves(value: &Value, indices: &[usize]) -> Result<()> {
    let proofs = value.field("proofs")?.array()?;
    let mut seen = vec![false; proofs.len()];
    for &index in indices {
        let proof = proofs
            .get(index)
            .ok_or_else(|| Error::format("runtime returned an invalid proof index"))?;
        if seen[index] || proof.field("rule")?.field("tag")?.text()? != "finite" {
            return Err(Error::format(
                "runtime returned duplicate or non-finite proof index",
            ));
        }
        seen[index] = true;
    }
    for (index, proof) in proofs.iter().enumerate() {
        if proof.field("rule")?.field("tag")?.text()? == "finite" && !seen[index] {
            return Err(Error::format(
                "runtime omitted a finite reconstruction obligation",
            ));
        }
    }
    Ok(())
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
            validate_hadamards(&decoded.actual, width, response.pairs)?;
        } else {
            validate_pairs(
                &decoded.actual,
                &decoded.request,
                &decoded.pairs,
                response.pairs,
            )?;
        }
        Ok(CheckedRequest {
            reconstruction: Reconstructed::new(
                payload,
                leaves,
                response.work,
                response.exact_work,
                &budget,
            ),
            request: Arc::from(request),
        })
    }
}

// Native v3 has already read and compared the exact matrices. This only checks
// transport coverage; a returned index or work count is not semantic evidence.
fn validate_pairs(
    actual: &Value,
    required: &Value,
    pairs: &[(usize, usize)],
    indices: Vec<usize>,
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
        validate_pairs(
            &decoded.pure.actual,
            &decoded.pure.request,
            &decoded.pure.pairs,
            response.pairs,
        )?;
        Ok(CheckedInstrument {
            reconstruction: Reconstructed::new(
                payload,
                leaves,
                response.work,
                response.exact_work,
                &budget,
            ),
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
        validate_pairs(
            &decoded.provider.actual,
            &decoded.provider.request,
            &decoded.provider.pairs,
            response.pairs,
        )?;
        let returned: std::collections::BTreeSet<_> = response.hadamards.iter().copied().collect();
        if returned.len() != response.hadamards.len() || returned != decoded.hadamards {
            return Err(Error::format(
                "runtime omitted, duplicated or substituted QPE Hadamard obligations",
            ));
        }
        for index in response.hadamards {
            validate_hadamards(&decoded.provider.actual, 1, vec![index])?;
        }
        Ok(CheckedQpeInstrument {
            instrument: CheckedInstrument {
                reconstruction: Reconstructed::new(
                    payload,
                    leaves,
                    response.work,
                    response.exact_work,
                    &budget,
                ),
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

/// Transport coverage only. The native checker has reconstructed original QIRF
/// against mathematical H, never a producer-supplied replacement target.
fn validate_hadamards(value: &Value, width: usize, indices: Vec<usize>) -> Result<()> {
    if !(1..=8).contains(&width) || indices.len() != width {
        return Err(Error::format(
            "runtime omitted Fourier Hadamard obligations",
        ));
    }
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
                let first = stack.pop().unwrap();
                let second = stack.pop().unwrap();
                let ty = if arity == 2 {
                    BasisType::pair(first, second)
                } else {
                    let mut fields = vec![first, second];
                    fields.extend((2..arity).map(|_| stack.pop().unwrap()));
                    BasisType::Tuple(fields)
                };
                stack.push(ty);
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
