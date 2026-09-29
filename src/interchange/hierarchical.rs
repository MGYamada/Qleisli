//! Fresh conditional hierarchy inspection and finite reconstruction.
//! Additive checked-request reports are not production VerifiedProgram values.
//! Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

mod bridge;

use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::Arc;
use std::time::{Duration, Instant};

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
        let response = invoke(&self.executable, decoded.bridge, Mode::Inspect)?;
        let response = response_indices(&response, Mode::Inspect)?;
        let mut budget = Budget::new(DEFAULT_EXACT_WORK);
        let leaves = reconstruct(&decoded.value, response.indices, &mut budget)?;
        Ok(Reconstructed {
            payload: Arc::from(payload),
            leaves,
            structural_work: response.work,
            exact_work: DEFAULT_EXACT_WORK - budget.remaining(),
        })
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
        let response = invoke(&self.executable, decoded.bridge, mode)?;
        let response = response_indices(&response, mode)?;
        let mut budget = Budget::new(DEFAULT_EXACT_WORK);
        let leaves = reconstruct(&decoded.actual, response.indices, &mut budget)?;
        if let Some(width) = decoded.fourier_width {
            reconstruct_hadamards(&decoded.actual, width, response.pairs, &mut budget)?;
            return Ok(CheckedRequest {
                reconstruction: Reconstructed {
                    payload: Arc::from(payload),
                    leaves,
                    structural_work: response.work,
                    exact_work: DEFAULT_EXACT_WORK - budget.remaining(),
                },
                request: Arc::from(request),
            });
        }
        let actual = decoded.actual.field("meanings")?.array()?;
        let required = decoded.request.field("meanings")?.array()?;
        let mut seen = vec![false; decoded.pairs.len()];
        for index in response.pairs {
            let &(a, r) = decoded
                .pairs
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
            let a = super::finite_matrix::decode(
                a.field("description")?.text()?.as_bytes(),
                &mut budget,
            )?;
            let r = super::finite_matrix::decode(
                r.field("description")?.text()?.as_bytes(),
                &mut budget,
            )?;
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
        for (i, &(a, r)) in decoded.pairs.iter().enumerate() {
            if actual[a].field("body")?.field("tag")?.text()? == "finite"
                && required[r].field("body")?.field("tag")?.text()? == "finite"
                && !seen[i]
            {
                return Err(Error::format(
                    "runtime omitted finite meaning equality obligation",
                ));
            }
        }
        Ok(CheckedRequest {
            reconstruction: Reconstructed {
                payload: Arc::from(payload),
                leaves,
                structural_work: response.work,
                exact_work: DEFAULT_EXACT_WORK - budget.remaining(),
            },
            request: Arc::from(request),
        })
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

#[derive(Clone, Copy)]
enum Mode {
    Inspect,
    Request,
    Fourier,
}
impl Mode {
    fn argument(self) -> &'static str {
        match self {
            Self::Inspect => "--hierarchy-pending",
            Self::Request => "--hierarchy-request-pending",
            Self::Fourier => "--hierarchy-fourier-pending",
        }
    }
    fn header(self) -> &'static str {
        match self {
            Self::Inspect => "qleisli.hierarchy-pending 1",
            Self::Request => "qleisli.hierarchy-request-pending 1",
            Self::Fourier => "qleisli.hierarchy-fourier-pending 1",
        }
    }
    fn maximum(self) -> usize {
        match self {
            Self::Inspect => 1_100_000,
            Self::Request | Self::Fourier => 2_200_000,
        }
    }
}
struct Response {
    work: usize,
    indices: Vec<usize>,
    pairs: Vec<usize>,
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

fn response_indices(bytes: &[u8], mode: Mode) -> Result<Response> {
    let text =
        std::str::from_utf8(bytes).map_err(|_| Error::format("invalid runtime response UTF-8"))?;
    let mut lines = text.split('\n');
    if lines.next() != Some(mode.header()) {
        return Err(Error::format("unknown runtime response"));
    }
    match lines.next() {
        Some("pending") => {}
        Some("error") => {
            let code = match lines.next() {
                Some("limit") => "limit",
                Some("contract") => "contract",
                Some("invalid_ir") => "invalid_ir",
                Some("format") => "format",
                _ => return Err(Error::format("unknown runtime failure")),
            };
            return Err(Error::new(
                code,
                "Lean hierarchy inspection rejected the artifact",
            ));
        }
        _ => return Err(Error::format("unknown runtime response status")),
    }
    let integer = |s: Option<&str>, maximum: usize| -> Result<usize> {
        let s = s.ok_or_else(|| Error::format("truncated runtime response"))?;
        if s.is_empty()
            || s.len() > 10
            || !s.bytes().all(|b| b.is_ascii_digit())
            || (s.len() > 1 && s.starts_with('0'))
        {
            return Err(Error::format("invalid runtime integer"));
        }
        let n = s
            .parse::<usize>()
            .map_err(|_| Error::limit("runtime integer overflow"))?;
        if n > maximum {
            return Err(Error::limit("runtime response exceeds its bound"));
        }
        Ok(n)
    };
    let work = integer(lines.next(), 2_000_000)?;
    let count = integer(lines.next(), 100_000)?;
    let indices = (0..count)
        .map(|_| integer(lines.next(), 99_999))
        .collect::<Result<_>>()?;
    let pairs = match mode {
        Mode::Inspect => Vec::new(),
        Mode::Request | Mode::Fourier => {
            let count = integer(
                lines.next(),
                if matches!(mode, Mode::Fourier) {
                    8
                } else {
                    100_000
                },
            )?;
            (0..count)
                .map(|_| integer(lines.next(), 99_999))
                .collect::<Result<_>>()?
        }
    };
    if lines.next() != Some("") || lines.next().is_some() {
        return Err(Error::format("trailing runtime response data"));
    }
    Ok(Response {
        work,
        indices,
        pairs,
    })
}

fn invoke(executable: &Path, bytes: Vec<u8>, mode: Mode) -> Result<Vec<u8>> {
    let mut child = Command::new(executable)
        .arg(mode.argument())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .map_err(|e| Error::new("io", format!("cannot start Lean runtime: {e}")))?;
    let mut stdin = child.stdin.take().unwrap();
    let stdout = child.stdout.take().unwrap();
    let writer = std::thread::spawn(move || stdin.write_all(&bytes));
    let reader = std::thread::spawn(move || {
        let mut output = Vec::new();
        stdout
            .take((mode.maximum() + 1) as u64)
            .read_to_end(&mut output)
            .map(|_| output)
    });
    let deadline = Instant::now() + Duration::from_secs(60);
    let status = loop {
        match child.try_wait() {
            Ok(Some(status)) => break Ok(status),
            Ok(None) if Instant::now() < deadline => std::thread::sleep(Duration::from_millis(10)),
            Ok(None) => {
                let _ = child.kill();
                let _ = child.wait();
                break Err(Error::limit("Lean runtime inspection timed out"));
            }
            Err(e) => {
                let _ = child.kill();
                let _ = child.wait();
                break Err(Error::new("io", format!("Lean runtime wait failed: {e}")));
            }
        }
    };
    let written = writer
        .join()
        .map_err(|_| Error::new("io", "runtime input thread failed"))?;
    let output = reader
        .join()
        .map_err(|_| Error::new("io", "runtime output thread failed"))?
        .map_err(|e| Error::new("io", format!("runtime output failed: {e}")))?;
    let status = status?;
    if output.len() > mode.maximum() {
        return Err(Error::limit("runtime response exceeds limit"));
    }
    if !status.success() {
        return match response_indices(&output, mode) {
            Err(error) => Err(error),
            Ok(_) => Err(Error::new("io", "failed runtime returned success data")),
        };
    }
    written.map_err(|e| Error::new("io", format!("runtime input failed: {e}")))?;
    Ok(output)
}
