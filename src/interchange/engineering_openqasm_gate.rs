//! Phase-sensitive engineering bounds and literal costs for ordered OpenQASM gates.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0

use std::path::{Path, PathBuf};
use std::time::Duration;

use super::codec::Codec;
use super::engineering_openqasm::GateCounts;
use super::engineering_pure::{DyadicBound, decode_dyadic};
use super::json::{self, Value};
use super::native::Kernel;
use super::native_context::{self, Mode};
use super::native_packet::{self, Scope, View};
use super::{Error, Result};
use crate::AcceptedProgram;
use crate::contract::exact::{Budget, Matrix};
use crate::contract::{BasisType, DEFAULT_EXACT_WORK};
use crate::edition::Edition;
use crate::ir::QuantumPort;

pub(super) const FORMAT: &str = "qleisli.engineering-openqasm-gate-request";
pub(super) const CLAIM_KIND: &str = "engineering-target-operator-resource-bound";
pub(super) const METRIC: &str = "pure-euclidean-operator-norm-v1";
pub(super) const CHECKER_PROFILE: &str = "canonical-gate-frobenius-r8-v1";
pub(super) const TARGET_PROFILE: &str = "openqasm3-canonical-ordered-gate-r8-v1";
pub(super) const SEQUENTIAL: &str = "ordered-sequential-two-v1";
pub(super) const CONTROLLED: &str = "controlled-low-selector-v1";
pub(super) const ERROR_CATEGORY: &str = "implementation-distance";
pub const RESOURCE_MODEL: &str = "openqasm3-ordered-gate-literal-gates-v1";
pub const MAX_TARGET_BYTES: usize = 1024;
const MAX_GATES: usize = 8;
const MAX_FILE_BYTES: usize = 16 << 20;
const HEADER: &str = "OPENQASM 3.0;\ninclude \"stdgates.inc\";\n";

#[derive(Debug)]
pub(super) struct Ideal {
    pub(super) input: QuantumPort,
    pub(super) output: QuantumPort,
    pub(super) matrix: Matrix,
    pub(super) program: AcceptedProgram,
}

impl Ideal {
    fn read(value: &Value, kernel: &Kernel, budget: &mut Budget) -> Result<Self> {
        value.fields(&["leaf", "expected_artifact"])?;
        let leaf = value.field("leaf")?;
        leaf.fields(&["input", "output", "matrix"])?;
        let decoder = super::Decoder { evidence: &[] };
        let input = QuantumPort::read(leaf.field("input")?, &decoder)?;
        let output = QuantumPort::read(leaf.field("output")?, &decoder)?;
        let matrix = super::finite_matrix::decode(&json::encode(leaf.field("matrix")?)?, budget)?;
        let original = value.field("expected_artifact")?.text()?.as_bytes();
        check_file(original)?;
        let program = kernel.check(original, None)?.into_program();
        Ok(Self {
            input,
            output,
            matrix,
            program,
        })
    }
}

#[derive(Debug)]
pub(super) enum Contract {
    Sequential {
        split: usize,
        epsilons: [DyadicBound; 2],
        ideals: Box<[Ideal; 2]>,
    },
    Controlled(Box<Ideal>),
}

impl Contract {
    pub(super) fn ideals(&self) -> &[Ideal] {
        match self {
            Self::Sequential { ideals, .. } => &ideals[..],
            Self::Controlled(ideal) => std::slice::from_ref(ideal.as_ref()),
        }
    }

    fn composition(&self) -> &'static str {
        match self {
            Self::Sequential { .. } => SEQUENTIAL,
            Self::Controlled(_) => CONTROLLED,
        }
    }
}

#[derive(Debug)]
pub(super) struct Request {
    pub(super) epsilon: DyadicBound,
    pub(super) limits: GateCounts,
    pub(super) contract: Contract,
}

fn check_file(bytes: &[u8]) -> Result<()> {
    if bytes.is_empty() || bytes.len() > MAX_FILE_BYTES {
        return Err(Error::limit(
            "engineering gate request and ideal require 1..16777216 bytes",
        ));
    }
    Ok(())
}

impl Request {
    fn read(bytes: &[u8], kernel: &Kernel) -> Result<Self> {
        check_file(bytes)?;
        let value = json::parse(bytes)?;
        let composition = value.field("composition")?.text()?;
        let mut fields = vec![
            "format",
            "version",
            "claim_kind",
            "metric",
            "checker_profile",
            "target_profile",
            "composition",
            "error_category",
            "epsilon",
            "resource_limits",
        ];
        fields.extend_from_slice(match composition {
            SEQUENTIAL => &["split", "first", "second"],
            CONTROLLED => &["ideal"],
            _ => return Err(Error::format("unknown engineering gate composition")),
        });
        value.fields(&fields)?;
        if value.field("version")?.number()? != 1 {
            return Err(Error::format("unknown engineering gate request version"));
        }
        for (name, expected) in [
            ("format", FORMAT),
            ("claim_kind", CLAIM_KIND),
            ("metric", METRIC),
            ("checker_profile", CHECKER_PROFILE),
            ("target_profile", TARGET_PROFILE),
            ("error_category", ERROR_CATEGORY),
        ] {
            if value.field(name)?.text()? != expected {
                return Err(Error::format(format!("unknown engineering gate {name}")));
            }
        }
        let epsilon = decode_dyadic(value.field("epsilon")?)?;
        let limits = value.field("resource_limits")?;
        limits.fields(&["model", "gates", "t_gates"])?;
        if limits.field("model")?.text()? != RESOURCE_MODEL {
            return Err(Error::format("unknown engineering gate resource model"));
        }
        let count = |field| {
            let n = limits.field(field)?.number()?;
            if n > MAX_GATES as u64 {
                return Err(Error::limit(
                    "engineering gate limits must be at most eight",
                ));
            }
            Ok(n as usize)
        };
        let limits = GateCounts {
            gates: count("gates")?,
            t_gates: count("t_gates")?,
        };
        let mut budget = Budget::new(DEFAULT_EXACT_WORK);
        let contract = if composition == SEQUENTIAL {
            let split = value.field("split")?.number()?;
            if split > MAX_GATES as u64 {
                return Err(Error::limit("engineering gate split must be at most eight"));
            }
            let mut component = |name| {
                let data = value.field(name)?;
                data.fields(&["ideal", "epsilon"])?;
                let epsilon = decode_dyadic(data.field("epsilon")?)?;
                let ideal = Ideal::read(data.field("ideal")?, kernel, &mut budget)?;
                Ok::<_, Error>((ideal, epsilon))
            };
            let (first, first_epsilon) = component("first")?;
            let (second, second_epsilon) = component("second")?;
            Contract::Sequential {
                split: split as usize,
                epsilons: [first_epsilon, second_epsilon],
                ideals: Box::new([first, second]),
            }
        } else {
            Contract::Controlled(Box::new(Ideal::read(
                value.field("ideal")?,
                kernel,
                &mut budget,
            )?))
        };
        Ok(Self {
            epsilon,
            limits,
            contract,
        })
    }
}

pub(super) struct Target<'a> {
    pub(super) bytes: &'a [u8],
    pub(super) basis: BasisType,
    pub(super) gates: Vec<Gate<'a>>,
    wires: usize,
}

pub(super) struct Gate<'a> {
    pub(super) name: &'a str,
    pub(super) wires: &'static [usize],
}

impl<'a> Target<'a> {
    fn read(bytes: &'a [u8]) -> Result<Self> {
        if bytes.len() > MAX_TARGET_BYTES {
            return Err(Error::limit("engineering gate target exceeds 1024 bytes"));
        }
        let bad = || Error::format("expected a canonical ordered OpenQASM gate definition");
        let body = std::str::from_utf8(bytes)
            .ok()
            .and_then(|text| text.strip_prefix(HEADER))
            .and_then(|text| text.strip_suffix('\n'))
            .ok_or_else(bad)?;
        let mut lines = body.split('\n');
        let (wires, basis) = match lines.next() {
            Some("gate implementation a {") => (1, BasisType::Bit),
            Some("gate implementation a, b {") => (
                2,
                BasisType::Pair(Box::new(BasisType::Bit), Box::new(BasisType::Bit)),
            ),
            _ => return Err(bad()),
        };
        if lines.next_back() != Some("}") {
            return Err(bad());
        }
        let mut gates = Vec::new();
        for line in lines {
            if gates.len() == MAX_GATES {
                return Err(Error::limit("engineering gate target exceeds eight gates"));
            }
            let (name, operands) = line.split_once(' ').ok_or_else(bad)?;
            let arity = match name {
                "h" | "x" | "y" | "z" | "s" | "sdg" | "t" | "tdg" => 1,
                "cx" | "cz" | "swap" => 2,
                _ => return Err(bad()),
            };
            let operands: &[usize] = match operands {
                "a;" => &[0],
                "b;" => &[1],
                "a, b;" => &[0, 1],
                "b, a;" => &[1, 0],
                _ => return Err(bad()),
            };
            if operands.len() != arity || operands.iter().any(|&wire| wire >= wires) {
                return Err(bad());
            }
            gates.push(Gate {
                name,
                wires: operands,
            });
        }
        Ok(Self {
            bytes,
            basis,
            gates,
            wires,
        })
    }

    fn counts(&self) -> GateCounts {
        GateCounts {
            gates: self.gates.len(),
            t_gates: self
                .gates
                .iter()
                .filter(|gate| matches!(gate.name, "t" | "tdg"))
                .count(),
        }
    }
}

/// An engineering report for the original gate definition, ordered ideal
/// artifacts, error contract and decoded literal counts checked together.
///
/// ```compile_fail
/// use qleisli::{AcceptedProgram, interchange::engineering_openqasm_gate::EngineeringOpenQasmGateReport};
/// fn promote(report: EngineeringOpenQasmGateReport) -> AcceptedProgram { report.into() }
/// ```
#[derive(Debug)]
pub struct EngineeringOpenQasmGateReport {
    context: native_context::CheckedContext,
    target: Box<[u8]>,
    request: Request,
    request_bytes: Box<[u8]>,
    checker: PathBuf,
    exact_work: usize,
    wires: usize,
    counts: GateCounts,
}

impl EngineeringOpenQasmGateReport {
    pub fn edition(&self) -> Edition {
        self.context.edition()
    }
    pub fn target_bytes(&self) -> &[u8] {
        &self.target
    }
    pub fn request_bytes(&self) -> &[u8] {
        &self.request_bytes
    }
    pub fn ideal_artifacts(&self) -> impl ExactSizeIterator<Item = &[u8]> {
        self.request
            .contract
            .ideals()
            .iter()
            .map(|ideal| ideal.program.artifact())
    }
    pub fn exact_work(&self) -> usize {
        self.exact_work
    }
    /// Canonical selected path, without native binary attestation.
    pub fn checker(&self) -> &Path {
        &self.checker
    }
    pub fn metric(&self) -> &'static str {
        METRIC
    }
    pub fn claim_kind(&self) -> &'static str {
        CLAIM_KIND
    }
    pub fn composition(&self) -> &'static str {
        self.request.contract.composition()
    }
    pub fn checker_profile(&self) -> &'static str {
        CHECKER_PROFILE
    }
    pub fn target_profile(&self) -> &'static str {
        TARGET_PROFILE
    }
    pub fn error_category(&self) -> &'static str {
        ERROR_CATEGORY
    }
    pub fn epsilon(&self) -> DyadicBound {
        self.request.epsilon
    }
    pub fn sequential(&self) -> Option<(usize, [DyadicBound; 2])> {
        match &self.request.contract {
            Contract::Sequential {
                split, epsilons, ..
            } => Some((*split, *epsilons)),
            Contract::Controlled(_) => None,
        }
    }
    pub fn resource_limits(&self) -> GateCounts {
        self.request.limits
    }
    pub fn checked_gate_counts(&self) -> GateCounts {
        self.counts
    }
    pub fn wires(&self) -> usize {
        self.wires
    }
}

/// Check an independently supplied finite ideal and the actual target gate
/// definition in a fresh native engineering invocation.
pub fn compare_serialized_with_kernel(
    kernel: &Kernel,
    target_bytes: &[u8],
    request_bytes: &[u8],
) -> Result<EngineeringOpenQasmGateReport> {
    let target = Target::read(target_bytes)?;
    let request = Request::read(request_bytes, kernel)?;
    let checker = std::fs::canonicalize(kernel.checker_path())
        .map_err(|error| Error::new("io", format!("cannot resolve Lean checker: {error}")))?;
    let edition = kernel.edition();
    let graph =
        super::execution_view::finite::engineering_openqasm_gate::complete(&request, &target)?;
    let mut original = Vec::with_capacity(12 + target_bytes.len() + request_bytes.len());
    original.extend_from_slice(b"QLV1");
    original.extend_from_slice(&(target_bytes.len() as u32).to_le_bytes());
    original.extend_from_slice(&(request_bytes.len() as u32).to_le_bytes());
    original.extend_from_slice(target_bytes);
    original.extend_from_slice(request_bytes);
    let (packet, scope) = native_packet::encode(
        edition,
        &original,
        Some(View {
            graph: &graph,
            caller: None,
        }),
    )?;
    if scope != Scope::Execution {
        return Err(Error::format(
            "engineering gate check requires execution scope",
        ));
    }
    let mode = Mode::EngineeringOpenQasmGate;
    let (context, exact_work, wires, counts) = super::process::invoke(
        &checker,
        packet,
        mode.argument(),
        Duration::from_secs(60),
        256,
        |bytes| {
            let (context, payload) = native_context::engineering_payload(bytes, edition, mode)?;
            let [work, wires, gates, t_gates] = payload.as_slice() else {
                return Err(Error::format("malformed engineering gate response"));
            };
            let count = native_context::engineering_count;
            let exact_work = count(work, "work count", DEFAULT_EXACT_WORK)?;
            let wires = count(wires, "wire count", 2)?;
            let counts = GateCounts {
                gates: count(gates, "gate count", MAX_GATES)?,
                t_gates: count(t_gates, "T gate count", MAX_GATES)?,
            };
            if wires != target.wires
                || counts != target.counts()
                || counts.gates > request.limits.gates
                || counts.t_gates > request.limits.t_gates
            {
                return Err(Error::format(
                    "engineering gate counts disagree with the invocation",
                ));
            }
            Ok((context, exact_work, wires, counts))
        },
    )?;
    Ok(EngineeringOpenQasmGateReport {
        context,
        target: target_bytes.into(),
        request,
        request_bytes: request_bytes.into(),
        checker,
        exact_work,
        wires,
        counts,
    })
}
