//! Independent host description of the fixed canonical target-byte profile.
//! This reader constructs untrusted data; only the separate native invocation
//! checks its equality to Lean's fresh target reader and instrument meaning.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use std::sync::Arc;

use super::super::{DecodedGraph, Error, Result, execution_view::finite::Graph};
use crate::ir::{
    BasisShape, CircuitAction, CircuitStep, ClassicalId, Effect, QuantumPort, RawOp, RawProgram,
    SingleGate, TokenId, WireId,
};

pub(super) const MAX_TARGET_BYTES: usize = 1024;
pub(super) const MAX_TARGET_GATES: usize = 8;
const HEADER: [&str; 5] = [
    "OPENQASM 3.0;",
    "include \"stdgates.inc\";",
    "qubit[1] q;",
    "bit[1] c;",
    "reset q;",
];

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Gate {
    H,
    X,
    Y,
    Z,
    S,
    Sdg,
    T,
    Tdg,
}

impl Gate {
    fn parse(line: &str) -> Result<Self> {
        match line {
            "h q[0];" => Ok(Self::H),
            "x q[0];" => Ok(Self::X),
            "y q[0];" => Ok(Self::Y),
            "z q[0];" => Ok(Self::Z),
            "s q[0];" => Ok(Self::S),
            "sdg q[0];" => Ok(Self::Sdg),
            "t q[0];" => Ok(Self::T),
            "tdg q[0];" => Ok(Self::Tdg),
            _ => Err(Error::format(
                "unsupported canonical one-qubit OpenQASM gate line",
            )),
        }
    }

    fn name(self) -> &'static str {
        match self {
            Self::H => "h",
            Self::X => "x",
            Self::Y => "y",
            Self::Z => "z",
            Self::S => "s",
            Self::Sdg => "sdg",
            Self::T => "t",
            Self::Tdg => "tdg",
        }
    }

    fn operation(self, input: TokenId, output: TokenId) -> RawOp {
        let simple = match self {
            Self::H => Some(SingleGate::H),
            Self::X => Some(SingleGate::X),
            Self::Z => Some(SingleGate::Z),
            Self::T => Some(SingleGate::T),
            _ => None,
        };
        if let Some(gate) = simple {
            return RawOp::Gate {
                gate,
                input,
                output,
            };
        }
        let (permutation, phases) = match self {
            Self::Y => (vec![1, 0], vec![2, 6]),
            Self::S => (vec![0, 1], vec![0, 2]),
            Self::Sdg => (vec![0, 1], vec![0, 6]),
            Self::Tdg => (vec![0, 1], vec![0, 7]),
            _ => unreachable!("simple gates returned above"),
        };
        RawOp::ApplyUnitary {
            input,
            output,
            steps: vec![CircuitStep {
                controls: vec![],
                action: CircuitAction::Monomial {
                    indices: vec![0],
                    permutation,
                    phases,
                },
            }],
        }
    }
}

#[derive(Debug)]
pub(super) struct Decoded {
    original: Arc<[u8]>,
    gates: Vec<Gate>,
    graph: DecodedGraph,
}

impl Decoded {
    pub(super) fn new(bytes: &[u8]) -> Result<Self> {
        if bytes.is_empty() || bytes.len() > MAX_TARGET_BYTES {
            return Err(Error::limit(
                "canonical OpenQASM target requires 1..1024 bytes",
            ));
        }
        if !bytes.is_ascii() {
            return Err(Error::format(
                "canonical OpenQASM target requires ASCII bytes",
            ));
        }
        let source = std::str::from_utf8(bytes)
            .map_err(|_| Error::format("canonical OpenQASM target requires ASCII bytes"))?;
        let lines = source.split('\n').collect::<Vec<_>>();
        if lines.len() < 7
            || !lines.starts_with(&HEADER)
            || lines.last() != Some(&"")
            || lines[lines.len() - 2] != "c[0] = measure q[0];"
        {
            return Err(Error::format(
                "canonical OpenQASM requires the exact one-qubit header, reset and terminal readout with a final newline",
            ));
        }
        let word = &lines[5..lines.len() - 2];
        if word.len() > MAX_TARGET_GATES {
            return Err(Error::limit(
                "canonical OpenQASM target exceeds eight gate lines",
            ));
        }
        let gates = word
            .iter()
            .map(|line| Gate::parse(line))
            .collect::<Result<Vec<_>>>()?;
        let mut operations = vec![
            RawOp::UnpackUnit { input: TokenId(0) },
            RawOp::Init0 {
                output: TokenId(1),
                wire: WireId(0),
            },
        ];
        let mut owner = TokenId(1);
        for gate in &gates {
            let next = TokenId(owner.0 + 1);
            operations.push(gate.operation(owner, next));
            owner = next;
        }
        operations.push(RawOp::MeasureZ {
            input: owner,
            output: ClassicalId(0),
        });
        let root = Arc::new(RawProgram {
            quantum_inputs: vec![QuantumPort {
                token: TokenId(0),
                wires: vec![],
                shape: BasisShape::UNIT,
            }],
            classical_inputs: vec![],
            operations,
            quantum_outputs: vec![],
            classical_outputs: vec![ClassicalId(0)],
            declared_effect: Effect::Observe,
        });
        Ok(Self {
            original: Arc::from(bytes),
            gates,
            graph: DecodedGraph {
                programs: vec![root],
                evidence: vec![],
                root: 0,
                interface: None,
                sources: vec![],
            },
        })
    }

    pub(super) fn original(&self) -> &[u8] {
        &self.original
    }

    pub(super) fn gate_word(&self) -> impl ExactSizeIterator<Item = &'static str> + '_ {
        self.gates.iter().map(|gate| gate.name())
    }

    pub(super) fn graph(&self) -> Graph<'_> {
        Graph {
            graph: &self.graph,
            root: &self.graph.programs[0],
            interface: None,
            effect: Effect::Observe,
            outputs: &[],
        }
    }
}
