//! Independent import of a narrow, already ownership-checked raw-IR profile.
//!
//! The imported type describes the concatenated ordered physical wires, not a
//! source type tree: `BasisShape` cannot recover that tree. Zero-width owners,
//! port partitions, and SSA identities remain checked by the ordinary verifier
//! and retained in the exact raw snapshot. Encoded operator evidence grants no
//! runtime entry assertion, allocation, or auxiliary-release capability.

use std::collections::BTreeMap;
use std::fmt;

use qleisli_core::ir::{
    CircuitAction, CircuitStep, Effect, RawOp, RawProgram, SingleGate, TokenId, WireId,
};

use crate::kernel::{
    CheckedEvidence, Limits, ProofId, ProofRule, RequiredContract, Term, TermGraph, TermId, TypeId,
    TypeNode, check,
};

const MAX_IMPORT_BITS: usize = 4096;
const MAX_IMPORT_PORTS: usize = 4096;
const MAX_IMPORT_OPERATIONS: usize = 10_000;
const MAX_IMPORT_STEPS: usize = 10_000;
const MAX_IMPORT_TRANSPORT_WORK: usize = 1_000_000;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AdapterError {
    Limit(&'static str),
    Unsupported(&'static str),
    InvalidIr(String),
    Binding(&'static str),
    Kernel(String),
}

impl fmt::Display for AdapterError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Limit(message) | Self::Unsupported(message) | Self::Binding(message) => {
                f.write_str(message)
            }
            Self::InvalidIr(message) | Self::Kernel(message) => f.write_str(message),
        }
    }
}

impl std::error::Error for AdapterError {}

/// A verified raw snapshot and its independently imported implementation term.
/// The returned graph may be extended with a separately specified contract and
/// proof. Its imported prefix must not be changed at the checking boundary.
#[derive(Clone, Debug)]
pub struct ImportedProgram {
    raw: RawProgram,
    graph: TermGraph,
    implementation: TermId,
    space: TypeId,
    input_wires: Vec<WireId>,
    output_wires: Vec<WireId>,
}

impl ImportedProgram {
    pub fn graph(&self) -> &TermGraph {
        &self.graph
    }

    pub fn implementation(&self) -> TermId {
        self.implementation
    }

    pub fn space(&self) -> TypeId {
        self.space
    }

    pub fn input_wires(&self) -> &[WireId] {
        &self.input_wires
    }

    pub fn output_wires(&self) -> &[WireId] {
        &self.output_wires
    }

    pub fn raw(&self) -> &RawProgram {
        &self.raw
    }

    /// Bind an independently requested meaning to this exact imported program.
    pub fn check(
        &self,
        graph: &TermGraph,
        proofs: &[ProofRule],
        root: ProofId,
        required: &RequiredContract,
        limits: Limits,
    ) -> Result<BoundProgram, AdapterError> {
        if graph.types.get(..self.graph.types.len()) != Some(self.graph.types.as_slice())
            || graph.terms.get(..self.graph.terms.len()) != Some(self.graph.terms.as_slice())
        {
            return Err(AdapterError::Binding("the imported graph prefix changed"));
        }
        if required.contract().implementation != self.implementation {
            return Err(AdapterError::Binding(
                "the requested proof is for a different implementation root",
            ));
        }
        let evidence = check(graph, proofs, root, required, limits)
            .map_err(|error| AdapterError::Kernel(error.to_string()))?;
        Ok(BoundProgram {
            raw: self.raw.clone(),
            evidence,
        })
    }
}

/// Operator evidence bound to the complete imported raw snapshot.
/// This object is deliberately not an execution or pure-release API.
#[derive(Debug)]
pub struct BoundProgram {
    raw: RawProgram,
    evidence: CheckedEvidence,
}

impl BoundProgram {
    pub fn raw(&self) -> &RawProgram {
        &self.raw
    }

    pub fn evidence(&self) -> &CheckedEvidence {
        &self.evidence
    }

    pub fn check_binding(&self, raw: &RawProgram) -> Result<(), AdapterError> {
        if raw != &self.raw {
            return Err(AdapterError::Binding(
                "the complete raw-IR snapshot changed",
            ));
        }
        Ok(())
    }
}

struct Builder {
    graph: TermGraph,
    widths: Vec<TypeId>,
}

impl Builder {
    fn new(bits: usize) -> Self {
        let mut graph = TermGraph {
            types: vec![TypeNode::Unit, TypeNode::Bit],
            terms: vec![],
        };
        let mut widths = vec![TypeId(0), TypeId(1)];
        // This right-associated physical type fixes a low first bit and its
        // remaining frame. Type nodes reference earlier nodes; no recursive
        // allocation or type traversal is needed even for many ports.
        for width in 2..=bits {
            let low = TypeId(1);
            let high = widths[width - 1];
            let id = TypeId(graph.types.len());
            graph.types.push(TypeNode::Pair { low, high });
            widths.push(id);
        }
        Self { graph, widths }
    }

    fn ty(&mut self, node: TypeNode) -> TypeId {
        if let Some(index) = self.graph.types.iter().position(|old| *old == node) {
            TypeId(index)
        } else {
            let id = TypeId(self.graph.types.len());
            self.graph.types.push(node);
            id
        }
    }

    fn term(&mut self, term: Term) -> TermId {
        if let Some(index) = self.graph.terms.iter().position(|old| *old == term) {
            TermId(index)
        } else {
            let id = TermId(self.graph.terms.len());
            self.graph.terms.push(term);
            id
        }
    }

    fn seq(&mut self, first: TermId, second: TermId) -> TermId {
        self.term(Term::Sequence { first, second })
    }

    fn primitive(&mut self, gate: SingleGate) -> TermId {
        self.term(match gate {
            SingleGate::H => Term::H,
            SingleGate::X => Term::X,
            SingleGate::Z => Term::Z,
            SingleGate::T => Term::T,
        })
    }

    /// Bring the selected low-first axes together, apply the local operator
    /// tensor identity, and restore the complete global interface.
    fn embed(&mut self, operand: TermId, local: TypeId, axes: &[usize], total: usize) -> TermId {
        let whole = self.widths[total];
        if local == whole && axes.iter().copied().eq(0..total) {
            return operand;
        }
        let rest = self.widths[total - axes.len()];
        let joined = self.ty(TypeNode::Pair {
            low: local,
            high: rest,
        });
        let mut gather = axes.to_vec();
        gather.extend((0..total).filter(|axis| !axes.contains(axis)));
        let identity = self.term(Term::Identity { space: rest });
        let action = self.term(Term::Tensor {
            low: operand,
            high: identity,
        });
        if joined == whole && gather.iter().copied().eq(0..total) {
            return action;
        }
        let mut scatter = vec![0; total];
        for (position, axis) in gather.iter().copied().enumerate() {
            scatter[axis] = position;
        }
        let before = self.term(Term::Rewire {
            input: whole,
            output: joined,
            output_axes: gather,
        });
        let after = self.term(Term::Rewire {
            input: joined,
            output: whole,
            output_axes: scatter,
        });
        let applied = self.seq(before, action);
        self.seq(applied, after)
    }

    fn step(
        &mut self,
        step: &CircuitStep,
        register: &[usize],
        total: usize,
    ) -> Result<TermId, AdapterError> {
        let (mut action, mut local, target_axes) = match &step.action {
            CircuitAction::Hadamard { target } => {
                (self.term(Term::H), TypeId(1), vec![register[*target]])
            }
            CircuitAction::Monomial {
                indices,
                permutation,
                phases,
            } => {
                let axes: Vec<_> = indices.iter().map(|index| register[*index]).collect();
                match indices.len() {
                    0 => (
                        self.term(Term::Phase {
                            space: TypeId(0),
                            eighths: phases[0],
                        }),
                        TypeId(0),
                        axes,
                    ),
                    1 => {
                        let phase = self.term(Term::Phase {
                            space: TypeId(1),
                            eighths: phases[0],
                        });
                        let t = self.term(Term::T);
                        let relative = self.term(Term::Repeat {
                            operand: t,
                            count: u64::from((phases[1] + 8 - phases[0]) % 8),
                        });
                        let mut operator = self.seq(phase, relative);
                        if permutation == &[1, 0] {
                            let x = self.term(Term::X);
                            operator = self.seq(operator, x);
                        }
                        (operator, TypeId(1), axes)
                    }
                    2 if permutation == &[0, 3, 2, 1] && phases == &[0, 0, 0, 0] => {
                        let local = self.ty(TypeNode::Pair {
                            low: TypeId(1),
                            high: TypeId(1),
                        });
                        (self.term(Term::Cnot), local, axes)
                    }
                    _ => {
                        return Err(AdapterError::Unsupported(
                            "unsupported monomial in adapter profile",
                        ));
                    }
                }
            }
            CircuitAction::Contract { .. } => {
                return Err(AdapterError::Unsupported(
                    "legacy dense function evidence is unsupported",
                ));
            }
        };
        for _ in step.controls.iter().rev() {
            action = self.term(Term::Controlled { operand: action });
            local = self.ty(TypeNode::Pair {
                low: TypeId(1),
                high: local,
            });
        }
        let mut axes: Vec<_> = step
            .controls
            .iter()
            .map(|control| register[control.index])
            .collect();
        axes.extend(target_axes);
        let controlled = self.embed(action, local, &axes, total);
        let mut result = controlled;
        // Conjugate each zero control by X; these axes are distinct and do not
        // overlap action axes, as already checked by the ordinary verifier.
        for control in step.controls.iter().filter(|control| !control.when_one) {
            let x = self.term(Term::X);
            let flip = self.embed(x, TypeId(1), &[register[control.index]], total);
            let first = self.seq(flip, result);
            result = self.seq(first, flip);
        }
        Ok(result)
    }
}

fn preflight(raw: &RawProgram) -> Result<usize, AdapterError> {
    if raw.quantum_inputs.len() > MAX_IMPORT_PORTS
        || raw.quantum_outputs.len() > MAX_IMPORT_PORTS
        || raw.operations.len() > MAX_IMPORT_OPERATIONS
    {
        return Err(AdapterError::Limit(
            "raw import port/operation limit exceeded",
        ));
    }
    if raw.declared_effect != Effect::Unitary
        || !raw.classical_inputs.is_empty()
        || !raw.classical_outputs.is_empty()
    {
        return Err(AdapterError::Unsupported(
            "adapter requires a declared unitary quantum-only interface",
        ));
    }
    let mut bits = 0usize;
    for port in &raw.quantum_inputs {
        bits = bits
            .checked_add(port.wires.len())
            .ok_or(AdapterError::Limit("raw import width overflow"))?;
        if bits > MAX_IMPORT_BITS {
            return Err(AdapterError::Limit(
                "raw import physical-width limit exceeded",
            ));
        }
    }
    let mut count = 0usize;
    for operation in &raw.operations {
        match operation {
            RawOp::Gate { .. }
            | RawOp::Cnot { .. }
            | RawOp::Toffoli { .. }
            | RawOp::Split { .. }
            | RawOp::Join { .. } => {}
            RawOp::ApplyUnitary { steps, .. } => {
                count = count
                    .checked_add(steps.len())
                    .ok_or(AdapterError::Limit("raw import step overflow"))?;
                if count > MAX_IMPORT_STEPS {
                    return Err(AdapterError::Limit(
                        "raw import circuit-step limit exceeded",
                    ));
                }
                for step in steps {
                    if step.controls.len() > 12 {
                        return Err(AdapterError::Limit("raw import control limit exceeded"));
                    }
                    match &step.action {
                        CircuitAction::Hadamard { .. } => {}
                        CircuitAction::Monomial {
                            indices,
                            permutation,
                            phases,
                        } if indices.len() <= 2 && permutation.len() <= 4 && phases.len() <= 4 => {}
                        CircuitAction::Monomial { .. } => {
                            return Err(AdapterError::Unsupported(
                                "monomial exceeds the adapter's local profile",
                            ));
                        }
                        CircuitAction::Contract { .. } => {
                            return Err(AdapterError::Unsupported(
                                "legacy dense function evidence is unsupported",
                            ));
                        }
                    }
                }
            }
            _ => {
                return Err(AdapterError::Unsupported(
                    "raw operation is outside the unitary adapter profile",
                ));
            }
        }
    }
    // Reject expensive transports before graph construction. The factor 26
    // covers a controlled action and both X placements for twelve zero controls.
    let estimated = bits
        .max(1)
        .checked_mul(raw.operations.len().saturating_add(count))
        .and_then(|work| work.checked_mul(26))
        .ok_or(AdapterError::Limit("raw import transport-work overflow"))?;
    if estimated > MAX_IMPORT_TRANSPORT_WORK {
        return Err(AdapterError::Limit(
            "raw import transport-work limit exceeded",
        ));
    }
    Ok(bits)
}

/// Import supported raw IR after independent resource/effect verification.
/// A bounded shape-only preflight rejects unsupported constructors before the
/// legacy verifier could invoke their dense semantic checking paths.
pub fn import_raw(raw: RawProgram) -> Result<ImportedProgram, AdapterError> {
    let bits = preflight(&raw)?;
    let verified =
        qleisli_core::verify(raw).map_err(|error| AdapterError::InvalidIr(error.to_string()))?;
    let raw = verified.raw();
    let mut builder = Builder::new(bits);
    let space = builder.widths[bits];
    let mut implementation = None;
    let input_wires: Vec<_> = raw
        .quantum_inputs
        .iter()
        .flat_map(|port| port.wires.iter().copied())
        .collect();
    let axis: BTreeMap<_, _> = input_wires
        .iter()
        .copied()
        .enumerate()
        .map(|(index, wire)| (wire, index))
        .collect();
    let mut live: BTreeMap<TokenId, Vec<WireId>> = raw
        .quantum_inputs
        .iter()
        .map(|port| (port.token, port.wires.clone()))
        .collect();
    for operation in &raw.operations {
        let next = match operation {
            RawOp::Gate {
                gate,
                input,
                output,
            } => {
                let wires = live.remove(input).expect("verified live gate input");
                let gate = builder.primitive(*gate);
                let action = builder.embed(gate, TypeId(1), &[axis[&wires[0]]], bits);
                live.insert(*output, wires);
                Some(action)
            }
            RawOp::Cnot {
                control,
                target,
                control_out,
                target_out,
            } => {
                let c = live.remove(control).expect("verified CNOT control");
                let t = live.remove(target).expect("verified CNOT target");
                let gate = builder.term(Term::Cnot);
                let local = builder.ty(TypeNode::Pair {
                    low: TypeId(1),
                    high: TypeId(1),
                });
                let action = builder.embed(gate, local, &[axis[&c[0]], axis[&t[0]]], bits);
                live.insert(*control_out, c);
                live.insert(*target_out, t);
                Some(action)
            }
            RawOp::Toffoli {
                control_a,
                control_b,
                target,
                control_a_out,
                control_b_out,
                target_out,
            } => {
                let a = live.remove(control_a).expect("verified Toffoli control");
                let b = live.remove(control_b).expect("verified Toffoli control");
                let t = live.remove(target).expect("verified Toffoli target");
                let cnot = builder.term(Term::Cnot);
                let gate = builder.term(Term::Controlled { operand: cnot });
                let pair = builder.ty(TypeNode::Pair {
                    low: TypeId(1),
                    high: TypeId(1),
                });
                let local = builder.ty(TypeNode::Pair {
                    low: TypeId(1),
                    high: pair,
                });
                let action =
                    builder.embed(gate, local, &[axis[&a[0]], axis[&b[0]], axis[&t[0]]], bits);
                live.insert(*control_a_out, a);
                live.insert(*control_b_out, b);
                live.insert(*target_out, t);
                Some(action)
            }
            RawOp::Split {
                input,
                left,
                right,
                left_bits,
            } => {
                let mut wires = live.remove(input).expect("verified split input");
                let tail = wires.split_off(usize::from(*left_bits));
                live.insert(*left, wires);
                live.insert(*right, tail);
                None
            }
            RawOp::Join {
                left,
                right,
                output,
            } => {
                let mut wires = live.remove(left).expect("verified join input");
                wires.extend(live.remove(right).expect("verified join input"));
                live.insert(*output, wires);
                None
            }
            RawOp::ApplyUnitary {
                input,
                output,
                steps,
            } => {
                let wires = live.remove(input).expect("verified circuit input");
                let register: Vec<_> = wires.iter().map(|wire| axis[wire]).collect();
                for step in steps {
                    let action = builder.step(step, &register, bits)?;
                    implementation = Some(match implementation {
                        Some(first) => builder.seq(first, action),
                        None => action,
                    });
                }
                live.insert(*output, wires);
                None
            }
            _ => {
                return Err(AdapterError::Unsupported(
                    "raw operation is outside the unitary adapter profile",
                ));
            }
        };
        if let Some(action) = next {
            implementation = Some(match implementation {
                Some(first) => builder.seq(first, action),
                None => action,
            });
        }
    }
    let output_wires: Vec<_> = raw
        .quantum_outputs
        .iter()
        .flat_map(|token| live[token].iter().copied())
        .collect();
    let output_axes: Vec<_> = output_wires.iter().map(|wire| axis[wire]).collect();
    if !output_axes.iter().copied().eq(0..bits) {
        let order = builder.term(Term::Rewire {
            input: space,
            output: space,
            output_axes,
        });
        implementation = Some(match implementation {
            Some(first) => builder.seq(first, order),
            None => order,
        });
    }
    let implementation = implementation.unwrap_or_else(|| builder.term(Term::Identity { space }));
    Ok(ImportedProgram {
        raw: raw.clone(),
        graph: builder.graph,
        implementation,
        space,
        input_wires,
        output_wires,
    })
}

#[cfg(test)]
#[path = "adapter_tests.rs"]
mod tests;
