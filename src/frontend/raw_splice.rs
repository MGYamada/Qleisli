//! Bounded, untrusted alpha-renaming of a checked unary body's identities.
//! The caller must independently check the emitted artifact and its equation.
use super::raw_state::RawState;
use crate::AcceptedProgram;
use crate::contract::{ContractError, exact::Budget};
use crate::ir::*;
use std::collections::BTreeMap;

pub(super) fn append<N>(
    state: &mut RawState<N>,
    body: &AcceptedProgram,
    input: &QuantumPort,
    budget: &mut Budget,
) -> Result<QuantumPort, ContractError> {
    let raw = body.raw();
    let ([original], [output]) = (raw.quantum_inputs.as_slice(), body.output_ports()) else {
        return Err(ContractError::Type(
            "spliced body requires one quantum input and output",
        ));
    };
    if !raw.classical_inputs.is_empty()
        || !raw.classical_outputs.is_empty()
        || original.shape != input.shape
        || original.wires.len() != input.wires.len()
    {
        return Err(ContractError::Type(
            "spliced body interface differs from the caller",
        ));
    }
    let mut renamer = Renamer {
        state,
        tokens: BTreeMap::from([(original.token, input.token)]),
        wires: original
            .wires
            .iter()
            .copied()
            .zip(input.wires.iter().copied())
            .collect(),
        classical: BTreeMap::new(),
    };
    // Native acceptance already bounds nesting; also bound work before cloning.
    budget.charge(body.artifact().len())?;
    let mut operations = raw.operations.clone();
    renamer.operations(&mut operations, 0, budget)?;
    let result = QuantumPort {
        token: renamer.token(output.token),
        wires: output.wires.iter().map(|w| renamer.wire(*w)).collect(),
        shape: output.shape,
    };
    renamer.state.operations.extend(operations);
    Ok(result)
}

struct Renamer<'a, N> {
    state: &'a mut RawState<N>,
    tokens: BTreeMap<TokenId, TokenId>,
    wires: BTreeMap<WireId, WireId>,
    classical: BTreeMap<ClassicalId, ClassicalId>,
}
impl<N> Renamer<'_, N> {
    fn token(&mut self, id: TokenId) -> TokenId {
        *self.tokens.entry(id).or_insert_with(|| self.state.token())
    }
    fn wire(&mut self, id: WireId) -> WireId {
        *self.wires.entry(id).or_insert_with(|| self.state.wire())
    }
    fn classical(&mut self, id: ClassicalId) -> ClassicalId {
        *self
            .classical
            .entry(id)
            .or_insert_with(|| self.state.classical())
    }
    fn operations(
        &mut self,
        operations: &mut [RawOp],
        depth: usize,
        budget: &mut Budget,
    ) -> Result<(), ContractError> {
        if depth > 32 {
            return Err(ContractError::Limit("spliced body exceeds depth 32"));
        }
        budget.charge(operations.len())?;
        for op in operations {
            match op {
                RawOp::PackUnit { output } => *output = self.token(*output),
                RawOp::UnpackUnit { input } | RawOp::Discard { input } => {
                    *input = self.token(*input)
                }
                RawOp::Init0 { output, wire } => {
                    *output = self.token(*output);
                    *wire = self.wire(*wire);
                }
                RawOp::Gate { input, output, .. } | RawOp::ApplyUnitary { input, output, .. } => {
                    *input = self.token(*input);
                    *output = self.token(*output);
                }
                RawOp::Cnot {
                    control,
                    target,
                    control_out,
                    target_out,
                }
                | RawOp::QuantumIf {
                    control,
                    target,
                    control_out,
                    target_out,
                    ..
                } => {
                    *control = self.token(*control);
                    *target = self.token(*target);
                    *control_out = self.token(*control_out);
                    *target_out = self.token(*target_out);
                }
                RawOp::Toffoli {
                    control_a,
                    control_b,
                    target,
                    control_a_out,
                    control_b_out,
                    target_out,
                } => {
                    *control_a = self.token(*control_a);
                    *control_b = self.token(*control_b);
                    *target = self.token(*target);
                    *control_a_out = self.token(*control_a_out);
                    *control_b_out = self.token(*control_b_out);
                    *target_out = self.token(*target_out);
                }
                RawOp::Split {
                    input, left, right, ..
                } => {
                    *input = self.token(*input);
                    *left = self.token(*left);
                    *right = self.token(*right);
                }
                RawOp::Join {
                    left,
                    right,
                    output,
                } => {
                    *left = self.token(*left);
                    *right = self.token(*right);
                    *output = self.token(*output);
                }
                RawOp::LiftBasis {
                    input,
                    output,
                    output_wires,
                    ..
                } => {
                    *input = self.token(*input);
                    *output = self.token(*output);
                    for wire in output_wires {
                        *wire = self.wire(*wire);
                    }
                }
                RawOp::MeasureZ { input, output } => {
                    *input = self.token(*input);
                    *output = self.classical(*output);
                }
                RawOp::Reset {
                    input,
                    output,
                    fresh_wire,
                } => {
                    *input = self.token(*input);
                    *output = self.token(*output);
                    *fresh_wire = self.wire(*fresh_wire);
                }
                RawOp::ClassicalConst { output, .. } => *output = self.classical(*output),
                RawOp::ClassicalNot { input, output } => {
                    *input = self.classical(*input);
                    *output = self.classical(*output);
                }
                RawOp::ClassicalXor {
                    left,
                    right,
                    output,
                }
                | RawOp::ClassicalAnd {
                    left,
                    right,
                    output,
                } => {
                    *left = self.classical(*left);
                    *right = self.classical(*right);
                    *output = self.classical(*output);
                }
                RawOp::ClassicalBranch {
                    condition,
                    then_ops,
                    else_ops,
                    quantum_phis,
                    classical_phis,
                } => {
                    *condition = self.classical(*condition);
                    self.operations(then_ops, depth + 1, budget)?;
                    self.operations(else_ops, depth + 1, budget)?;
                    for phi in quantum_phis {
                        phi.then_token = self.token(phi.then_token);
                        phi.else_token = self.token(phi.else_token);
                        phi.output = self.token(phi.output);
                        for wire in &mut phi.output_wires {
                            *wire = self.wire(*wire);
                        }
                    }
                    for phi in classical_phis {
                        phi.then_id = self.classical(phi.then_id);
                        phi.else_id = self.classical(phi.else_id);
                        phi.output = self.classical(phi.output);
                    }
                }
                RawOp::CertifiedCompute {
                    source,
                    source_out,
                    ancilla_wires,
                    ..
                } => {
                    *source = self.token(*source);
                    *source_out = self.token(*source_out);
                    for wire in ancilla_wires {
                        *wire = self.wire(*wire);
                    }
                }
                RawOp::ComputeUseUncompute {
                    source,
                    source_out,
                    targets,
                    ancilla_wires,
                    ..
                } => {
                    *source = self.token(*source);
                    *source_out = self.token(*source_out);
                    for target in targets {
                        target.input = self.token(target.input);
                        target.output = self.token(target.output);
                    }
                    for wire in ancilla_wires {
                        *wire = self.wire(*wire);
                    }
                }
            }
        }
        Ok(())
    }
}
