//! Conversion of independently verified unary unitaries to flat finite circuits.
use super::*;
use crate::ir::*;

pub(super) fn size(step: &CircuitStep) -> usize {
    1 + step.controls.len()
        + match &step.action {
            CircuitAction::Contract { indices, .. } => indices.len() + 1,
            CircuitAction::Hadamard { .. } => 1,
            CircuitAction::Monomial {
                indices,
                permutation,
                phases,
            } => indices.len() + permutation.len() + phases.len(),
        }
}

pub(super) fn gate(gate: SingleGate, target: usize) -> CircuitStep {
    CircuitStep {
        controls: vec![],
        action: match gate {
            SingleGate::H => CircuitAction::Hadamard { target },
            _ => CircuitAction::Monomial {
                indices: vec![target],
                permutation: if gate == SingleGate::X {
                    vec![1, 0]
                } else {
                    vec![0, 1]
                },
                phases: vec![
                    0,
                    match gate {
                        SingleGate::Z => 4,
                        SingleGate::T => 1,
                        _ => 0,
                    },
                ],
            },
        },
    }
}

pub(super) fn remap(step: &mut CircuitStep, axes: &[usize]) {
    for control in &mut step.controls {
        control.index = axes[control.index];
    }
    match &mut step.action {
        CircuitAction::Contract { indices, .. } => {
            for index in indices {
                *index = axes[*index];
            }
        }
        CircuitAction::Hadamard { target } => *target = axes[*target],
        CircuitAction::Monomial { indices, .. } => {
            for index in indices {
                *index = axes[*index];
            }
        }
    }
}

pub(super) fn invert(steps: &mut [CircuitStep]) {
    crate::contract::invert_steps(steps);
}

pub(super) fn flatten(
    compiler: &mut Compiler<'_>,
    module: &str,
    span: Span,
    verified: &VerifiedProgram,
) -> Result<Vec<CircuitStep>, CompileError> {
    let raw = verified.program();
    let port = &raw.quantum_inputs[0];
    let width = port.wires.len();
    let mut registers = BTreeMap::from([(port.token, (0..width).collect::<Vec<_>>())]);
    let mut steps = Vec::new();
    let mut classical = BTreeMap::new();
    flatten_ops(
        compiler,
        module,
        span,
        &raw.operations,
        &mut registers,
        &mut classical,
        &mut steps,
    )?;
    // Rebind the result to the input axis order. Reordered ownership is part
    // of the function's operator and must participate in adjoint and control.
    let axes = &registers[&raw.quantum_outputs[0]];
    if axes.iter().copied().ne(0..width) {
        compiler.charge(module, span, (1 << width) * (width + 2))?;
        let permutation = (0..1usize << width)
            .map(|label| {
                axes.iter().enumerate().fold(0u16, |out, (place, axis)| {
                    out | ((((label >> axis) & 1) as u16) << place)
                })
            })
            .collect();
        steps.push(CircuitStep {
            controls: vec![],
            action: CircuitAction::Monomial {
                indices: (0..width).collect(),
                permutation,
                phases: vec![0; 1 << width],
            },
        });
    }
    compiler.charge(module, span, total_size(steps.iter().map(size)))?;
    Ok(steps)
}

// Recursion is bounded by the independent verifier's branch-depth limit.
#[allow(clippy::too_many_arguments)]
fn flatten_ops(
    compiler: &mut Compiler<'_>,
    module: &str,
    span: Span,
    operations: &[RawOp],
    registers: &mut BTreeMap<TokenId, Vec<usize>>,
    classical: &mut BTreeMap<ClassicalId, bool>,
    steps: &mut Vec<CircuitStep>,
) -> Result<(), CompileError> {
    for op in operations {
        compiler.tick(module, span)?;
        match op {
            RawOp::Gate {
                gate: g,
                input,
                output,
            } => {
                let axes = registers.remove(input).expect("verified input");
                steps.push(gate(*g, axes[0]));
                registers.insert(*output, axes);
            }
            RawOp::Cnot {
                control,
                target,
                control_out,
                target_out,
            } => {
                let c = registers.remove(control).expect("verified input");
                let t = registers.remove(target).expect("verified input");
                let mut step = gate(SingleGate::X, t[0]);
                step.controls.push(BitControl {
                    index: c[0],
                    when_one: true,
                });
                steps.push(step);
                registers.insert(*control_out, c);
                registers.insert(*target_out, t);
            }
            RawOp::Toffoli {
                control_a,
                control_b,
                target,
                control_a_out,
                control_b_out,
                target_out,
            } => {
                let a = registers.remove(control_a).expect("verified input");
                let b = registers.remove(control_b).expect("verified input");
                let t = registers.remove(target).expect("verified input");
                let mut step = gate(SingleGate::X, t[0]);
                step.controls = vec![
                    BitControl {
                        index: a[0],
                        when_one: true,
                    },
                    BitControl {
                        index: b[0],
                        when_one: true,
                    },
                ];
                steps.push(step);
                registers.insert(*control_a_out, a);
                registers.insert(*control_b_out, b);
                registers.insert(*target_out, t);
            }
            RawOp::Split {
                input,
                left,
                right,
                left_bits,
            } => {
                let axes = registers.remove(input).expect("verified input");
                let middle = usize::from(*left_bits);
                registers.insert(*left, axes[..middle].to_vec());
                registers.insert(*right, axes[middle..].to_vec());
            }
            RawOp::Join {
                left,
                right,
                output,
            } => {
                let mut axes = registers.remove(left).expect("verified input");
                axes.extend(registers.remove(right).expect("verified input"));
                registers.insert(*output, axes);
            }
            RawOp::LiftBasis {
                input,
                output,
                table,
                ..
            } => {
                let axes = registers.remove(input).expect("verified input");
                // A verified Unitary cannot contain a width-increasing lift.
                compiler.charge(module, span, table.len() * 2 + axes.len())?;
                steps.push(CircuitStep {
                    controls: vec![],
                    action: CircuitAction::Monomial {
                        indices: axes.clone(),
                        permutation: table.clone(),
                        phases: vec![0; table.len()],
                    },
                });
                registers.insert(*output, axes);
            }
            RawOp::ApplyUnitary {
                input,
                output,
                steps: nested,
            } => {
                let axes = registers.remove(input).expect("verified input");
                for step in nested {
                    compiler.charge(module, span, size(step))?;
                    let mut step = step.clone();
                    remap(&mut step, &axes);
                    steps.push(step);
                }
                registers.insert(*output, axes);
            }
            RawOp::CertifiedCompute {
                source,
                source_out,
                logical_steps,
                ..
            } => {
                // The independent verifier established W E_f = E_f u for
                // these exact retained circuits. Eliminating the private
                // compute/uncompute scope therefore realizes u with its phase.
                let axes = registers.remove(source).expect("verified input");
                for step in logical_steps {
                    compiler.charge(module, span, size(step))?;
                    let mut step = step.clone();
                    remap(&mut step, &axes);
                    steps.push(step);
                }
                registers.insert(*source_out, axes);
            }
            RawOp::ComputeUseUncompute {
                source,
                source_out,
                targets,
                function,
                use_ops,
                ..
            } if targets.is_empty() => {
                let axes = registers.remove(source).expect("verified input");
                compiler.charge(
                    module,
                    span,
                    function.len().saturating_mul(use_ops.len() + 2),
                )?;
                let mut phases = vec![0u8; function.len()];
                for (label, computed) in function.iter().enumerate() {
                    for usage in use_ops {
                        let ProtectedUse::ProtectedGate { bit, gate } = usage else {
                            return Err(compiler.error(
                                module,
                                span,
                                ErrorCode::Unsupported,
                                "static transform requires a diagonal computed body",
                            ));
                        };
                        let value = match bit.region {
                            ProtectedRegion::Source => label,
                            ProtectedRegion::Ancilla => usize::from(*computed),
                        };
                        if value & (1 << bit.index) != 0 {
                            let exponent = if *gate == SingleGate::Z { 4 } else { 1 };
                            phases[label] = (phases[label] + exponent) % 8;
                        }
                    }
                }
                steps.push(CircuitStep {
                    controls: vec![],
                    action: CircuitAction::Monomial {
                        indices: axes.clone(),
                        permutation: (0..function.len() as u16).collect(),
                        phases,
                    },
                });
                registers.insert(*source_out, axes);
            }
            RawOp::ClassicalConst { value, output } => {
                classical.insert(*output, *value);
            }
            RawOp::ClassicalNot { input, output } => {
                classical.insert(*output, !classical[input]);
            }
            RawOp::ClassicalXor {
                left,
                right,
                output,
            } => {
                classical.insert(*output, classical[left] ^ classical[right]);
            }
            RawOp::ClassicalAnd {
                left,
                right,
                output,
            } => {
                classical.insert(*output, classical[left] & classical[right]);
            }
            RawOp::ClassicalBranch {
                condition,
                then_ops,
                else_ops,
                quantum_phis,
                classical_phis,
            } => {
                compiler.charge(module, span, quantum_phis.len() + classical_phis.len())?;
                // A static target has no classical inputs and cannot observe.
                // Its classical values, including conditions, are closed and
                // deterministic. Both arms were checked before this selection.
                let then_arm = classical[condition];
                let arm = if then_arm { then_ops } else { else_ops };
                flatten_ops(compiler, module, span, arm, registers, classical, steps)?;
                let outputs = quantum_phis
                    .iter()
                    .map(|phi| {
                        let input = if then_arm {
                            phi.then_token
                        } else {
                            phi.else_token
                        };
                        (
                            phi.output,
                            registers.remove(&input).expect("verified phi input"),
                        )
                    })
                    .collect::<Vec<_>>();
                registers.extend(outputs);
                let values = classical_phis
                    .iter()
                    .map(|phi| {
                        let input = if then_arm { phi.then_id } else { phi.else_id };
                        (phi.output, classical[&input])
                    })
                    .collect::<Vec<_>>();
                classical.extend(values);
            }
            _ => {
                return Err(compiler.error(
                    module,
                    span,
                    ErrorCode::Unsupported,
                    "operation is outside the finite static unitary subset",
                ));
            }
        }
    }
    Ok(())
}
