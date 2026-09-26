//! Conversion of independently verified unary unitaries to flat finite circuits.
use super::*;
use crate::ir::*;

pub(super) fn size(step: &CircuitStep) -> usize {
    1 + step.controls.len()
        + match &step.action {
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
        CircuitAction::Hadamard { target } => *target = axes[*target],
        CircuitAction::Monomial { indices, .. } => {
            for index in indices {
                *index = axes[*index];
            }
        }
    }
}

pub(super) fn invert(steps: &mut [CircuitStep]) {
    steps.reverse();
    for step in steps {
        if let CircuitAction::Monomial {
            permutation,
            phases,
            ..
        } = &mut step.action
        {
            let mut inverse = vec![0; permutation.len()];
            let mut inverse_phases = vec![0; phases.len()];
            for (x, y) in permutation.iter().enumerate() {
                inverse[usize::from(*y)] = x as u16;
                inverse_phases[usize::from(*y)] = (8 - phases[x]) % 8;
            }
            *permutation = inverse;
            *phases = inverse_phases;
        }
    }
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
    for op in &raw.operations {
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
    // Rebind the result to the input axis order. Reordered ownership is part
    // of the function's operator and must participate in adjoint and control.
    let axes = &registers[&raw.quantum_outputs[0]];
    if axes.iter().copied().ne(0..width) {
        compiler.charge(module, span, (1 << width) * (width + 2))?;
        let permutation = (0..1usize << width)
            .map(|label| {
                axes.iter().enumerate().fold(0u16, |out, (place, axis)| {
                    out | (((label >> axis) & 1) as u16) << place
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
