//! Conversion of independently verified unitaries to ordered flat finite circuits.
use super::lower::{CircuitSources, OperationSources};
use super::*;
use crate::ir::*;

pub(super) fn size(step: &CircuitStep) -> usize {
    crate::frontend::raw_state::circuit_size(step)
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
    verified: &AcceptedProgram,
) -> Result<Vec<CircuitStep>, CompileError> {
    flatten_with_sources(compiler, module, span, verified, None).map(|(steps, _)| steps)
}

pub(super) fn flatten_with_sources(
    compiler: &mut Compiler<'_>,
    module: &str,
    span: Span,
    verified: &AcceptedProgram,
    sources: Option<&OperationSources>,
) -> Result<(Vec<CircuitStep>, CircuitSources), CompileError> {
    let raw = verified.program();
    compiler.charge(module, span, raw.quantum_inputs.len() + 1)?;
    let width = raw
        .quantum_inputs
        .iter()
        .map(|port| port.wires.len())
        .sum::<usize>();
    compiler.charge(
        module,
        span,
        width + raw.quantum_inputs.len() * 3 + raw.quantum_outputs.len() + 80,
    )?;
    if width > MAX_BITS
        || !raw.classical_inputs.is_empty()
        || !raw.classical_outputs.is_empty()
        || raw.quantum_inputs.is_empty()
        || raw.quantum_outputs.is_empty()
    {
        return Err(compiler.error(
            module,
            span,
            ErrorCode::Unsupported,
            "finite transforms require a nonempty quantum owner group of at most 12 bits",
        ));
    }
    let mut offset = 0;
    let registers = raw
        .quantum_inputs
        .iter()
        .map(|port| {
            let axes = (offset..offset + port.wires.len()).collect();
            offset += port.wires.len();
            (port.token, axes)
        })
        .collect();
    let mut flat = FlatCircuit {
        registers,
        classical: BTreeMap::new(),
        steps: Vec::new(),
        sources,
        path: Vec::new(),
        circuit_sources: BTreeMap::new(),
    };
    flat.append(compiler, module, span, &raw.operations)?;
    // Rebind the result to the input axis order. Reordered ownership is part
    // of the function's operator and must participate in adjoint and control.
    compiler.charge(
        module,
        span,
        width * width + width + raw.quantum_outputs.len() + 80,
    )?;
    let axes: Vec<_> = raw
        .quantum_outputs
        .iter()
        .flat_map(|token| flat.registers[token].iter().copied())
        .collect();
    if axes.len() != width
        || (0..width).any(|axis| axes.iter().filter(|found| **found == axis).count() != 1)
    {
        return Err(compiler.error(
            module,
            span,
            ErrorCode::InvalidIr,
            "verified transform changes its complete ordered quantum interface",
        ));
    }
    if axes.iter().copied().ne(0..width) {
        compiler.charge(module, span, (1 << width) * (width + 2))?;
        let permutation = (0..1usize << width)
            .map(|label| {
                axes.iter().enumerate().fold(0u16, |out, (place, axis)| {
                    out | ((((label >> axis) & 1) as u16) << place)
                })
            })
            .collect();
        if flat.steps.len() == flat.steps.capacity() {
            compiler.charge(module, span, flat.steps.len() + 1)?;
            flat.steps.reserve_exact(1);
        }
        flat.steps.push(CircuitStep {
            controls: vec![],
            action: CircuitAction::Monomial {
                indices: (0..width).collect(),
                permutation,
                phases: vec![0; 1 << width],
            },
        });
    }
    compiler.charge(module, span, total_size(flat.steps.iter().map(size)))?;
    Ok((flat.steps, flat.circuit_sources))
}

/// Propose the diagonal rows from the validated XOR scratch circuit. The
/// native body check still reads the original predicate, scratch and uses.
fn structural_predicate_rows(
    compiler: &mut Compiler<'_>,
    module: &str,
    span: Span,
    width: usize,
    forward: &[CircuitStep],
) -> Result<Vec<u16>, CompileError> {
    if width > crate::contract::MAX_CONTRACT_BITS {
        return Err(compiler.error(
            module,
            span,
            ErrorCode::Limit,
            "computed diagonal exceeds six source bits",
        ));
    }
    let clauses = 1 + total_size(forward.iter().map(|step| step.controls.len() + 1));
    let count = 1 << width;
    compiler.charge(module, span, clauses.saturating_mul(count))?;
    if !forward.iter().all(|step| {
        matches!(&step.action, CircuitAction::Monomial { indices, permutation, phases }
            if indices == &[width] && permutation == &[1, 0] && phases == &[0, 0])
            && step.controls.iter().all(|control| control.index < width)
    }) {
        return Err(compiler.error(
            module,
            span,
            ErrorCode::InvalidIr,
            "structural computation requires source-controlled scratch flips",
        ));
    }
    Ok((0..count)
        .map(|label| {
            u16::from(forward.iter().fold(false, |parity, step| {
                parity
                    ^ step
                        .controls
                        .iter()
                        .all(|control| ((label >> control.index) & 1 != 0) == control.when_one)
            }))
        })
        .collect())
}

/// The complete working state of one flattening pass. Classical branches
/// recurse through this same state, retaining ownership and visible constants.
struct FlatCircuit<'a> {
    registers: BTreeMap<TokenId, Vec<usize>>,
    classical: BTreeMap<ClassicalId, bool>,
    steps: Vec<CircuitStep>,
    sources: Option<&'a OperationSources>,
    path: Vec<usize>,
    circuit_sources: CircuitSources,
}

impl FlatCircuit<'_> {
    fn append_computed_diagonal(
        &mut self,
        compiler: &mut Compiler<'_>,
        module: &str,
        span: Span,
        [source, output]: [TokenId; 2],
        function: &[u16],
        uses: &[ProtectedUse],
    ) -> Result<(), CompileError> {
        let axes = self.registers.remove(&source).expect("verified input");
        let use_cost = uses.iter().fold(2usize, |cost, usage| {
            cost.saturating_add(match usage {
                ProtectedUse::ControlledPhase { controls, .. } => controls.len() + 1,
                _ => 1,
            })
        });
        compiler.charge(
            module,
            span,
            (axes.len() + 1).saturating_add(function.len().saturating_mul(use_cost)),
        )?;
        let mut phases = vec![0u8; function.len()];
        for (label, computed) in function.iter().enumerate() {
            for usage in uses {
                let bit_value = |bit: &ProtectedBit| {
                    let value = match bit.region {
                        ProtectedRegion::Source => label,
                        ProtectedRegion::Ancilla => usize::from(*computed),
                    };
                    value & (1 << bit.index) != 0
                };
                let exponent = match usage {
                    ProtectedUse::ProtectedGate { bit, gate }
                        if matches!(gate, SingleGate::Z | SingleGate::T) =>
                    {
                        if bit_value(bit) {
                            if *gate == SingleGate::Z { 4 } else { 1 }
                        } else {
                            0
                        }
                    }
                    ProtectedUse::ControlledPhase { controls, phase } => {
                        if controls
                            .iter()
                            .all(|control| bit_value(&control.bit) == control.when_one)
                        {
                            match phase {
                                ScalarPhase::MinusOne => 4,
                                ScalarPhase::EighthTurn => 1,
                            }
                        } else {
                            0
                        }
                    }
                    _ => {
                        return Err(compiler.error(
                            module,
                            span,
                            ErrorCode::Unsupported,
                            "static transform requires a diagonal computed body",
                        ));
                    }
                };
                phases[label] = (phases[label] + exponent) % 8;
            }
        }
        self.steps.push(CircuitStep {
            controls: vec![],
            action: CircuitAction::Monomial {
                indices: axes.clone(),
                permutation: (0..function.len() as u16).collect(),
                phases,
            },
        });
        self.registers.insert(output, axes);
        Ok(())
    }

    // Recursion is bounded by the independent verifier's branch-depth limit.
    fn append(
        &mut self,
        compiler: &mut Compiler<'_>,
        module: &str,
        span: Span,
        operations: &[RawOp],
    ) -> Result<(), CompileError> {
        for (index, op) in operations.iter().enumerate() {
            compiler.tick(module, span)?;
            let begin = self.steps.len();
            if self.sources.is_some() {
                self.path.push(index);
            }
            match op {
                RawOp::PackUnit { output } => {
                    // A logical zero-width owner has no coordinate to remap.
                    // Scalar actions on it remain ordinary circuit steps.
                    self.registers.insert(*output, Vec::new());
                }
                RawOp::UnpackUnit { input } => {
                    let axes = self.registers.remove(input).expect("verified Unit owner");
                    if !axes.is_empty() {
                        return Err(compiler.error(
                            module,
                            span,
                            ErrorCode::InvalidIr,
                            "structural Unit consumption has nonzero width",
                        ));
                    }
                }
                RawOp::Gate {
                    gate: g,
                    input,
                    output,
                } => {
                    let axes = self.registers.remove(input).expect("verified input");
                    self.steps.push(gate(*g, axes[0]));
                    self.registers.insert(*output, axes);
                }
                RawOp::Cnot {
                    control,
                    target,
                    control_out,
                    target_out,
                } => {
                    let c = self.registers.remove(control).expect("verified input");
                    let t = self.registers.remove(target).expect("verified input");
                    let mut step = gate(SingleGate::X, t[0]);
                    step.controls.push(BitControl {
                        index: c[0],
                        when_one: true,
                    });
                    self.steps.push(step);
                    self.registers.insert(*control_out, c);
                    self.registers.insert(*target_out, t);
                }
                RawOp::Toffoli {
                    control_a,
                    control_b,
                    target,
                    control_a_out,
                    control_b_out,
                    target_out,
                } => {
                    let a = self.registers.remove(control_a).expect("verified input");
                    let b = self.registers.remove(control_b).expect("verified input");
                    let t = self.registers.remove(target).expect("verified input");
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
                    self.steps.push(step);
                    self.registers.insert(*control_a_out, a);
                    self.registers.insert(*control_b_out, b);
                    self.registers.insert(*target_out, t);
                }
                RawOp::Split {
                    input,
                    left,
                    right,
                    left_bits,
                } => {
                    let axes = self.registers.remove(input).expect("verified input");
                    let middle = usize::from(*left_bits);
                    self.registers.insert(*left, axes[..middle].to_vec());
                    self.registers.insert(*right, axes[middle..].to_vec());
                }
                RawOp::Join {
                    left,
                    right,
                    output,
                } => {
                    let mut axes = self.registers.remove(left).expect("verified input");
                    axes.extend(self.registers.remove(right).expect("verified input"));
                    self.registers.insert(*output, axes);
                }
                RawOp::LiftBasis {
                    input,
                    output,
                    table,
                    ..
                } => {
                    let axes = self.registers.remove(input).expect("verified input");
                    // A verified Unitary cannot contain a width-increasing lift.
                    compiler.charge(module, span, table.len() * 2 + axes.len())?;
                    self.steps.push(CircuitStep {
                        controls: vec![],
                        action: CircuitAction::Monomial {
                            indices: axes.clone(),
                            permutation: table.clone(),
                            phases: vec![0; table.len()],
                        },
                    });
                    self.registers.insert(*output, axes);
                }
                RawOp::ApplyUnitary {
                    input,
                    output,
                    steps: nested,
                }
                | RawOp::CertifiedCompute {
                    source: input,
                    source_out: output,
                    logical_steps: nested,
                    ..
                } => {
                    // CertifiedCompute's independently checked W E_f = E_f u
                    // equation permits this same phase-preserving logical circuit.
                    let axes = self.registers.remove(input).expect("verified input");
                    for step in nested {
                        compiler.charge(module, span, size(step))?;
                        let mut step = step.clone();
                        remap(&mut step, &axes);
                        self.steps.push(step);
                    }
                    self.registers.insert(*output, axes);
                }
                RawOp::ComputeUseUncompute {
                    source,
                    source_out,
                    targets,
                    function,
                    use_ops,
                    ..
                } if targets.is_empty() => {
                    self.append_computed_diagonal(
                        compiler,
                        module,
                        span,
                        [*source, *source_out],
                        function,
                        use_ops,
                    )?;
                }
                RawOp::StructuralCompute {
                    source,
                    source_out,
                    forward,
                    uses,
                    ..
                } => {
                    let width = self.registers[source].len();
                    let rows = structural_predicate_rows(compiler, module, span, width, forward)?;
                    self.append_computed_diagonal(
                        compiler,
                        module,
                        span,
                        [*source, *source_out],
                        &rows,
                        uses,
                    )?;
                }
                RawOp::ClassicalConst { value, output } => {
                    self.classical.insert(*output, *value);
                }
                RawOp::ClassicalNot { input, output } => {
                    self.classical.insert(*output, !self.classical[input]);
                }
                RawOp::ClassicalXor {
                    left,
                    right,
                    output,
                } => {
                    self.classical
                        .insert(*output, self.classical[left] ^ self.classical[right]);
                }
                RawOp::ClassicalAnd {
                    left,
                    right,
                    output,
                } => {
                    self.classical
                        .insert(*output, self.classical[left] & self.classical[right]);
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
                    let then_arm = self.classical[condition];
                    let arm = if then_arm { then_ops } else { else_ops };
                    if self.sources.is_some() {
                        self.path.push(usize::from(!then_arm));
                    }
                    self.append(compiler, module, span, arm)?;
                    if self.sources.is_some() {
                        self.path.pop();
                    }
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
                                self.registers.remove(&input).expect("verified phi input"),
                            )
                        })
                        .collect::<Vec<_>>();
                    self.registers.extend(outputs);
                    let values = classical_phis
                        .iter()
                        .map(|phi| {
                            let input = if then_arm { phi.then_id } else { phi.else_id };
                            (phi.output, self.classical[&input])
                        })
                        .collect::<Vec<_>>();
                    self.classical.extend(values);
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
            if let Some(sources) = self.sources {
                if !matches!(op, RawOp::ClassicalBranch { .. }) {
                    if let Some(source) = sources.get(&self.path) {
                        for step in begin..self.steps.len() {
                            // A flattened nested clean body contributes its logical
                            // implementation. Its physical steps are a separate word.
                            let site = match op {
                                RawOp::ApplyUnitary { .. } => source
                                    .circuit
                                    .as_ref()
                                    .and_then(|steps| steps.get(&(step - begin))),
                                _ => None,
                            }
                            .unwrap_or(&source.site);
                            if site.instance.is_some() {
                                self.circuit_sources.insert(step, site.clone());
                            }
                        }
                    }
                }
                self.path.pop();
            }
        }
        Ok(())
    }
}
