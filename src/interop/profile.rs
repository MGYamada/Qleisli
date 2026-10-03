use super::{InteropError, InteropErrorKind, MAX_GATES, MAX_OPERATIONS, MAX_QUBITS};
use crate::AcceptedProgram;
use crate::ir::*;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Gate {
    H,
    X,
    Y,
    Z,
    S,
    Sdg,
    T,
    Tdg,
    Cx,
    Cz,
    Swap,
    Ccx,
}

impl Gate {
    pub fn parse(name: &str) -> Option<Self> {
        Some(match name {
            "h" => Self::H,
            "x" => Self::X,
            "y" => Self::Y,
            "z" => Self::Z,
            "s" => Self::S,
            "sdg" => Self::Sdg,
            "t" => Self::T,
            "tdg" => Self::Tdg,
            "cx" => Self::Cx,
            "cz" => Self::Cz,
            "swap" => Self::Swap,
            "ccx" => Self::Ccx,
            _ => return None,
        })
    }
    pub fn name(self) -> &'static str {
        match self {
            Self::H => "h",
            Self::X => "x",
            Self::Y => "y",
            Self::Z => "z",
            Self::S => "s",
            Self::Sdg => "sdg",
            Self::T => "t",
            Self::Tdg => "tdg",
            Self::Cx => "cx",
            Self::Cz => "cz",
            Self::Swap => "swap",
            Self::Ccx => "ccx",
        }
    }
    pub fn arity(self) -> usize {
        match self {
            Self::Cx | Self::Cz | Self::Swap => 2,
            Self::Ccx => 3,
            _ => 1,
        }
    }
    fn single(gate: SingleGate) -> Self {
        match gate {
            SingleGate::H => Self::H,
            SingleGate::X => Self::X,
            SingleGate::Z => Self::Z,
            SingleGate::T => Self::T,
        }
    }
    pub fn step(self) -> CircuitStep {
        let (indices, permutation, phases) = match self {
            Self::H => {
                return CircuitStep {
                    controls: vec![],
                    action: CircuitAction::Hadamard { target: 0 },
                };
            }
            Self::X | Self::Cx | Self::Ccx => (vec![self.arity() - 1], vec![1, 0], vec![0, 0]),
            Self::Y => (vec![0], vec![1, 0], vec![2, 6]),
            Self::Z | Self::Cz => (vec![self.arity() - 1], vec![0, 1], vec![0, 4]),
            Self::S => (vec![0], vec![0, 1], vec![0, 2]),
            Self::Sdg => (vec![0], vec![0, 1], vec![0, 6]),
            Self::T => (vec![0], vec![0, 1], vec![0, 1]),
            Self::Tdg => (vec![0], vec![0, 1], vec![0, 7]),
            Self::Swap => (vec![0, 1], vec![0, 2, 1, 3], vec![0; 4]),
        };
        let controls = match self {
            Self::Cx | Self::Cz | Self::Ccx => (0..self.arity() - 1)
                .map(|index| BitControl {
                    index,
                    when_one: true,
                })
                .collect(),
            _ => vec![],
        };
        CircuitStep {
            controls,
            action: CircuitAction::Monomial {
                indices,
                permutation,
                phases,
            },
        }
    }
}

pub(super) struct GateOp {
    pub gate: Gate,
    pub wires: Vec<usize>,
}
pub(super) struct TerminalCircuit {
    pub qubits: usize,
    pub gates: Vec<GateOp>,
    /// Physical qubits in visible result order. Hidden terminal results trace out.
    pub measurements: Vec<usize>,
}

impl TerminalCircuit {
    pub fn push(&mut self, gate: Gate, wires: Vec<usize>) -> Result<(), InteropError> {
        if self.gates.len() >= MAX_GATES {
            return Err(InteropError::limit("at most 4096 gates"));
        }
        if wires.len() != gate.arity()
            || wires.iter().any(|&q| q >= self.qubits)
            || wires.iter().collect::<BTreeSet<_>>().len() != wires.len()
        {
            return Err(InteropError::unsupported(
                "gate operands must be distinct in-range qubits of the required arity",
            ));
        }
        self.gates.push(GateOp { gate, wires });
        Ok(())
    }
    pub fn lower_with_kernel(
        &self,
        kernel: &crate::interchange::native::Kernel,
    ) -> Result<AcceptedProgram, InteropError> {
        let mut operations = Vec::new();
        let mut next = 0u32;
        let mut fresh = || {
            let id = TokenId(next);
            next += 1;
            id
        };
        let mut owners = Vec::new();
        for q in 0..self.qubits {
            let output = fresh();
            operations.push(RawOp::Init0 {
                output,
                wire: WireId(q as u32),
            });
            owners.push(Some(output));
        }
        for op in &self.gates {
            let mut input = owners[op.wires[0]].take().expect("profile owner");
            for &q in &op.wires[1..] {
                let output = fresh();
                operations.push(RawOp::Join {
                    left: input,
                    right: owners[q].take().expect("profile owner"),
                    output,
                });
                input = output;
            }
            let output = fresh();
            operations.push(RawOp::ApplyUnitary {
                input,
                output,
                steps: vec![op.gate.step()],
            });
            let mut input = output;
            for i in (1..op.wires.len()).rev() {
                let left = fresh();
                let right = fresh();
                operations.push(RawOp::Split {
                    input,
                    left,
                    right,
                    left_bits: i as u8,
                });
                owners[op.wires[i]] = Some(right);
                input = left;
            }
            owners[op.wires[0]] = Some(input);
        }
        let mut classical_outputs = Vec::new();
        for (i, &q) in self.measurements.iter().enumerate() {
            let output = ClassicalId(i as u32);
            operations.push(RawOp::MeasureZ {
                input: owners[q].take().expect("profile measurement"),
                output,
            });
            classical_outputs.push(output);
        }
        for input in owners.into_iter().flatten() {
            operations.push(RawOp::Discard { input });
        }
        kernel
            .accept_raw(RawProgram {
                quantum_inputs: vec![],
                classical_inputs: vec![],
                operations,
                quantum_outputs: vec![],
                classical_outputs,
                declared_effect: Effect::Observe,
            })
            .map_err(|e| InteropError::new(InteropErrorKind::InvalidIr, e.to_string()))
    }
}

pub(super) fn recognize(
    step: &CircuitStep,
    wires: &[usize],
) -> Result<(Gate, Vec<usize>), InteropError> {
    let mut axes = Vec::new();
    for control in &step.controls {
        if !control.when_one {
            return Err(InteropError::unsupported("negative gate controls"));
        }
        axes.push(control.index);
    }
    let gate = match &step.action {
        CircuitAction::Hadamard { target } if axes.is_empty() => {
            axes.push(*target);
            Gate::H
        }
        CircuitAction::Monomial {
            indices,
            permutation,
            phases,
        } => {
            let n = axes.len();
            axes.extend(indices);
            match (n, indices.len(), permutation.as_slice(), phases.as_slice()) {
                (0, 1, [1, 0], [0, 0]) => Gate::X,
                (0, 1, [1, 0], [2, 6]) => Gate::Y,
                (0, 1, [0, 1], [0, 4]) => Gate::Z,
                (0, 1, [0, 1], [0, 2]) => Gate::S,
                (0, 1, [0, 1], [0, 6]) => Gate::Sdg,
                (0, 1, [0, 1], [0, 1]) => Gate::T,
                (0, 1, [0, 1], [0, 7]) => Gate::Tdg,
                (1, 1, [1, 0], [0, 0]) => Gate::Cx,
                (1, 1, [0, 1], [0, 4]) => Gate::Cz,
                (2, 1, [1, 0], [0, 0]) => Gate::Ccx,
                (0, 2, [0, 2, 1, 3], [0, 0, 0, 0]) => Gate::Swap,
                _ => {
                    return Err(InteropError::unsupported(
                        "monomial phases/table or controls outside the terminal gate vocabulary",
                    ));
                }
            }
        }
        _ => {
            return Err(InteropError::unsupported(
                "circuit action outside the terminal gate vocabulary",
            ));
        }
    };
    Ok((gate, axes.into_iter().map(|axis| wires[axis]).collect()))
}

pub(super) fn extract(program: &AcceptedProgram) -> Result<TerminalCircuit, InteropError> {
    let raw = program.raw();
    if !raw.quantum_inputs.is_empty()
        || !raw.classical_inputs.is_empty()
        || !raw.quantum_outputs.is_empty()
    {
        return Err(InteropError::unsupported(
            "closed terminal computation required",
        ));
    }
    if raw.operations.len() > MAX_OPERATIONS {
        return Err(InteropError::limit("at most 65536 raw operations"));
    }
    if raw.classical_outputs.len() > MAX_QUBITS {
        return Err(InteropError::limit("at most 12 result bits"));
    }
    let mut circuit = TerminalCircuit {
        qubits: 0,
        gates: vec![],
        measurements: vec![],
    };
    let mut owners = BTreeMap::<TokenId, Vec<usize>>::new();
    let mut scratch = Vec::new();
    let mut measured = BTreeMap::new();
    let mut observed = false;
    for (index, op) in raw.operations.iter().enumerate() {
        let result = (|| {
            if observed
                && !matches!(
                    op,
                    RawOp::MeasureZ { .. }
                        | RawOp::Discard { .. }
                        | RawOp::Split { .. }
                        | RawOp::Join { .. }
                )
            {
                return Err(InteropError::unsupported(
                    "quantum operation after terminal observation",
                ));
            }
            match op {
                RawOp::Init0 { output, .. } => {
                    if circuit.qubits >= MAX_QUBITS {
                        return Err(InteropError::limit("at most 12 allocated qubits"));
                    }
                    owners.insert(*output, vec![circuit.qubits]);
                    circuit.qubits += 1;
                }
                RawOp::Gate {
                    gate,
                    input,
                    output,
                } => {
                    let wires = owners.remove(input).expect("verified owner");
                    circuit.push(Gate::single(*gate), wires.clone())?;
                    owners.insert(*output, wires);
                }
                RawOp::Cnot {
                    control,
                    target,
                    control_out,
                    target_out,
                } => {
                    let a = owners.remove(control).expect("verified owner");
                    let b = owners.remove(target).expect("verified owner");
                    circuit.push(Gate::Cx, vec![a[0], b[0]])?;
                    owners.insert(*control_out, a);
                    owners.insert(*target_out, b);
                }
                RawOp::Toffoli {
                    control_a,
                    control_b,
                    target,
                    control_a_out,
                    control_b_out,
                    target_out,
                } => {
                    let a = owners.remove(control_a).expect("verified owner");
                    let b = owners.remove(control_b).expect("verified owner");
                    let c = owners.remove(target).expect("verified owner");
                    circuit.push(Gate::Ccx, vec![a[0], b[0], c[0]])?;
                    owners.insert(*control_a_out, a);
                    owners.insert(*control_b_out, b);
                    owners.insert(*target_out, c);
                }
                RawOp::Split {
                    input,
                    left,
                    right,
                    left_bits,
                } => {
                    let mut wires = owners.remove(input).expect("verified owner");
                    let tail = wires.split_off(usize::from(*left_bits));
                    owners.insert(*left, wires);
                    owners.insert(*right, tail);
                }
                RawOp::Join {
                    left,
                    right,
                    output,
                } => {
                    let mut wires = owners.remove(left).expect("verified owner");
                    wires.extend(owners.remove(right).expect("verified owner"));
                    owners.insert(*output, wires);
                }
                RawOp::ApplyUnitary {
                    input,
                    output,
                    steps,
                } => {
                    let wires = owners.remove(input).expect("verified owner");
                    super::export::steps(&mut circuit, &mut scratch, steps, &wires)?;
                    owners.insert(*output, wires);
                }
                RawOp::LiftBasis {
                    input,
                    output,
                    output_wires,
                    table,
                } => {
                    let wires = owners.remove(input).expect("verified owner");
                    let axes =
                        super::export::axis_permutation(table, wires.len(), output_wires.len())?;
                    owners.insert(*output, axes.into_iter().map(|axis| wires[axis]).collect());
                }
                RawOp::MeasureZ { input, output } => {
                    observed = true;
                    let wires = owners.remove(input).expect("verified owner");
                    measured.insert(*output, wires[0]);
                }
                RawOp::Discard { input } => {
                    observed = true;
                    owners.remove(input);
                }
                _ => {
                    return Err(InteropError::unsupported(
                        "IR constructor outside the terminal profile",
                    ));
                }
            }
            Ok(())
        })();
        result.map_err(|mut e: InteropError| {
            e.operation = Some(index);
            e
        })?;
    }
    let mut outputs = BTreeSet::new();
    for id in &raw.classical_outputs {
        if !outputs.insert(id) {
            return Err(InteropError::unsupported("repeated classical output ID"));
        }
        circuit.measurements.push(
            *measured
                .get(id)
                .ok_or_else(|| InteropError::unsupported("output must be a measured bit"))?,
        );
    }
    super::export::fold_phases(&mut circuit);
    Ok(circuit)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::contract::exact::{Budget, Exact};
    use crate::contract::{BasisType, Circuit};

    #[test]
    fn gate_columns_match_independent_exact_definitions_including_phase() {
        for name in [
            "h", "x", "y", "z", "s", "sdg", "t", "tdg", "cx", "cz", "swap", "ccx",
        ] {
            let gate = Gate::parse(name).unwrap();
            let basis =
                (1..gate.arity()).fold(BasisType::Bit, |ty, _| BasisType::pair(ty, BasisType::Bit));
            let matrix = Circuit::new(basis, vec![gate.step()])
                .unwrap()
                .matrix(&mut Budget::new(100_000))
                .unwrap();
            for col in 0..1usize << gate.arity() {
                for row in 0..1usize << gate.arity() {
                    let mut target = col;
                    let mut phase = 0;
                    match name {
                        "x" => target ^= 1,
                        "y" => {
                            target ^= 1;
                            phase = if col == 0 { 2 } else { 6 };
                        }
                        "z" => phase = 4 * col as i32,
                        "s" => phase = 2 * col as i32,
                        "sdg" => phase = -2 * col as i32,
                        "t" => phase = col as i32,
                        "tdg" => phase = -(col as i32),
                        "cx" if col & 1 != 0 => target ^= 2,
                        "cz" if col == 3 => phase = 4,
                        "swap" => target = ((col & 1) << 1) | (col >> 1),
                        "ccx" if col & 3 == 3 => target ^= 4,
                        _ => (),
                    }
                    let expected = if name == "h" {
                        if row == 1 && col == 1 {
                            Exact::inv_sqrt2().neg().unwrap()
                        } else {
                            Exact::inv_sqrt2()
                        }
                    } else if row == target {
                        Exact::phase(phase)
                    } else {
                        Exact::zero()
                    };
                    assert_eq!(matrix.get(row, col), Some(expected), "{name}[{row}, {col}]");
                }
            }
        }
    }
}
