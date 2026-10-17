//! Exact finite operator checks, including global phase, not a general proof.

mod common;

use std::collections::BTreeMap;
use std::ops::{Add, Mul, Neg};

use common::SourceRoot;
use qleisli::frontend::compile::compile_project;
use qleisli::ir::{
    BitControl, CircuitAction, CircuitStep, ClassicalId, RawOp, RawProgram, ScalarPhase,
    SingleGate, TokenId, UnitaryStep, WireId,
};

// Z[zeta, 1/2], where zeta = exp(i*pi/4) and zeta^4 = -1.
// Normalization makes equality exact; checked arithmetic fails on overflow.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Exact {
    coefficients: [i128; 4],
    denominator_power: u32,
}

impl Exact {
    const ZERO: Self = Self {
        coefficients: [0; 4],
        denominator_power: 0,
    };
    const ONE: Self = Self {
        coefficients: [1, 0, 0, 0],
        denominator_power: 0,
    };

    fn new(mut coefficients: [i128; 4], mut denominator_power: u32) -> Self {
        while denominator_power > 0 && coefficients.iter().all(|x| x % 2 == 0) {
            coefficients = coefficients.map(|x| x / 2);
            denominator_power -= 1;
        }
        Self {
            coefficients,
            denominator_power,
        }
    }

    fn phase(exponent: usize) -> Self {
        let exponent = exponent % 8;
        let mut coefficients = [0; 4];
        coefficients[exponent % 4] = if exponent < 4 { 1 } else { -1 };
        Self::new(coefficients, 0)
    }

    fn conjugate(self) -> Self {
        let [a, b, c, d] = self.coefficients;
        Self::new(
            [
                a,
                d.checked_neg().unwrap(),
                c.checked_neg().unwrap(),
                b.checked_neg().unwrap(),
            ],
            self.denominator_power,
        )
    }

    fn inverse_sqrt_two() -> Self {
        Self::new([0, 1, 0, -1], 1)
    }
}

impl Add for Exact {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        let power = self.denominator_power.max(rhs.denominator_power);
        let left_scale = 2_i128.checked_pow(power - self.denominator_power).unwrap();
        let right_scale = 2_i128.checked_pow(power - rhs.denominator_power).unwrap();
        Self::new(
            std::array::from_fn(|i| {
                self.coefficients[i]
                    .checked_mul(left_scale)
                    .unwrap()
                    .checked_add(rhs.coefficients[i].checked_mul(right_scale).unwrap())
                    .unwrap()
            }),
            power,
        )
    }
}

impl Neg for Exact {
    type Output = Self;

    fn neg(self) -> Self {
        Self::new(
            self.coefficients.map(|x| x.checked_neg().unwrap()),
            self.denominator_power,
        )
    }
}

impl Mul for Exact {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        let mut coefficients = [0_i128; 4];
        for (i, left) in self.coefficients.into_iter().enumerate() {
            for (j, right) in rhs.coefficients.into_iter().enumerate() {
                let product = left.checked_mul(right).unwrap();
                let product = if i + j >= 4 {
                    product.checked_neg().unwrap()
                } else {
                    product
                };
                coefficients[(i + j) % 4] = coefficients[(i + j) % 4].checked_add(product).unwrap();
            }
        }
        Self::new(
            coefficients,
            self.denominator_power
                .checked_add(rhs.denominator_power)
                .unwrap(),
        )
    }
}

const IMPORTS: &str = "
use std::state::init0;  use std::gate::x;
use std::gate::z; use std::gate::t; use std::gate::cnot;
\x20\x20
";

fn compiled_steps(definitions: &str, preparation: &str, operation: &str) -> Vec<CircuitStep> {
    let root = SourceRoot::new(&format!(
        "{IMPORTS}\n{definitions}\nobserve fn main() -> Unit {{
            {preparation} let result = {operation}; discard(result); ()
        }}"
    ));
    let verified = compile_project(&root.0).unwrap();
    let mut circuits = verified
        .program()
        .operations
        .iter()
        .filter_map(|op| match op {
            RawOp::ApplyUnitary { steps, .. } => Some(steps.clone()),
            _ => None,
        });
    let steps = circuits.next().expect("one outer static operation");
    assert!(
        circuits.next().is_none(),
        "nested operations must be flattened"
    );
    steps
}

// Interpret the retained implementation, rather than its cached matrix or the
// production simulator/extractor. This deliberately small pure Raw profile
// rejects unsupported commands instead of treating function calls as identity.
// Axis 0 is the least significant bit throughout, including output owner order.
fn raw_operator(raw: &RawProgram, depth: usize) -> Vec<Vec<Exact>> {
    assert!(depth <= 32, "bounded retained function evidence depth");
    assert_eq!(raw.quantum_inputs.len(), 1);
    assert_eq!(raw.quantum_outputs.len(), 1);
    assert!(raw.classical_inputs.is_empty() && raw.classical_outputs.is_empty());
    assert_eq!(raw.declared_effect, qleisli::ir::Effect::Unitary);
    let port = &raw.quantum_inputs[0];
    let width = port.wires.len();
    assert!(
        width <= 3,
        "this exact checker covers small implementations"
    );
    assert_eq!(usize::from(port.shape.bits), width);
    let axes: BTreeMap<_, _> = port
        .wires
        .iter()
        .enumerate()
        .map(|(axis, wire)| (*wire, axis))
        .collect();
    assert_eq!(axes.len(), width);
    let dimension = 1 << width;
    let mut columns = vec![vec![Exact::ZERO; dimension]; dimension];
    for (column, values) in columns.iter_mut().enumerate() {
        let mut state = RawState {
            owners: BTreeMap::from([(port.token, port.wires.clone())]),
            classical: BTreeMap::new(),
            axes: axes.clone(),
            amplitudes: vec![Exact::ZERO; dimension],
            depth,
        };
        state.amplitudes[column] = Exact::ONE;
        state.operations(&raw.operations);
        let output = state.take(raw.quantum_outputs[0]);
        assert!(state.owners.is_empty());
        assert_eq!(output.len(), width);
        let output_axes = state.indices(&output);
        let mut ordered_axes = output_axes.clone();
        ordered_axes.sort_unstable();
        assert_eq!(ordered_axes, (0..width).collect::<Vec<_>>());
        for (basis, amplitude) in state.amplitudes.into_iter().enumerate() {
            let row = label(basis, &output_axes);
            values[row] = values[row] + amplitude;
        }
    }
    (0..dimension)
        .map(|row| columns.iter().map(|column| column[row]).collect())
        .collect()
}

struct RawState {
    owners: BTreeMap<TokenId, Vec<WireId>>,
    classical: BTreeMap<ClassicalId, bool>,
    axes: BTreeMap<WireId, usize>,
    amplitudes: Vec<Exact>,
    depth: usize,
}

impl RawState {
    fn take(&mut self, token: TokenId) -> Vec<WireId> {
        self.owners.remove(&token).expect("live Raw owner")
    }

    fn put(&mut self, token: TokenId, wires: Vec<WireId>) {
        assert!(self.owners.insert(token, wires).is_none());
    }

    fn indices(&self, wires: &[WireId]) -> Vec<usize> {
        wires.iter().map(|wire| self.axes[wire]).collect()
    }

    fn apply(&mut self, steps: &[CircuitStep], wires: &[WireId]) {
        let axes = self.indices(wires);
        apply_steps(&mut self.amplitudes, steps, &axes, self.depth);
    }

    fn operations(&mut self, operations: &[RawOp]) {
        for op in operations {
            match op {
                RawOp::PackUnit { output } => self.put(*output, vec![]),
                RawOp::UnpackUnit { input } => assert!(self.take(*input).is_empty()),
                RawOp::Split {
                    input,
                    left,
                    right,
                    left_bits,
                } => {
                    let mut wires = self.take(*input);
                    let right_wires = wires.split_off(usize::from(*left_bits));
                    self.put(*left, wires);
                    self.put(*right, right_wires);
                }
                RawOp::Join {
                    left,
                    right,
                    output,
                } => {
                    let mut wires = self.take(*left);
                    wires.extend(self.take(*right));
                    self.put(*output, wires);
                }
                RawOp::Gate {
                    gate,
                    input,
                    output,
                } => {
                    let wires = self.take(*input);
                    assert_eq!(wires.len(), 1);
                    self.apply(&[gate_step(*gate, 0)], &wires);
                    self.put(*output, wires);
                }
                RawOp::Cnot {
                    control,
                    target,
                    control_out,
                    target_out,
                } => {
                    let control_wires = self.take(*control);
                    let target_wires = self.take(*target);
                    assert_eq!(control_wires.len(), 1);
                    assert_eq!(target_wires.len(), 1);
                    let wires = [control_wires[0], target_wires[0]];
                    let step = CircuitStep {
                        controls: vec![BitControl {
                            index: 0,
                            when_one: true,
                        }],
                        action: gate_step(SingleGate::X, 1).action.clone(),
                    };
                    self.apply(&[step], &wires);
                    self.put(*control_out, control_wires);
                    self.put(*target_out, target_wires);
                }
                RawOp::Toffoli {
                    control_a,
                    control_b,
                    target,
                    control_a_out,
                    control_b_out,
                    target_out,
                } => {
                    let a = self.take(*control_a);
                    let b = self.take(*control_b);
                    let target_wires = self.take(*target);
                    assert_eq!((a.len(), b.len(), target_wires.len()), (1, 1, 1));
                    let mut step = gate_step(SingleGate::X, 2);
                    step.controls.extend([0, 1].map(|index| BitControl {
                        index,
                        when_one: true,
                    }));
                    self.apply(&[step], &[a[0], b[0], target_wires[0]]);
                    self.put(*control_a_out, a);
                    self.put(*control_b_out, b);
                    self.put(*target_out, target_wires);
                }
                RawOp::LiftBasis {
                    input,
                    output,
                    output_wires,
                    table,
                } => {
                    let wires = self.take(*input);
                    assert_eq!(
                        &wires, output_wires,
                        "pure table keeps its full wire interface"
                    );
                    let step = CircuitStep {
                        controls: vec![],
                        action: CircuitAction::Monomial {
                            indices: (0..wires.len()).collect(),
                            permutation: table.clone(),
                            phases: vec![0; table.len()],
                        },
                    };
                    self.apply(&[step], &wires);
                    self.put(*output, wires);
                }
                RawOp::ApplyUnitary {
                    input,
                    output,
                    steps,
                } => {
                    let wires = self.take(*input);
                    self.apply(steps, &wires);
                    self.put(*output, wires);
                }
                RawOp::QuantumIf {
                    control,
                    target,
                    control_out,
                    target_out,
                    zero_ops,
                    one_ops,
                } => {
                    let control_wires = self.take(*control);
                    let target_wires = self.take(*target);
                    assert_eq!(control_wires.len(), 1);
                    let mut wires = target_wires.clone();
                    wires.extend(&control_wires);
                    for (when_one, operations) in [(false, zero_ops), (true, one_ops)] {
                        for operation in operations {
                            let mut step = unitary_step(operation);
                            step.controls.push(BitControl {
                                index: target_wires.len(),
                                when_one,
                            });
                            self.apply(&[step], &wires);
                        }
                    }
                    self.put(*control_out, control_wires);
                    self.put(*target_out, target_wires);
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
                    let branch = self.classical[condition];
                    let mut classical = self.classical.clone();
                    self.operations(if branch { then_ops } else { else_ops });
                    let mut owners = BTreeMap::new();
                    let mut renamed_axes = vec![];
                    for phi in quantum_phis {
                        let wires = self.take(if branch {
                            phi.then_token
                        } else {
                            phi.else_token
                        });
                        assert_eq!(wires.len(), phi.output_wires.len());
                        // Phi IDs name the same ordered physical coordinates.
                        // Collect every rename before replacing any mapping.
                        renamed_axes
                            .extend(phi.output_wires.iter().copied().zip(self.indices(&wires)));
                        assert!(
                            owners
                                .insert(phi.output, phi.output_wires.clone())
                                .is_none()
                        );
                    }
                    assert!(
                        self.owners.is_empty(),
                        "branch must return every live owner"
                    );
                    self.owners = owners;
                    self.axes.extend(renamed_axes);
                    for phi in classical_phis {
                        let value = self.classical[&if branch { phi.then_id } else { phi.else_id }];
                        classical.insert(phi.output, value);
                    }
                    self.classical = classical;
                }
                _ => panic!("outside the small pure Raw oracle profile"),
            }
        }
    }
}

fn gate_step(gate: SingleGate, target: usize) -> CircuitStep {
    CircuitStep {
        controls: vec![],
        action: match gate {
            SingleGate::H => CircuitAction::Hadamard { target },
            SingleGate::X | SingleGate::Z | SingleGate::T => CircuitAction::Monomial {
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

fn unitary_step(step: &UnitaryStep) -> CircuitStep {
    match step {
        UnitaryStep::Gate { gate, target_index } => gate_step(*gate, *target_index),
        UnitaryStep::Cnot {
            control_index,
            target_index,
        } => {
            let mut step = gate_step(SingleGate::X, *target_index);
            step.controls.push(BitControl {
                index: *control_index,
                when_one: true,
            });
            step
        }
        UnitaryStep::Toffoli {
            control_a_index,
            control_b_index,
            target_index,
        } => {
            let mut step = gate_step(SingleGate::X, *target_index);
            step.controls.extend(
                [*control_a_index, *control_b_index].map(|index| BitControl {
                    index,
                    when_one: true,
                }),
            );
            step
        }
        UnitaryStep::ScalarPhase(phase) => CircuitStep {
            controls: vec![],
            action: CircuitAction::Monomial {
                indices: vec![],
                permutation: vec![0],
                phases: vec![match phase {
                    ScalarPhase::MinusOne => 4,
                    ScalarPhase::EighthTurn => 1,
                }],
            },
        },
    }
}

fn label(basis: usize, axes: &[usize]) -> usize {
    axes.iter().enumerate().fold(0, |label, (place, axis)| {
        label | (((basis >> axis) & 1) << place)
    })
}

fn replace_label(basis: usize, axes: &[usize], value: usize) -> usize {
    axes.iter()
        .enumerate()
        .fold(basis, |output, (place, axis)| {
            (output & !(1 << axis)) | (((value >> place) & 1) << axis)
        })
}

fn apply_steps(amplitudes: &mut Vec<Exact>, steps: &[CircuitStep], axes: &[usize], depth: usize) {
    for step in steps {
        let contract = match &step.action {
            CircuitAction::Contract {
                indices, evidence, ..
            } => {
                assert_eq!(indices.len(), evidence.signature().bits().unwrap());
                Some(raw_operator(evidence.implementation(), depth + 1))
            }
            _ => None,
        };
        let mut next = vec![Exact::ZERO; amplitudes.len()];
        for (basis, amplitude) in amplitudes.iter().copied().enumerate() {
            if !step
                .controls
                .iter()
                .all(|control| ((basis >> axes[control.index]) & 1 != 0) == control.when_one)
            {
                next[basis] = next[basis] + amplitude;
                continue;
            }
            match &step.action {
                CircuitAction::Contract {
                    indices, adjoint, ..
                } => {
                    let targets: Vec<_> = indices.iter().map(|index| axes[*index]).collect();
                    let column = label(basis, &targets);
                    let matrix = contract.as_ref().unwrap();
                    for (row, values) in matrix.iter().enumerate() {
                        let coefficient = if *adjoint {
                            matrix[column][row].conjugate()
                        } else {
                            values[column]
                        };
                        let output = replace_label(basis, &targets, row);
                        next[output] = next[output] + amplitude * coefficient;
                    }
                }
                CircuitAction::Hadamard { target } => {
                    let mask = 1 << axes[*target];
                    let zero = basis & !mask;
                    let scaled = amplitude * Exact::inverse_sqrt_two();
                    next[zero] = next[zero] + scaled;
                    next[zero | mask] =
                        next[zero | mask] + if basis & mask == 0 { scaled } else { -scaled };
                }
                CircuitAction::Monomial {
                    indices,
                    permutation,
                    phases,
                } => {
                    let targets: Vec<_> = indices.iter().map(|index| axes[*index]).collect();
                    let column = label(basis, &targets);
                    let output = replace_label(basis, &targets, usize::from(permutation[column]));
                    next[output] =
                        next[output] + amplitude * Exact::phase(usize::from(phases[column]));
                }
            }
        }
        *amplitudes = next;
    }
}

fn operator(width: usize, steps: &[CircuitStep]) -> Vec<Vec<Exact>> {
    assert!(
        width <= 3,
        "this exact checker intentionally covers small examples"
    );
    let dimension = 1 << width;
    let axes: Vec<_> = (0..width).collect();
    let mut matrix = vec![vec![Exact::ZERO; dimension]; dimension];
    for column in 0..dimension {
        let mut amplitudes = vec![Exact::ZERO; dimension];
        amplitudes[column] = Exact::ONE;
        apply_steps(&mut amplitudes, steps, &axes, 0);
        for (row, amplitude) in amplitudes.into_iter().enumerate() {
            matrix[row][column] = amplitude;
        }
    }
    matrix
}

fn assert_operator(width: usize, steps: &[CircuitStep], expected: impl Fn(usize, usize) -> Exact) {
    for (row, entries) in operator(width, steps).into_iter().enumerate() {
        for (column, amplitude) in entries.into_iter().enumerate() {
            assert_eq!(
                amplitude,
                expected(row, column),
                "matrix entry ({row}, {column})"
            );
        }
    }
}

#[test]
fn exact_scalar_arithmetic_matches_cyclotomic_and_hadamard_identities() {
    assert_eq!(Exact::phase(1) * Exact::phase(3), -Exact::ONE);
    assert_eq!(Exact::phase(1) * Exact::phase(7), Exact::ONE);
    let half = Exact::new([1, 0, 0, 0], 1);
    assert_eq!(Exact::inverse_sqrt_two() * Exact::inverse_sqrt_two(), half);
    assert_eq!(half + half, Exact::ONE);
    assert_eq!(half + -half, Exact::ZERO);
    assert_eq!(
        Exact::inverse_sqrt_two().conjugate(),
        Exact::inverse_sqrt_two()
    );
    assert_eq!(determinant_exponent(1, &[gate_step(SingleGate::H, 0)]), 4);
    for i in 0..8 {
        assert_eq!(Exact::phase(i).conjugate(), Exact::phase(8 - i));
        for j in 0..8 {
            assert_eq!(Exact::phase(i) * Exact::phase(j), Exact::phase(i + j));
        }
    }
}

// A small direct oracle check, without a compiler/native roundtrip: phi wire
// IDs are new names for the selected ordered coordinates, not new physical axes.
#[test]
fn exact_raw_oracle_retains_fresh_phi_axes_for_both_closed_branches() {
    use qleisli::ir::{BasisShape, Effect, QuantumPhi, QuantumPort};
    let t = TokenId;
    let w = WireId;
    for branch in [false, true] {
        let raw = RawProgram {
            quantum_inputs: vec![QuantumPort {
                token: t(0),
                wires: vec![w(0), w(1)],
                shape: BasisShape { bits: 2 },
            }],
            classical_inputs: vec![],
            operations: vec![
                RawOp::ClassicalConst {
                    value: branch,
                    output: ClassicalId(0),
                },
                RawOp::ClassicalBranch {
                    condition: ClassicalId(0),
                    then_ops: vec![
                        RawOp::Split {
                            input: t(0),
                            left: t(1),
                            right: t(2),
                            left_bits: 1,
                        },
                        RawOp::Gate {
                            gate: SingleGate::H,
                            input: t(1),
                            output: t(3),
                        },
                        RawOp::Join {
                            left: t(2),
                            right: t(3),
                            output: t(4),
                        },
                    ],
                    else_ops: vec![
                        RawOp::Split {
                            input: t(0),
                            left: t(5),
                            right: t(6),
                            left_bits: 1,
                        },
                        RawOp::Gate {
                            gate: SingleGate::X,
                            input: t(5),
                            output: t(7),
                        },
                        RawOp::Join {
                            left: t(7),
                            right: t(6),
                            output: t(8),
                        },
                    ],
                    quantum_phis: vec![QuantumPhi {
                        then_token: t(4),
                        else_token: t(8),
                        output: t(9),
                        output_wires: vec![w(10), w(11)],
                    }],
                    classical_phis: vec![],
                },
                RawOp::ApplyUnitary {
                    input: t(9),
                    output: t(10),
                    steps: vec![gate_step(SingleGate::T, 0)],
                },
            ],
            quantum_outputs: vec![t(10)],
            classical_outputs: vec![],
            declared_effect: Effect::Unitary,
        };
        let matrix = raw_operator(&raw, 0);
        for (row, entries) in matrix.iter().enumerate() {
            for (column, actual) in entries.iter().enumerate() {
                let (a, b) = (column & 1, column >> 1);
                let expected = if branch {
                    // H on a, return (b,r), then T on the first returned axis.
                    if row & 1 == b {
                        Exact::inverse_sqrt_two() * Exact::phase(b + 4 * a * (row >> 1))
                    } else {
                        Exact::ZERO
                    }
                } else if row == (1 - a) | (b << 1) {
                    Exact::phase(1 - a)
                } else {
                    Exact::ZERO
                };
                assert_eq!(
                    *actual, expected,
                    "branch {branch}, matrix entry ({row}, {column})"
                );
            }
        }
    }
}

const MIX: &str = "
unitary fn mix(q: Q<(Bit,Bit)>) -> Q<(Bit,Bit)> {
    let (a,b) = split(q);
    let a = t(h(a));
    let b = basis b as label { not label };
    let (a,b) = cnot(a,b);
    join(b,a)
}
";

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn adjoint_and_nested_axis_remapping_match_all_exact_matrix_entries() {
    // U|a,b> = sum_r (-1)^(a*r) zeta^r |b xor 1 xor r,r>/sqrt(2).
    let preparation = "let q = join(init0(),init0());";
    let forward = compiled_steps(MIX, preparation, "power(mix,1)(q)");
    assert_operator(2, &forward, |row, column| {
        let (a, b, r) = (column & 1, column >> 1, row >> 1);
        if row & 1 == b ^ 1 ^ r {
            Exact::inverse_sqrt_two() * Exact::phase(r + 4 * a * r)
        } else {
            Exact::ZERO
        }
    });
    // U^dagger|c,d> = sum_a (-1)^(a*d) zeta^(-d)|a,c xor 1 xor d>/sqrt(2).
    let backward = compiled_steps(MIX, preparation, "adjoint(mix)(q)");
    assert_operator(2, &backward, |row, column| {
        let (c, d, a, b) = (column & 1, column >> 1, row & 1, row >> 1);
        if b == c ^ 1 ^ d {
            Exact::inverse_sqrt_two() * Exact::phase(8 - d + 4 * a * d)
        } else {
            Exact::ZERO
        }
    });
    let nested = format!(
        "{MIX}
unitary fn nested(q: Q<((Bit,Bit),Bit)>) -> Q<((Bit,Bit),Bit)> {{
    let (ab,c) = split(q); let (a,b) = split(ab);
    let (c,a) = split(power(mix,1)(join(c,a)));
    join(join(b,c),a)
}}"
    );
    let steps = compiled_steps(
        &nested,
        "let q = join(join(init0(),init0()),init0());",
        "power(nested,1)(q)",
    );
    // Apply U to the ordered, nonadjacent pair (c,a), then return (b,c',a').
    assert_operator(3, &steps, |row, column| {
        let (a, b, c, r) = (column & 1, (column >> 1) & 1, column >> 2, row >> 2);
        if row & 1 == b && (row >> 1) & 1 == a ^ 1 ^ r {
            Exact::inverse_sqrt_two() * Exact::phase(r + 4 * c * r)
        } else {
            Exact::ZERO
        }
    });
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn finite_repetition_preserves_the_phase_of_a_noncommuting_operator() {
    // V = T X, so V|b> = zeta^(1-b)|1-b> and V^2 = zeta I.
    let definitions = "unitary fn forward(q: Q<Bit>) -> Q<Bit> { t(x(q)) }";
    for count in [0, 1, 2, 3, 8] {
        let steps = compiled_steps(
            definitions,
            "let q = init0();",
            &format!("power(forward,{count})(q)"),
        );
        assert_operator(1, &steps, |row, column| {
            if row == column ^ (count % 2) {
                Exact::phase(count / 2 + (count % 2) * (1 - column))
            } else {
                Exact::ZERO
            }
        });
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn nested_qif_preserves_zero_one_controls_and_branch_phases() {
    let definitions = "
unitary fn forward(q: Q<Bit>) -> Q<Bit> { t(x(q)) }
unitary fn backward(q: Q<Bit>) -> Q<Bit> { adjoint(forward)(q) }
unitary fn first(q: Q<(Bit,Bit)>) -> Q<(Bit,Bit)> {
    let (b,c) = split(q); let (b,c) = qif(b,c) { 0 => forward, 1 => backward }; join(b,c)
}
unitary fn second(q: Q<(Bit,Bit)>) -> Q<(Bit,Bit)> {
    let (b,c) = split(q); let (b,c) = qif(b,c) { 0 => z, 1 => t }; join(b,c)
}
unitary fn nested(q: Q<(Bit,(Bit,Bit))>) -> Q<(Bit,(Bit,Bit))> {
    let (a,bc) = split(q); let (a,bc) = qif(a,bc) { 0 => first, 1 => second }; join(a,bc)
}";
    let steps = compiled_steps(
        definitions,
        "let q = join(init0(),join(init0(),init0()));",
        "power(nested,1)(q)",
    );
    assert_operator(3, &steps, |row, column| {
        let (a, b, c) = (column & 1, (column >> 1) & 1, column >> 2);
        let (output, phase) = match (a, b) {
            (0, 0) => (column ^ 4, 1 - c), // V on c.
            (0, 1) => (column ^ 4, 8 - c), // V^dagger on c.
            (1, 0) => (column, 4 * c),     // Z on c.
            (1, 1) => (column, c),         // T on c.
            _ => unreachable!(),
        };
        if row == output {
            Exact::phase(phase)
        } else {
            Exact::ZERO
        }
    });
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn computed_scalar_phase_is_retained_on_unit_and_under_adjoint_and_control() {
    let definitions = "
classical fn yes(value: Unit) -> Bit { 1 }
unitary fn identity(q: Q<Unit>) -> Q<Unit> { q }
unitary fn phase(q: Q<Unit>) -> Q<Unit> { with_computed(q,yes) { |a| z(t(t(t(a)))) } }
unitary fn controlled(q: Q<(Bit,Unit)>) -> Q<(Bit,Unit)> {
    let (c,u) = split(q); let (c,u) = qif(c,u) { 0 => phase, 1 => identity }; join(c,u)
}";
    let preparation =
        "let pair = basis init0() as b { ((),b) }; let (u,b) = split(pair); discard(b);";
    // C_yes^dagger Z T^3 C_yes contributes zeta^7 on the one-dimensional space.
    for (operation, phase) in [("power(phase,1)(u)", 7), ("adjoint(phase)(u)", 1)] {
        let steps = compiled_steps(definitions, preparation, operation);
        assert_operator(0, &steps, |_, _| Exact::phase(phase));
    }
    let steps = compiled_steps(
        definitions,
        &format!("{preparation} let q = join(init0(),u);"),
        "power(controlled,1)(q)",
    );
    assert_operator(1, &steps, |row, column| {
        if row == column {
            Exact::phase(if column == 0 { 7 } else { 0 })
        } else {
            Exact::ZERO
        }
    });
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn ordinary_phase_gates_match_exact_operators_and_their_static_clients() {
    let imports = "use std::gate::{s,sdg,tdg,id}; unitary fn bit_identity(q:Q<Bit>)->Q<Bit>{id[type(Bit)](q)}";
    for (name, exponent) in [("s", 2), ("sdg", 6), ("tdg", 7)] {
        for (operation, power) in [
            (format!("power({name},1)(q)"), exponent),
            (format!("adjoint({name})(q)"), 8 - exponent),
            (format!("power({name},3)(q)"), 3 * exponent),
        ] {
            let steps = compiled_steps(imports, "let q = init0();", &operation);
            assert_operator(1, &steps, |row, column| {
                if row == column {
                    Exact::phase(power * column)
                } else {
                    Exact::ZERO
                }
            });
        }
        let definitions = format!(
            "{imports}
            unitary fn controlled(q:Q<(Bit,Bit)>)->Q<(Bit,Bit)> {{
                let (c,t) = split(q);
                let (c,t) = qif(c,t) {{ 0 => bit_identity, 1 => {name} }};
                join(c,t)
            }}"
        );
        let steps = compiled_steps(
            &definitions,
            "let q = join(init0(),init0());",
            "power(controlled,1)(q)",
        );
        assert_operator(2, &steps, |row, column| {
            if row == column {
                Exact::phase(if column == 3 { exponent } else { 0 })
            } else {
                Exact::ZERO
            }
        });
    }
    // Direct aliases must agree too, independently of static-call expansion.
    let steps = compiled_steps(
        &format!(
            "{imports}
        unitary fn direct(q:Q<Bit>)->Q<Bit>{{ global_phase_eighth(tdg(sdg(s(id[type(Bit)](q))))) }}"
        ),
        "let q = init0();",
        "power(direct,1)(q)",
    );
    assert_operator(1, &steps, |row, column| {
        if row == column {
            Exact::phase(1 + 15 * column)
        } else {
            Exact::ZERO
        }
    });
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn language_scalar_phase_retains_zero_width_control_and_basis_specific_expectations() {
    let imports = "use std::gate::id; unitary fn unit_identity(q:Q<Unit>)->Q<Unit>{id[type(Unit)](q)} unitary fn bit_identity(q:Q<Bit>)->Q<Bit>{id[type(Bit)](q)}";
    let unit = "let pair = basis init0() as b { ((),b) };
        let (q,b) = split(pair); discard(b);";
    for (operation, exponent) in [
        ("power(unit_identity,1)(q)", 0),
        ("power(global_phase_eighth,1)(q)", 1),
        ("adjoint(global_phase_eighth)(q)", 7),
        ("power(global_phase_eighth,8)(q)", 0),
    ] {
        let steps = compiled_steps(imports, unit, operation);
        assert_operator(0, &steps, |_, _| Exact::phase(exponent));
    }
    // Within one compiler, check both Unit and Bit meanings for the same names.
    let definitions = format!(
        "{imports}
        unitary fn mixed(q:Q<((Bit,Unit),Bit)>)->Q<((Bit,Unit),Bit)> {{
            let (cu,b) = split(q); let (c,u) = split(cu);
            let (c,u) = qif(c,u) {{ 0 => unit_identity, 1 => global_phase_eighth }};
            let (c,b) = qif(c,b) {{ 0 => bit_identity, 1 => global_phase_eighth }};
            join(join(c,u),b)
        }}"
    );
    let steps = compiled_steps(
        &definitions,
        &format!("{unit} let q = join(join(init0(),q),init0());"),
        "power(mixed,1)(q)",
    );
    assert_operator(2, &steps, |row, column| {
        if row == column {
            Exact::phase(2 * (column & 1))
        } else {
            Exact::ZERO
        }
    });
    let steps = compiled_steps(
        imports,
        "let q = join(init0(),init0());",
        "adjoint(global_phase_eighth)(q)",
    );
    assert_operator(2, &steps, |row, column| {
        if row == column {
            Exact::phase(7)
        } else {
            Exact::ZERO
        }
    });
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn scalar_source_action_adds_no_auxiliary_wire_and_aliases_keep_linear_types() {
    use qleisli::frontend::compile::{ErrorCode, check_project};
    let root = SourceRoot::new(
        "use std::state::init0;
\x20\x20\x20\x20\x20\x20\x20\x20
        observe fn main()->Unit { discard(global_phase_eighth(init0())); () }",
    );
    let verified = compile_project(&root.0).unwrap();
    assert_eq!(verified.program().operations.len(), 4);
    assert!(matches!(
        &verified.program().operations[0],
        RawOp::PackUnit { .. }
    ));
    assert!(
        matches!(&verified.program().operations[1], RawOp::LiftBasis { output_wires, table, .. } if output_wires.len() == 1 && table == &[0])
    );
    assert!(
        matches!(&verified.program().operations[2], RawOp::ApplyUnitary { steps, .. }
        if steps.len() == 1 && matches!(&steps[0].action,
            CircuitAction::Monomial { indices, permutation, phases }
            if indices.is_empty() && permutation == &[0] && phases == &[1]))
    );
    for (source, code) in [
        (
            "use std::gate::id; unitary fn f(q:Q<Unit>)->(Q<Unit>,Q<Unit>){(id[type(Unit)](q),id[type(Unit)](q))}",
            ErrorCode::Ownership,
        ),
        (
            " unitary fn f(q:Bit)->Bit{global_phase_eighth(q)}",
            ErrorCode::TypeMismatch,
        ),
        (
            "use std::gate::s; unitary fn f(q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>{s(q)}",
            ErrorCode::TypeMismatch,
        ),
        (
            "use std::gate::tdg; unitary fn f(q:Q<Unit>)->Q<Unit>{power(tdg,0)(q)}",
            ErrorCode::TypeMismatch,
        ),
    ] {
        root.write("main.qli", source);
        assert_eq!(check_project(&root.0).unwrap_err().code, code);
    }
}

fn permutation_is_odd(permutation: &[usize]) -> bool {
    let mut odd = false;
    for (i, output) in permutation.iter().enumerate() {
        for later in &permutation[i + 1..] {
            odd ^= output > later;
        }
    }
    odd
}

// Leibniz determinant of the independently replayed matrix, including retained
// functions and all scalar phases. At most eight rows; no division or simulator.
fn determinant_exponent(width: usize, steps: &[CircuitStep]) -> usize {
    fn expand(matrix: &[Vec<Exact>], row: usize, columns: &mut Vec<usize>) -> Exact {
        if row == matrix.len() {
            return if permutation_is_odd(columns) {
                -Exact::ONE
            } else {
                Exact::ONE
            };
        }
        let mut sum = Exact::ZERO;
        for column in 0..matrix.len() {
            if !columns.contains(&column) && matrix[row][column] != Exact::ZERO {
                columns.push(column);
                sum = sum + matrix[row][column] * expand(matrix, row + 1, columns);
                columns.pop();
            }
        }
        sum
    }
    let determinant = expand(&operator(width, steps), 0, &mut vec![]);
    (0..8)
        .find(|exponent| determinant == Exact::phase(*exponent))
        .expect("determinant is an exact eighth root in this regression")
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn review_same_wire_obstructions_do_not_reject_semantic_unitaries() {
    let c3x = include_str!(
        "fixtures/frontend_v030/coherent-basis/current/ordinary-type-cutover/current/review_v023/c3x.qli"
    );
    let root = SourceRoot::new(&format!(
        "{IMPORTS}\n{c3x}
        observe fn main()->Unit {{
            discard(c3x(join(join(init0(),init0()),join(init0(),init0())))); ()
        }}"
    ));
    let verified = compile_project(&root.0).unwrap();
    let table = verified
        .program()
        .operations
        .iter()
        .find_map(|op| match op {
            RawOp::LiftBasis {
                table,
                output_wires,
                ..
            } => {
                assert_eq!(output_wires.len(), 4);
                Some(table)
            }
            _ => None,
        })
        .unwrap();
    let expected: Vec<u16> = (0..14).chain([15, 14]).collect();
    assert_eq!(table, &expected);
    assert!(permutation_is_odd(
        &table.iter().map(|x| usize::from(*x)).collect::<Vec<_>>()
    ));

    let steps = compiled_steps(
        "use std::transform::qft3;",
        "let q = join(join(init0(),init0()),init0());",
        "power(qft3,1)(q)",
    );
    assert_operator(3, &steps, |row, column| {
        Exact::phase(row * column) * Exact::inverse_sqrt_two() * Exact::new([1, 0, 0, 0], 1)
    });
    assert_eq!(determinant_exponent(3, &steps), 2, "det(F8) = i exactly");
    // Exercise conjugate transpose on retained ordinary function evidence too.
    let inverse = compiled_steps(
        "use std::transform::qft3;",
        "let q = join(join(init0(),init0()),init0());",
        "adjoint(qft3)(q)",
    );
    assert_operator(3, &inverse, |row, column| {
        Exact::phase((8 - (row * column) % 8) % 8)
            * Exact::inverse_sqrt_two()
            * Exact::new([1, 0, 0, 0], 1)
    });
    assert_eq!(
        determinant_exponent(3, &inverse),
        6,
        "det(F8†) = -i exactly"
    );
    // Embedded H/T/X and NCT generate only +/-1 at width 3 and +1 at width 4.
    for width in [3, 4] {
        let allowed = if width == 3 { vec![0, 4] } else { vec![0] };
        for (local_width, determinant) in [(1usize, 4usize), (1, 1), (2, 4), (3, 4)] {
            assert!(allowed.contains(&((determinant * (1 << (width - local_width))) % 8)));
        }
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn closed_classical_computation_selects_static_branches_and_preserves_output_axes() {
    let definitions = "
unitary fn choose(q: Q<(Bit,Bit)>) -> Q<(Bit,Bit)> {
    let (a,b) = split(q);
    let flag = if 1 { 0 xor not 0 } else { 0 };
    let a = if flag and 1 { t(x(a)) } else { z(a) };
    join(b,a)
}
unitary fn identity(q: Q<(Bit,Bit)>) -> Q<(Bit,Bit)> { q }
unitary fn control(q: Q<(Bit,(Bit,Bit))>) -> Q<(Bit,(Bit,Bit))> {
    let (c,p) = split(q);
    let (c,p) = qif(c,p) { 0 => identity, 1 => choose };
    join(c,p)
}";
    // U|a,b> = zeta^(1-a)|b,1-a>; both branch phis and final
    // ownership order participate in the exact inverse and controlled matrix.
    let preparation = "let q = join(init0(),init0());";
    let steps = compiled_steps(definitions, preparation, "power(choose,1)(q)");
    assert_operator(2, &steps, |row, column| {
        let a = column & 1;
        let b = column >> 1;
        if row == b | ((1 - a) << 1) {
            Exact::phase(1 - a)
        } else {
            Exact::ZERO
        }
    });
    let inverse = compiled_steps(definitions, preparation, "adjoint(choose)(q)");
    assert_operator(2, &inverse, |row, column| {
        let b = column & 1;
        let a = 1 - (column >> 1);
        if row == a | (b << 1) {
            Exact::phase(8 - (1 - a))
        } else {
            Exact::ZERO
        }
    });
    let else_definitions = definitions.replace("if 1 {", "if 0 {");
    let else_steps = compiled_steps(&else_definitions, preparation, "power(choose,1)(q)");
    assert_operator(2, &else_steps, |row, column| {
        let a = column & 1;
        let b = column >> 1;
        if row == b | (a << 1) {
            Exact::phase(4 * a)
        } else {
            Exact::ZERO
        }
    });
    let controlled = compiled_steps(
        definitions,
        "let q = join(init0(),join(init0(),init0()));",
        "power(control,1)(q)",
    );
    assert_operator(3, &controlled, |row, column| {
        let c = column & 1;
        let a = (column >> 1) & 1;
        let b = column >> 2;
        let (output, phase) = if c == 0 {
            (column, 0)
        } else {
            (c | (b << 1) | ((1 - a) << 2), 1 - a)
        };
        if row == output {
            Exact::phase(phase)
        } else {
            Exact::ZERO
        }
    });
    let scalar_definitions = "
classical fn one(u:Unit)->Bit { 1 }
unitary fn identity(q:Q<Unit>)->Q<Unit> { q }
unitary fn scalar(q:Q<Unit>)->Q<Unit> {
    if not 0 {
        if 1 and 0 { q } else { with_computed(q,one) { |a| z(t(a)) } }
    } else { q }
}
unitary fn controlled(q:Q<(Bit,Unit)>)->Q<(Bit,Unit)> {
    let (c,u)=split(q);
    let (c,u)=qif(c,u) { 0=>identity, 1=>scalar };
    join(c,u)
}";
    let scalar = compiled_steps(
        scalar_definitions,
        "let q=basis init0() as b { (b,()) };",
        "power(controlled,1)(q)",
    );
    assert_operator(1, &scalar, |row, column| {
        if row == column {
            Exact::phase(5 * column)
        } else {
            Exact::ZERO
        }
    });
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn product_pattern_lift_is_a_full_basis_permutation_under_inverse_and_control() {
    let definitions = "
unitary fn permute(q: Q<(Bit,Bit)>) -> Q<(Bit,Bit)> {
    basis q as (a,b) { (b,a xor b) }
}
unitary fn identity(q: Q<(Bit,Bit)>) -> Q<(Bit,Bit)> { q }
unitary fn control(q: Q<(Bit,(Bit,Bit))>) -> Q<(Bit,(Bit,Bit))> {
    let (c,p) = split(q);
    let (c,p) = qif(c,p) { 0 => identity, 1 => permute };
    join(c,p)
}";
    let inverse = compiled_steps(
        definitions,
        "let q=join(init0(),init0());",
        "adjoint(permute)(q)",
    );
    assert_operator(2, &inverse, |row, column| {
        let b = column & 1;
        let a = (column >> 1) ^ b;
        if row == a | (b << 1) {
            Exact::ONE
        } else {
            Exact::ZERO
        }
    });
    let controlled = compiled_steps(
        definitions,
        "let q=join(init0(),join(init0(),init0()));",
        "power(control,1)(q)",
    );
    assert_operator(3, &controlled, |row, column| {
        let c = column & 1;
        let a = (column >> 1) & 1;
        let b = column >> 2;
        let output = if c == 0 {
            column
        } else {
            c | (b << 1) | ((a ^ b) << 2)
        };
        if row == output {
            Exact::ONE
        } else {
            Exact::ZERO
        }
    });
}
