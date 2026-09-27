//! Differential checks use exact operators and numeric amplitudes, including
//! their complex phase. Generated cases are deterministic and dependency-free.

use std::sync::Arc;

use super::*;
use crate::contract::exact::{Budget, Exact, Matrix};
use crate::contract::{
    BasisType, CheckedContract, Circuit, Contract, DEFAULT_EXACT_WORK, Encoding, FunctionEvidence,
    FunctionIdentity,
};
use crate::ir::{BasisShape, BitControl, Effect, QuantumPort, RawProgram};

fn work() -> Budget {
    Budget::new(DEFAULT_EXACT_WORK)
}

fn execution_budget() -> ExecutionBudget {
    ExecutionBudget {
        remaining: 1_000_000,
        max: 1_000_000,
    }
}

fn basis(width: usize) -> BasisType {
    (0..width)
        .map(|_| BasisType::Bit)
        .reduce(BasisType::pair)
        .unwrap_or(BasisType::Unit)
}

fn close(actual: Complex, expected: Complex) {
    assert!(
        (actual.re - expected.re).abs() < 1e-12 && (actual.im - expected.im).abs() < 1e-12,
        "actual {actual:?}, expected {expected:?}"
    );
}

fn numeric(exact: Exact) -> Complex {
    let (re, im) = exact.components_f64();
    Complex { re, im }
}

struct Generator(u64);

impl Generator {
    fn choose(&mut self, bound: usize) -> usize {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1);
        ((self.0 >> 32) as usize) % bound
    }

    fn shuffle<T>(&mut self, values: &mut [T]) {
        for end in (1..values.len()).rev() {
            values.swap(end, self.choose(end + 1));
        }
    }

    fn steps(&mut self, width: usize, count: usize) -> Vec<CircuitStep> {
        (0..count)
            .map(|_| {
                let mut axes: Vec<_> = (0..width).collect();
                self.shuffle(&mut axes);
                let target_count = self.choose(width + 1);
                let (targets, remaining) = axes.split_at(target_count);
                let controls = remaining
                    .iter()
                    .filter_map(|&index| {
                        if self.choose(2) == 1 {
                            Some(BitControl {
                                index,
                                when_one: self.choose(2) == 1,
                            })
                        } else {
                            None
                        }
                    })
                    .collect();
                let action = if target_count == 1 && self.choose(2) == 1 {
                    CircuitAction::Hadamard { target: targets[0] }
                } else {
                    let dimension = 1 << target_count;
                    let mut permutation: Vec<_> = (0..dimension as u16).collect();
                    self.shuffle(&mut permutation);
                    CircuitAction::Monomial {
                        indices: targets.to_vec(),
                        permutation,
                        phases: (0..dimension).map(|_| self.choose(8) as u8).collect(),
                    }
                };
                CircuitStep { controls, action }
            })
            .collect()
    }
}

fn placed_index(label: usize, axes: &[usize]) -> usize {
    axes.iter().enumerate().fold(0, |index, (place, axis)| {
        index | (((label >> place) & 1) << axis)
    })
}

fn assert_numeric_matrix(circuit: &Circuit, expected: &Matrix) {
    let width = circuit.basis().bits().unwrap();
    let dimension = 1 << width;
    assert_eq!((expected.rows(), expected.cols()), (dimension, dimension));
    // Reverse the physical placement and leave a spectator on axis zero.
    let axes: Vec<_> = (1..=width).rev().collect();
    for column in 0..dimension {
        let mut component = Component {
            axes: (0..=width).map(|axis| WireId(axis as u32)).collect(),
            amplitudes: vec![Complex::ZERO; dimension * 2],
            tokens: BTreeMap::new(),
            classical: BTreeMap::new(),
        };
        component.amplitudes[placed_index(column, &axes)] = Complex::ONE;
        // The second spectator block carries a distinct phase and input.
        let other = column ^ (dimension - 1);
        component.amplitudes[placed_index(other, &axes) | 1] = Complex { re: 0.0, im: 0.5 };
        run_circuit(
            &mut component,
            &axes,
            circuit.steps(),
            &mut execution_budget(),
        )
        .unwrap();
        for row in 0..dimension {
            close(
                component.amplitudes[placed_index(row, &axes)],
                numeric(expected.get(row, column).unwrap()),
            );
            close(
                component.amplitudes[placed_index(row, &axes) | 1],
                numeric(expected.get(row, other).unwrap()) * Complex { re: 0.0, im: 0.5 },
            );
        }
    }
}

#[test]
fn generated_circuits_match_exact_amplitudes_adjoint_and_control_laws() {
    let mut generator = Generator(0x514c_4549_534c_4901);
    for width in 0..=3 {
        for case in 0..24 {
            let steps = generator.steps(width, 1 + case % 17);
            let circuit = Circuit::new(basis(width), steps.clone()).unwrap();
            let matrix = circuit.matrix(&mut work()).unwrap();
            assert_numeric_matrix(&circuit, &matrix);

            // The expected adjoint is computed by matrix transposition and
            // conjugation, independently of inversion of individual steps.
            let mut inverse_steps = steps;
            crate::contract::invert_steps(&mut inverse_steps);
            let inverse = Circuit::new(basis(width), inverse_steps).unwrap();
            let expected_inverse = matrix.adjoint(&mut work()).unwrap();
            assert_eq!(inverse.matrix(&mut work()).unwrap(), expected_inverse);
            assert_numeric_matrix(&inverse, &expected_inverse);

            let encoding = Encoding::identity(basis(width)).unwrap();
            let contract =
                Contract::new(encoding.clone(), encoding, matrix.clone(), &mut work()).unwrap();
            let checked = CheckedContract::check(circuit, contract, &mut work()).unwrap();
            let controlled = checked.controlled(&mut work()).unwrap();
            let dimension = matrix.rows() * 2;
            let mut entries = vec![Exact::zero(); dimension * dimension];
            // Independent block-diagonal specification, control is low bit.
            for row in 0..dimension {
                for col in 0..dimension {
                    entries[row * dimension + col] = match (row % 2, col % 2) {
                        (0, 0) if row == col => Exact::one(),
                        (1, 1) => matrix.get(row / 2, col / 2).unwrap(),
                        _ => Exact::zero(),
                    };
                }
            }
            let expected_control = Matrix::new(dimension, dimension, entries).unwrap();
            assert_eq!(
                controlled.circuit().matrix(&mut work()).unwrap(),
                expected_control
            );
            assert_numeric_matrix(controlled.circuit(), &expected_control);
        }
    }
}

fn auxiliary_component(zero: Complex, one: Complex) -> Component {
    Component {
        axes: vec![WireId(7)],
        amplitudes: vec![zero, one],
        tokens: BTreeMap::new(),
        classical: BTreeMap::new(),
    }
}

#[test]
fn certified_cleanup_alarm_is_relative_and_preserves_numerical_mass() {
    for scale in [1.0, 1e-20] {
        let dirty = auxiliary_component(Complex::ZERO, Complex::ONE.scaled(scale));
        assert!(matches!(
            dirty.remove_certified_zero(WireId(7)),
            Err(SimulationError::InconsistentVerifiedIr(
                "certified auxiliary has nonzero numerical leakage"
            ))
        ));
    }
    let zero = Complex { re: 0.2, im: -0.3 };
    let tiny = Complex { re: 1e-14, im: 0.0 };
    let cleaned = auxiliary_component(zero, tiny)
        .remove_certified_zero(WireId(7))
        .unwrap();
    assert!(cleaned.axes.is_empty());
    assert_eq!(cleaned.amplitudes[0].re, zero.re);
    assert_eq!(cleaned.amplitudes[0].im, zero.im);
    assert_eq!(cleaned.weight(), zero.norm_squared());
    assert_eq!(
        auxiliary_component(Complex::ZERO, Complex::ZERO)
            .remove_certified_zero(WireId(7))
            .unwrap()
            .weight(),
        0.0
    );
    for invalid in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY, f64::MAX] {
        for amplitude in [
            Complex {
                re: invalid,
                im: 0.0,
            },
            Complex {
                re: 0.0,
                im: invalid,
            },
        ] {
            for (zero, one) in [(amplitude, Complex::ZERO), (Complex::ZERO, amplitude)] {
                assert!(matches!(
                    auxiliary_component(zero, one).remove_certified_zero(WireId(7)),
                    Err(SimulationError::InconsistentVerifiedIr(_))
                ));
            }
        }
    }
}

#[test]
fn certified_cleanup_alarm_is_scale_invariant_at_underflow_boundaries() {
    for scale in [1.0, 1e-20, 1e-160, 1e-200, 1e-300] {
        // Exercise both real and imaginary leakage, including subnormal total
        // weight and amplitudes whose squared weights all underflow to zero.
        for (kept, leaked) in [
            (Complex::ONE, Complex { re: 0.0, im: -1.0 }),
            (Complex { re: 0.0, im: -1.0 }, Complex::ONE),
        ] {
            for ratio in [1e-4, 2e-6] {
                let dirty = auxiliary_component(kept.scaled(scale), leaked.scaled(scale * ratio));
                assert!(
                    matches!(
                        dirty.remove_certified_zero(WireId(7)),
                        Err(SimulationError::InconsistentVerifiedIr(
                            "certified auxiliary has nonzero numerical leakage"
                        ))
                    ),
                    "missed relative leakage at amplitude scale {scale:e}, ratio {ratio:e}",
                );
            }
            for ratio in [0.0, 5e-7] {
                let zero = kept.scaled(scale);
                let cleaned = auxiliary_component(zero, leaked.scaled(scale * ratio))
                    .remove_certified_zero(WireId(7))
                    .unwrap();
                assert!(cleaned.axes.is_empty());
                assert_eq!(cleaned.amplitudes.len(), 1);
                assert_eq!(cleaned.amplitudes[0].re.to_bits(), zero.re.to_bits());
                assert_eq!(cleaned.amplitudes[0].im.to_bits(), zero.im.to_bits());
            }
        }
    }
    // Dividing by the smallest amplitude is safe; forming its reciprocal is
    // not. A wholly dirty auxiliary must still alarm at this scale.
    let smallest = f64::from_bits(1);
    let dirty = auxiliary_component(Complex::ZERO, Complex::ONE.scaled(smallest));
    assert!(matches!(
        dirty.remove_certified_zero(WireId(7)),
        Err(SimulationError::InconsistentVerifiedIr(
            "certified auxiliary has nonzero numerical leakage"
        ))
    ));
}

fn raw_function(operations: Vec<RawOp>, output: TokenId) -> RawProgram {
    RawProgram {
        quantum_inputs: vec![QuantumPort {
            token: TokenId(0),
            wires: vec![WireId(10), WireId(20)],
            shape: BasisShape { bits: 2 },
        }],
        classical_inputs: vec![],
        operations,
        quantum_outputs: vec![output],
        classical_outputs: vec![],
        declared_effect: Effect::Unitary,
    }
}

fn monomial(indices: Vec<usize>, permutation: Vec<u16>, phases: Vec<u8>) -> CircuitStep {
    CircuitStep {
        controls: vec![],
        action: CircuitAction::Monomial {
            indices,
            permutation,
            phases,
        },
    }
}

fn physical_evidence(prefix: Vec<CircuitStep>) -> Arc<FunctionEvidence> {
    let auxiliary_h = CircuitStep {
        controls: vec![],
        action: CircuitAction::Hadamard { target: 2 },
    };
    let logical_phase = monomial(vec![0, 1], vec![0, 1, 2, 3], vec![0, 1, 0, 0]);
    let implementation = raw_function(
        vec![
            RawOp::ApplyUnitary {
                input: TokenId(0),
                output: TokenId(1),
                steps: prefix.clone(),
            },
            RawOp::CertifiedCompute {
                source: TokenId(1),
                source_out: TokenId(2),
                ancilla_wires: vec![WireId(99)],
                function: vec![0, 1, 0, 0],
                use_steps: vec![
                    auxiliary_h.clone(),
                    auxiliary_h,
                    monomial(vec![2], vec![0, 1], vec![0, 1]),
                ],
                logical_steps: vec![logical_phase.clone()],
            },
            RawOp::Split {
                input: TokenId(2),
                left: TokenId(3),
                right: TokenId(4),
                left_bits: 1,
            },
            RawOp::Join {
                left: TokenId(4),
                right: TokenId(3),
                output: TokenId(5),
            },
        ],
        TokenId(5),
    );
    let mut specified = prefix;
    specified.extend([
        logical_phase,
        monomial(vec![0, 1], vec![0, 2, 1, 3], vec![0; 4]),
    ]);
    let specification = raw_function(
        vec![RawOp::ApplyUnitary {
            input: TokenId(0),
            output: TokenId(1),
            steps: specified,
        }],
        TokenId(1),
    );
    Arc::new(
        FunctionEvidence::check(
            basis(2),
            implementation,
            specification,
            FunctionIdentity {
                implementation: "physical".into(),
                specification: "specified".into(),
                sources: vec![],
            },
            &mut work(),
        )
        .unwrap(),
    )
}

#[test]
fn physical_raw_auxiliary_execution_agrees_with_extracted_contracts() {
    let mut generator = Generator(0x514c_4549_534c_4902);
    for case in 0..16 {
        let evidence = physical_evidence(generator.steps(2, case));
        let physical = evidence.implementation();
        // Validation is independent of the test-only ability to execute an
        // open raw function on a supplied vector.
        crate::verify(physical.clone()).unwrap();
        let contracted = Circuit::new(
            basis(2),
            vec![CircuitStep {
                controls: vec![],
                action: CircuitAction::Contract {
                    indices: vec![0, 1],
                    evidence: evidence.clone(),
                    adjoint: false,
                },
            }],
        )
        .unwrap();
        assert_numeric_matrix(&contracted, evidence.meaning());
        for column in 0..4 {
            let mut state = Component {
                axes: vec![WireId(20), WireId(77), WireId(10)],
                amplitudes: vec![Complex::ZERO; 8],
                tokens: BTreeMap::from([(TokenId(0), vec![WireId(10), WireId(20)])]),
                classical: BTreeMap::new(),
            };
            state.amplitudes[placed_index(column, &[2, 0])] = Complex { re: 0.3, im: 0.4 };
            state.amplitudes[placed_index(column ^ 3, &[2, 0]) | 2] = Complex { re: -0.4, im: 0.3 };
            let result = execute_ops(
                vec![state.clone()],
                &physical.operations,
                SimulationLimits::default(),
                &mut execution_budget(),
            )
            .unwrap();
            assert_eq!(result.len(), 1);
            let actual = &result[0];
            assert!(!actual.axes.contains(&WireId(99)));
            let output_axes: Vec<_> = actual.tokens[&physical.quantum_outputs[0]]
                .iter()
                .map(|wire| actual.position(*wire).unwrap())
                .collect();
            run_circuit(
                &mut state,
                &[2, 0],
                contracted.steps(),
                &mut execution_budget(),
            )
            .unwrap();
            for label in 0..4 {
                for reference in 0..2 {
                    close(
                        actual.amplitudes[placed_index(label, &output_axes) | (reference << 1)],
                        state.amplitudes[placed_index(label, &[2, 0]) | (reference << 1)],
                    );
                }
            }
            // This failure proves that the raw path allocated the physical
            // auxiliary, even though the contracted path needs only 3 axes.
            let limits = SimulationLimits {
                max_qubits: 3,
                ..SimulationLimits::default()
            };
            assert!(matches!(
                execute_ops(
                    vec![state],
                    &physical.operations,
                    limits,
                    &mut execution_budget()
                ),
                Err(SimulationError::DimensionLimit {
                    required: 4,
                    max: 3
                })
            ));
        }

        // Retained evidence remains phase-correct under inversion and an
        // external negative control, with its interface axes reversed.
        for adjoint in [false, true] {
            let steps = vec![CircuitStep {
                controls: vec![BitControl {
                    index: 1,
                    when_one: false,
                }],
                action: CircuitAction::Contract {
                    indices: vec![2, 0],
                    evidence: evidence.clone(),
                    adjoint,
                },
            }];
            let circuit = Circuit::new(basis(3), steps).unwrap();
            let matrix = circuit.matrix(&mut work()).unwrap();
            assert_numeric_matrix(&circuit, &matrix);
        }
    }
}

#[test]
fn certified_compute_execution_alarms_if_internal_state_violates_exact_cleanup() {
    let evidence = physical_evidence(vec![]);
    let mut operation = evidence.implementation().operations[1].clone();
    if let RawOp::CertifiedCompute { use_steps, .. } = &mut operation {
        use_steps.push(monomial(vec![2], vec![1, 0], vec![0, 0]));
    }
    let mut invalid = evidence.implementation().clone();
    invalid.operations[1] = operation.clone();
    assert!(
        crate::verify(invalid).is_err(),
        "exact verification must reject before execution"
    );
    // Fault injection bypasses the public VerifiedProgram boundary only in
    // this private test, to make the runtime alarm reachable.
    let state = Component {
        axes: vec![WireId(10), WireId(20)],
        amplitudes: vec![Complex::ONE, Complex::ZERO, Complex::ZERO, Complex::ZERO],
        tokens: BTreeMap::from([(TokenId(1), vec![WireId(10), WireId(20)])]),
        classical: BTreeMap::new(),
    };
    assert!(matches!(
        execute_op(
            state,
            &operation,
            SimulationLimits::default(),
            &mut execution_budget()
        ),
        Err(SimulationError::InconsistentVerifiedIr(
            "certified auxiliary has nonzero numerical leakage"
        ))
    ));
}
