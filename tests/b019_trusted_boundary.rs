//! Independent finite audit of retained evidence under axis/control transport.

use qleisli::contract::exact::{Budget, Exact};
use qleisli::contract::{
    BasisType, Circuit, DEFAULT_EXACT_WORK, FunctionEvidence, FunctionIdentity,
};
use qleisli::ir::*;
use std::sync::Arc;

fn work() -> Budget {
    Budget::new(DEFAULT_EXACT_WORK)
}

#[test]
fn every_two_bit_permutation_retains_phase_under_control_axis_transport_and_adjoint() {
    let pair = BasisType::pair(BasisType::Bit, BasisType::Bit);
    let triple = BasisType::pair(pair.clone(), BasisType::Bit);
    let mut checked = 0;
    // Enumerate independently, without using the circuit inversion/remapping helpers.
    for a in 0u16..4 {
        for b in 0u16..4 {
            for c in 0u16..4 {
                for d in 0u16..4 {
                    let permutation = [a, b, c, d];
                    if (0..4).any(|i| (i + 1..4).any(|j| permutation[i] == permutation[j])) {
                        continue;
                    }
                    for shift in 0u8..8 {
                        let phases: Vec<_> = (0u8..4).map(|x| (3 * x + shift) % 8).collect();
                        let raw = RawProgram {
                            quantum_inputs: vec![QuantumPort {
                                token: TokenId(0),
                                wires: vec![WireId(9), WireId(3)],
                                shape: BasisShape { bits: 2 },
                            }],
                            classical_inputs: vec![],
                            operations: vec![RawOp::ApplyUnitary {
                                input: TokenId(0),
                                output: TokenId(1),
                                steps: vec![CircuitStep {
                                    controls: vec![],
                                    action: CircuitAction::Monomial {
                                        indices: vec![0, 1],
                                        permutation: permutation.to_vec(),
                                        phases: phases.clone(),
                                    },
                                }],
                            }],
                            quantum_outputs: vec![TokenId(1)],
                            classical_outputs: vec![],
                            declared_effect: Effect::Unitary,
                        };
                        let evidence = Arc::new(
                            FunctionEvidence::check(
                                pair.clone(),
                                raw.clone(),
                                raw,
                                FunctionIdentity {
                                    implementation: "audit::implementation".into(),
                                    specification: "audit::target".into(),
                                    sources: vec![],
                                },
                                &mut work(),
                            )
                            .unwrap(),
                        );
                        for first in 0usize..3 {
                            for second in 0usize..3 {
                                if first == second {
                                    continue;
                                }
                                let control = 3 - first - second;
                                for when_one in [false, true] {
                                    for adjoint in [false, true] {
                                        let matrix = Circuit::new(
                                            triple.clone(),
                                            vec![CircuitStep {
                                                controls: vec![BitControl {
                                                    index: control,
                                                    when_one,
                                                }],
                                                action: CircuitAction::Contract {
                                                    indices: vec![first, second],
                                                    evidence: Arc::clone(&evidence),
                                                    adjoint,
                                                },
                                            }],
                                        )
                                        .unwrap()
                                        .matrix(&mut work())
                                        .unwrap();
                                        for input in 0usize..8 {
                                            let mut output = input;
                                            let mut exponent = 0i32;
                                            if (input & (1 << control) != 0) == when_one {
                                                let local = ((input >> first) & 1)
                                                    | (((input >> second) & 1) << 1);
                                                let target = if adjoint {
                                                    permutation
                                                        .iter()
                                                        .position(|&x| usize::from(x) == local)
                                                        .unwrap()
                                                } else {
                                                    usize::from(permutation[local])
                                                };
                                                exponent = if adjoint {
                                                    -i32::from(phases[target])
                                                } else {
                                                    i32::from(phases[local])
                                                };
                                                output = (input & !((1 << first) | (1 << second)))
                                                    | ((target & 1) << first)
                                                    | (((target >> 1) & 1) << second);
                                            }
                                            for row in 0usize..8 {
                                                let expected = if row == output {
                                                    Exact::phase(exponent)
                                                } else {
                                                    Exact::zero()
                                                };
                                                assert_eq!(matrix.get(row, input), Some(expected));
                                            }
                                        }
                                        checked += 1;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(checked, 24 * 8 * 6 * 2 * 2);
}
