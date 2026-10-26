//! Structural controls and fresh native equations for the small executable slice.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;
use crate::contract::{BasisType, DEFAULT_EXACT_WORK};

fn phase_step(axis: usize, phase: u8) -> CircuitStep {
    CircuitStep {
        controls: vec![],
        action: CircuitAction::Monomial {
            indices: vec![axis],
            permutation: vec![0, 1],
            phases: vec![0, phase],
        },
    }
}

#[test]
fn zero_width_selector_preserves_internal_control_at_new_axis_zero() {
    let mut step = phase_step(2, 1);
    step.controls = vec![
        BitControl {
            index: 0,
            when_one: true,
        },
        BitControl {
            index: 1,
            when_one: false,
        },
    ];
    lift_arm(std::slice::from_mut(&mut step), 0, 2, 0, true).unwrap();
    assert_eq!(
        step.controls,
        vec![BitControl {
            index: 0,
            when_one: false
        }]
    );
    let CircuitAction::Monomial { indices, .. } = step.action else {
        panic!("phase action was lost")
    };
    assert_eq!(indices, [1]);
}

#[test]
fn conjugation_scaffolding_does_not_gain_ungranted_controls() {
    let before = phase_step(1, 7);
    let mut middle = CircuitStep {
        controls: vec![BitControl {
            index: 0,
            when_one: true,
        }],
        action: CircuitAction::Hadamard { target: 1 },
    };
    // Target-local negative predicates also retain their polarity.
    middle.controls.push(BitControl {
        index: 2,
        when_one: false,
    });
    let after = phase_step(1, 1);
    let mut steps = vec![before, middle, after];
    lift_arm(&mut steps, 2, 2, 2, true).unwrap();
    assert!(steps[0].controls.is_empty() && steps[2].controls.is_empty());
    assert_eq!(
        steps[1].controls,
        vec![
            BitControl {
                index: 3,
                when_one: false
            },
            BitControl {
                index: 0,
                when_one: false
            },
            BitControl {
                index: 1,
                when_one: true
            },
        ]
    );
}

#[test]
fn malformed_synthetic_control_is_not_reinterpreted() {
    let mut action_on_selector = phase_step(0, 1);
    assert!(lift_arm(std::slice::from_mut(&mut action_on_selector), 1, 1, 1, true).is_err());
    for controls in [
        vec![BitControl {
            index: 0,
            when_one: false,
        }],
        vec![
            BitControl {
                index: 0,
                when_one: true
            };
            2
        ],
    ] {
        let mut step = phase_step(1, 1);
        step.controls = controls;
        assert!(lift_arm(std::slice::from_mut(&mut step), 1, 1, 1, true).is_err());
    }
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn native_full_circuit_refuses_phase_polarity_reference_axis_and_arm_faults() {
    let kernel =
        crate::interchange::native::Kernel::selected(crate::edition::Edition::E2026).unwrap();
    let signature = BasisType::pair(
        BasisType::Bit,
        BasisType::pair(BasisType::Bit, BasisType::Bit),
    );
    let positive = vec![CircuitStep {
        controls: vec![BitControl {
            index: 0,
            when_one: true,
        }],
        action: CircuitAction::Monomial {
            indices: vec![1],
            permutation: vec![0, 1],
            phases: vec![0, 1],
        },
    }];
    // Independent controlled phase tensored with identity on the reference.
    // Control is low axis 0; target is axis 1; reference is axis 2.
    let expected = Matrix::new(
        8,
        8,
        (0..64)
            .map(|index| {
                if index / 8 != index % 8 {
                    Exact::zero()
                } else {
                    Exact::phase(i32::from((index / 8) & 3 == 3))
                }
            })
            .collect(),
    )
    .unwrap();
    let circuit = Circuit::new(signature.clone(), positive.clone()).unwrap();
    check_native(
        &kernel,
        &circuit,
        expected.clone(),
        &mut Budget::new(DEFAULT_EXACT_WORK),
    )
    .unwrap();
    for fault in 0..5 {
        let mut steps = positive.clone();
        match fault {
            0 => {
                let CircuitAction::Monomial { phases, .. } = &mut steps[0].action else {
                    panic!("expected phase action")
                };
                phases[1] = 7;
            }
            1 => steps[0].controls[0].when_one = false,
            2 => {
                // Target-only phase is valid and differs on the other sector;
                // no malformed or overlapping-axis rejection is the oracle.
                steps[0].controls.clear();
            }
            3 => {
                steps[0].controls.clear();
                let CircuitAction::Monomial { indices, .. } = &mut steps[0].action else {
                    panic!("expected phase action")
                };
                indices[0] = 2;
            }
            _ => steps.clear(),
        }
        let candidate = Circuit::new(signature.clone(), steps).unwrap();
        assert_eq!(
            check_native(
                &kernel,
                &candidate,
                expected.clone(),
                &mut Budget::new(DEFAULT_EXACT_WORK)
            )
            .unwrap_err(),
            ContractError::EquationMismatch
        );
    }
}
