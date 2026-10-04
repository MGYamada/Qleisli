mod common;
use common::accept;
use qleisli::ir::{
    BasisShape, ClassicalId, ClassicalPhi, Control, Effect, ProtectedBit, ProtectedRegion,
    ProtectedUse, QuantumPhi, QuantumPort, RawOp, RawProgram, ScalarPhase, SingleGate,
    TargetTransition, TokenId, UnitaryStep, WireId,
};

fn t(id: u32) -> TokenId {
    TokenId(id)
}

fn w(id: u32) -> WireId {
    WireId(id)
}

fn c(id: u32) -> ClassicalId {
    ClassicalId(id)
}

fn bit_port(token: u32, wire: u32) -> QuantumPort {
    QuantumPort {
        token: t(token),
        wires: vec![w(wire)],
        shape: BasisShape::BIT,
    }
}

fn program(
    quantum_inputs: Vec<QuantumPort>,
    classical_inputs: Vec<ClassicalId>,
    operations: Vec<RawOp>,
    quantum_outputs: Vec<TokenId>,
    classical_outputs: Vec<ClassicalId>,
    declared_effect: Effect,
) -> RawProgram {
    RawProgram {
        quantum_inputs,
        classical_inputs,
        operations,
        quantum_outputs,
        classical_outputs,
        declared_effect,
    }
}

fn rejected(program: RawProgram, phrase: &str) {
    let error = accept(program).expect_err("malformed IR must be rejected");
    assert!(
        matches!(error.code, "invalid_ir" | "contract" | "limit" | "format"),
        "expected rejection for {phrase:?}, got {error}"
    );
}

#[test]
fn appended_classical_history_fits_the_native_deadline() {
    // A small zero-qubit program previously exhausted the 60-second deadline:
    // every step checked a growing history with nested membership scans.
    let count = 6_000u32;
    let operations = (0..count)
        .map(|id| RawOp::ClassicalConst {
            value: false,
            output: c(id),
        })
        .collect();
    let checked = accept(program(
        vec![],
        vec![],
        operations,
        vec![],
        vec![c(count - 1)],
        Effect::Observe,
    ))
    .expect("append-only classical histories must fit the native deadline");
    assert_eq!(checked.program().operations.len(), count as usize);
    assert_eq!(checked.program().classical_outputs, vec![c(count - 1)]);
}

#[test]
#[ignore = "historical Rust scaling experiment; maximum-size runs are deferred"]
fn many_live_wires_do_not_require_quadratic_duplicate_checks() {
    let count = 80_000u32;
    let operations = (0..count)
        .map(|id| RawOp::Init0 {
            output: t(id),
            wire: w(id),
        })
        .collect();
    let checked = accept(program(
        vec![],
        vec![],
        operations,
        (0..count).map(t).collect(),
        vec![],
        Effect::Iso,
    ))
    .unwrap();
    assert_eq!(checked.program().quantum_outputs.len(), count as usize);
}

#[test]
#[ignore = "historical Rust scaling experiment; maximum-size runs are deferred"]
fn many_branches_share_freshness_history_without_leaking_classical_scopes() {
    let mut operations = Vec::new();
    let mut condition = c(0);
    for index in 0..8_000u32 {
        let then_id = c(index * 3 + 1);
        let else_id = c(index * 3 + 2);
        let output = c(index * 3 + 3);
        operations.push(RawOp::ClassicalBranch {
            condition,
            then_ops: vec![RawOp::ClassicalNot {
                input: condition,
                output: then_id,
            }],
            else_ops: vec![RawOp::ClassicalNot {
                input: condition,
                output: else_id,
            }],
            quantum_phis: vec![],
            classical_phis: vec![ClassicalPhi {
                then_id,
                else_id,
                output,
            }],
        });
        condition = output;
    }
    accept(program(
        vec![],
        vec![c(0)],
        operations,
        vec![],
        vec![condition],
        Effect::Unitary,
    ))
    .unwrap();

    rejected(
        program(
            vec![],
            vec![c(0)],
            vec![RawOp::ClassicalBranch {
                condition: c(0),
                then_ops: vec![RawOp::ClassicalNot {
                    input: c(0),
                    output: c(1),
                }],
                else_ops: vec![RawOp::ClassicalNot {
                    input: c(1),
                    output: c(2),
                }],
                quantum_phis: vec![],
                classical_phis: vec![],
            }],
            vec![],
            vec![],
            Effect::Unitary,
        ),
        "not defined in this scope",
    );
}

#[test]
fn nested_classical_phi_is_visible_in_its_parent_arm() {
    let inner = RawOp::ClassicalBranch {
        condition: c(0),
        then_ops: vec![RawOp::ClassicalNot {
            input: c(0),
            output: c(1),
        }],
        else_ops: vec![RawOp::ClassicalNot {
            input: c(0),
            output: c(2),
        }],
        quantum_phis: vec![],
        classical_phis: vec![ClassicalPhi {
            then_id: c(1),
            else_id: c(2),
            output: c(3),
        }],
    };
    let outer = RawOp::ClassicalBranch {
        condition: c(0),
        then_ops: vec![inner],
        else_ops: vec![RawOp::ClassicalNot {
            input: c(0),
            output: c(4),
        }],
        quantum_phis: vec![],
        classical_phis: vec![ClassicalPhi {
            then_id: c(3),
            else_id: c(4),
            output: c(5),
        }],
    };
    accept(program(
        vec![],
        vec![c(0)],
        vec![outer],
        vec![],
        vec![c(5)],
        Effect::Unitary,
    ))
    .unwrap();
}

#[test]
fn classical_phis_cannot_read_outputs_of_the_same_merge() {
    rejected(
        program(
            vec![],
            vec![c(0)],
            vec![RawOp::ClassicalBranch {
                condition: c(0),
                then_ops: vec![],
                else_ops: vec![],
                quantum_phis: vec![],
                classical_phis: vec![
                    ClassicalPhi {
                        then_id: c(0),
                        else_id: c(0),
                        output: c(1),
                    },
                    ClassicalPhi {
                        then_id: c(1),
                        else_id: c(0),
                        output: c(2),
                    },
                ],
            }],
            vec![],
            vec![c(2)],
            Effect::Unitary,
        ),
        "undefined arm value",
    );
}

#[test]
fn bell_preparation_split_and_partial_measurement() {
    let bell = program(
        vec![],
        vec![],
        vec![
            RawOp::Init0 {
                output: t(0),
                wire: w(0),
            },
            RawOp::Gate {
                gate: SingleGate::H,
                input: t(0),
                output: t(1),
            },
            RawOp::LiftBasis {
                input: t(1),
                output: t(2),
                output_wires: vec![w(0), w(1)],
                table: vec![0, 3],
            },
            RawOp::Split {
                input: t(2),
                left: t(3),
                right: t(4),
                left_bits: 1,
            },
            RawOp::MeasureZ {
                input: t(3),
                output: c(0),
            },
            RawOp::MeasureZ {
                input: t(4),
                output: c(1),
            },
        ],
        vec![],
        vec![c(0), c(1)],
        Effect::Observe,
    );
    let checked = accept(bell).unwrap();
    assert_eq!(checked.derived_effect(), Effect::Observe);
    assert_eq!(checked.raw().classical_outputs, vec![c(0), c(1)]);
}

#[test]
fn computed_phase_oracle_has_checked_zero_return_scope() {
    let oracle = program(
        vec![bit_port(0, 0)],
        vec![],
        vec![RawOp::ComputeUseUncompute {
            source: t(0),
            source_out: t(1),
            targets: vec![],
            ancilla_wires: vec![w(1)],
            function: vec![1, 0],
            use_ops: vec![ProtectedUse::ProtectedGate {
                bit: ProtectedBit {
                    region: ProtectedRegion::Ancilla,
                    index: 0,
                },
                gate: SingleGate::Z,
            }],
        }],
        vec![t(1)],
        vec![],
        Effect::Unitary,
    );
    assert_eq!(accept(oracle).unwrap().derived_effect(), Effect::Unitary);
}

#[test]
fn computed_scope_can_control_a_target_without_changing_protected_bits() {
    let controlled = program(
        vec![bit_port(0, 0), bit_port(1, 1)],
        vec![],
        vec![RawOp::ComputeUseUncompute {
            source: t(0),
            source_out: t(2),
            targets: vec![TargetTransition {
                input: t(1),
                output: t(3),
            }],
            ancilla_wires: vec![w(2)],
            function: vec![0, 1],
            use_ops: vec![ProtectedUse::ControlledTargetGate {
                controls: vec![Control {
                    bit: ProtectedBit {
                        region: ProtectedRegion::Ancilla,
                        index: 0,
                    },
                    when_one: true,
                }],
                target_index: 0,
                gate: SingleGate::H,
            }],
        }],
        vec![t(2), t(3)],
        vec![],
        Effect::Unitary,
    );
    accept(controlled).unwrap();
}

#[test]
fn measurement_feedback_merges_exclusive_branch_resources() {
    let feedback = program(
        vec![bit_port(0, 0), bit_port(1, 1)],
        vec![],
        vec![
            RawOp::MeasureZ {
                input: t(0),
                output: c(0),
            },
            RawOp::ClassicalBranch {
                condition: c(0),
                then_ops: vec![RawOp::Gate {
                    gate: SingleGate::X,
                    input: t(1),
                    output: t(2),
                }],
                else_ops: vec![],
                quantum_phis: vec![QuantumPhi {
                    then_token: t(2),
                    else_token: t(1),
                    output: t(3),
                    output_wires: vec![w(2)],
                }],
                classical_phis: vec![],
            },
        ],
        vec![t(3)],
        vec![c(0)],
        Effect::Observe,
    );
    assert_eq!(accept(feedback).unwrap().derived_effect(), Effect::Observe);
}

#[test]
fn copied_quantum_token_is_rejected_even_for_unit() {
    rejected(
        program(
            vec![QuantumPort {
                token: t(0),
                wires: vec![],
                shape: BasisShape::UNIT,
            }],
            vec![],
            vec![RawOp::Join {
                left: t(0),
                right: t(0),
                output: t(1),
            }],
            vec![t(1)],
            vec![],
            Effect::Unitary,
        ),
        "used twice",
    );
}

#[test]
fn a_unit_register_can_be_split_into_two_unit_registers() {
    let unit = program(
        vec![QuantumPort {
            token: t(0),
            wires: vec![],
            shape: BasisShape::UNIT,
        }],
        vec![],
        vec![
            RawOp::Split {
                input: t(0),
                left: t(1),
                right: t(2),
                left_bits: 0,
            },
            RawOp::Join {
                left: t(1),
                right: t(2),
                output: t(3),
            },
        ],
        vec![t(3)],
        vec![],
        Effect::Unitary,
    );
    accept(unit).unwrap();
}

#[test]
fn measured_token_cannot_be_used_again() {
    rejected(
        program(
            vec![bit_port(0, 0)],
            vec![],
            vec![
                RawOp::MeasureZ {
                    input: t(0),
                    output: c(0),
                },
                RawOp::Gate {
                    gate: SingleGate::H,
                    input: t(0),
                    output: t(1),
                },
            ],
            vec![],
            vec![c(0)],
            Effect::Observe,
        ),
        "already consumed",
    );
}

#[test]
fn implicit_drop_is_rejected() {
    rejected(
        program(
            vec![bit_port(0, 0)],
            vec![],
            vec![],
            vec![],
            vec![],
            Effect::Iso,
        ),
        "omitted",
    );
}

#[test]
fn noninjective_and_partial_lifts_are_rejected() {
    for table in [vec![0, 0], vec![0]] {
        let phrase = if table.len() == 1 {
            "not total"
        } else {
            "not injective"
        };
        rejected(
            program(
                vec![bit_port(0, 0)],
                vec![],
                vec![RawOp::LiftBasis {
                    input: t(0),
                    output: t(1),
                    output_wires: vec![w(0)],
                    table,
                }],
                vec![t(1)],
                vec![],
                Effect::Iso,
            ),
            phrase,
        );
    }
}

#[test]
fn growing_lift_cannot_claim_unitary() {
    rejected(
        program(
            vec![bit_port(0, 0)],
            vec![],
            vec![RawOp::LiftBasis {
                input: t(0),
                output: t(1),
                output_wires: vec![w(0), w(1)],
                table: vec![0, 3],
            }],
            vec![t(1)],
            vec![],
            Effect::Unitary,
        ),
        "effect",
    );
}

#[test]
fn measurement_cannot_claim_pure_effect() {
    rejected(
        program(
            vec![bit_port(0, 0)],
            vec![],
            vec![RawOp::MeasureZ {
                input: t(0),
                output: c(0),
            }],
            vec![],
            vec![c(0)],
            Effect::Iso,
        ),
        "effect",
    );
}

#[test]
fn destructive_reset_requires_new_logical_wire() {
    rejected(
        program(
            vec![bit_port(0, 0)],
            vec![],
            vec![RawOp::Reset {
                input: t(0),
                output: t(1),
                fresh_wire: w(0),
            }],
            vec![t(1)],
            vec![],
            Effect::Observe,
        ),
        "not globally fresh",
    );
}

#[test]
fn use_that_changes_source_or_ancilla_basis_is_rejected() {
    for region in [ProtectedRegion::Source, ProtectedRegion::Ancilla] {
        rejected(
            program(
                vec![bit_port(0, 0)],
                vec![],
                vec![RawOp::ComputeUseUncompute {
                    source: t(0),
                    source_out: t(1),
                    targets: vec![],
                    ancilla_wires: vec![w(1)],
                    function: vec![0, 1],
                    use_ops: vec![ProtectedUse::ProtectedGate {
                        bit: ProtectedBit { region, index: 0 },
                        gate: SingleGate::H,
                    }],
                }],
                vec![t(1)],
                vec![],
                Effect::Unitary,
            ),
            "zero return is unproved",
        );
    }
}

#[test]
fn compute_scope_rejects_partial_function_and_ancilla_wire_reuse() {
    for (function, ancilla, phrase) in [
        (vec![0], w(1), "not total"),
        (vec![0, 1], w(0), "not globally fresh"),
    ] {
        rejected(
            program(
                vec![bit_port(0, 0)],
                vec![],
                vec![RawOp::ComputeUseUncompute {
                    source: t(0),
                    source_out: t(1),
                    targets: vec![],
                    ancilla_wires: vec![ancilla],
                    function,
                    use_ops: vec![],
                }],
                vec![t(1)],
                vec![],
                Effect::Unitary,
            ),
            phrase,
        );
    }
}

#[test]
fn computed_predicate_need_not_be_injective_because_xor_compute_is_reversible() {
    let constant_predicate = program(
        vec![bit_port(0, 0)],
        vec![],
        vec![RawOp::ComputeUseUncompute {
            source: t(0),
            source_out: t(1),
            targets: vec![],
            ancilla_wires: vec![w(1)],
            function: vec![1, 1],
            use_ops: vec![ProtectedUse::ProtectedGate {
                bit: ProtectedBit {
                    region: ProtectedRegion::Ancilla,
                    index: 0,
                },
                gate: SingleGate::Z,
            }],
        }],
        vec![t(1)],
        vec![],
        Effect::Unitary,
    );
    accept(constant_predicate).unwrap();
}

#[test]
fn conditional_scalar_phase_preserves_unit_target_phase() {
    let phased = program(
        vec![bit_port(0, 0)],
        vec![],
        vec![RawOp::ComputeUseUncompute {
            source: t(0),
            source_out: t(1),
            targets: vec![],
            ancilla_wires: vec![],
            function: vec![0, 0],
            use_ops: vec![ProtectedUse::ControlledPhase {
                controls: vec![Control {
                    bit: ProtectedBit {
                        region: ProtectedRegion::Source,
                        index: 0,
                    },
                    when_one: true,
                }],
                phase: ScalarPhase::MinusOne,
            }],
        }],
        vec![t(1)],
        vec![],
        Effect::Unitary,
    );
    accept(phased).unwrap();
}

#[test]
fn branch_rejects_unmerged_or_mismatched_quantum_contexts() {
    rejected(
        program(
            vec![],
            vec![c(0)],
            vec![RawOp::ClassicalBranch {
                condition: c(0),
                then_ops: vec![RawOp::Init0 {
                    output: t(0),
                    wire: w(0),
                }],
                else_ops: vec![],
                quantum_phis: vec![],
                classical_phis: vec![],
            }],
            vec![],
            vec![],
            Effect::Iso,
        ),
        "unmerged",
    );

    rejected(
        program(
            vec![bit_port(0, 0)],
            vec![c(0)],
            vec![RawOp::ClassicalBranch {
                condition: c(0),
                then_ops: vec![],
                else_ops: vec![RawOp::Split {
                    input: t(0),
                    left: t(1),
                    right: t(2),
                    left_bits: 0,
                }],
                quantum_phis: vec![QuantumPhi {
                    then_token: t(0),
                    else_token: t(1),
                    output: t(3),
                    output_wires: vec![w(1)],
                }],
                classical_phis: vec![],
            }],
            vec![t(3)],
            vec![],
            Effect::Unitary,
        ),
        "shapes do not match",
    );
}

#[test]
fn branch_effects_cannot_be_hidden_and_arm_ids_must_be_globally_fresh() {
    rejected(
        program(
            vec![bit_port(0, 0)],
            vec![c(0)],
            vec![RawOp::ClassicalBranch {
                condition: c(0),
                then_ops: vec![RawOp::Discard { input: t(0) }],
                else_ops: vec![RawOp::Discard { input: t(0) }],
                quantum_phis: vec![],
                classical_phis: vec![],
            }],
            vec![],
            vec![],
            Effect::Iso,
        ),
        "effect",
    );

    rejected(
        program(
            vec![],
            vec![c(0)],
            vec![RawOp::ClassicalBranch {
                condition: c(0),
                then_ops: vec![
                    RawOp::Init0 {
                        output: t(0),
                        wire: w(0),
                    },
                    RawOp::Discard { input: t(0) },
                ],
                else_ops: vec![
                    RawOp::Init0 {
                        output: t(0),
                        wire: w(0),
                    },
                    RawOp::Discard { input: t(0) },
                ],
                quantum_phis: vec![],
                classical_phis: vec![],
            }],
            vec![],
            vec![],
            Effect::Observe,
        ),
        "not globally fresh",
    );
}

#[test]
fn quantum_basis_cannot_be_used_as_classical_branch_guard() {
    rejected(
        program(
            vec![bit_port(0, 0)],
            vec![],
            vec![RawOp::ClassicalBranch {
                condition: c(0),
                then_ops: vec![],
                else_ops: vec![],
                quantum_phis: vec![QuantumPhi {
                    then_token: t(0),
                    else_token: t(0),
                    output: t(1),
                    output_wires: vec![w(1)],
                }],
                classical_phis: vec![],
            }],
            vec![t(1)],
            vec![],
            Effect::Unitary,
        ),
        "classical bit",
    );
}

#[test]
fn wire_ids_are_never_reallocated_even_after_measurement() {
    rejected(
        program(
            vec![],
            vec![],
            vec![
                RawOp::Init0 {
                    output: t(0),
                    wire: w(0),
                },
                RawOp::MeasureZ {
                    input: t(0),
                    output: c(0),
                },
                RawOp::Init0 {
                    output: t(1),
                    wire: w(0),
                },
            ],
            vec![t(1)],
            vec![c(0)],
            Effect::Observe,
        ),
        "not globally fresh",
    );
}

#[test]
fn branch_depth_limit_counts_empty_branches_in_both_arms() {
    // Small nested programs must work with and without a leaf in both arms.
    // Depth 65 must reject, even when no operation sits at the end. The QIRF
    // JSON depth bound may reject before the raw branch depth bound.
    for in_then_arm in [true, false] {
        for with_leaf in [false, true] {
            for levels in [8, 16, 65] {
                let mut nested = if with_leaf {
                    vec![RawOp::ClassicalNot {
                        input: c(0),
                        output: c(1),
                    }]
                } else {
                    vec![]
                };
                for _ in 0..levels {
                    let (then_ops, else_ops) = if in_then_arm {
                        (nested, vec![])
                    } else {
                        (vec![], nested)
                    };
                    nested = vec![RawOp::ClassicalBranch {
                        condition: c(0),
                        then_ops,
                        else_ops,
                        quantum_phis: vec![],
                        classical_phis: vec![],
                    }];
                }
                let result = accept(program(
                    vec![],
                    vec![c(0)],
                    nested,
                    vec![],
                    vec![],
                    Effect::Unitary,
                ));
                if levels <= 16 {
                    assert_eq!(result.unwrap().derived_effect(), Effect::Unitary);
                } else {
                    let error = result.expect_err("the 65th branch exceeds the IR profile");
                    assert!(
                        matches!(error.code, "limit" | "format" | "invalid_ir"),
                        "{error}"
                    );
                }
            }
        }
    }
}

#[test]
fn oversized_register_and_deeply_nested_branch_are_rejected() {
    rejected(
        program(
            vec![QuantumPort {
                token: t(0),
                wires: (0..13).map(w).collect(),
                shape: BasisShape { bits: 13 },
            }],
            vec![],
            vec![],
            vec![t(0)],
            vec![],
            Effect::Iso,
        ),
        "finite basis shape",
    );

    let mut nested = vec![];
    for _ in 0..1_000 {
        nested = vec![RawOp::ClassicalBranch {
            condition: c(0),
            then_ops: nested,
            else_ops: vec![],
            quantum_phis: vec![],
            classical_phis: vec![],
        }];
    }
    rejected(
        program(vec![], vec![c(0)], nested, vec![], vec![], Effect::Unitary),
        "depth limit",
    );
}

#[test]
fn coherent_qif_accepts_unitary_arms_and_unit_target_phase() {
    let checked = accept(program(
        vec![
            bit_port(0, 0),
            QuantumPort {
                token: t(1),
                wires: vec![],
                shape: BasisShape::UNIT,
            },
        ],
        vec![],
        vec![RawOp::QuantumIf {
            control: t(0),
            target: t(1),
            control_out: t(2),
            target_out: t(3),
            zero_ops: vec![],
            one_ops: vec![UnitaryStep::ScalarPhase(ScalarPhase::MinusOne)],
        }],
        vec![t(2), t(3)],
        vec![],
        Effect::Unitary,
    ))
    .unwrap();
    assert_eq!(checked.derived_effect(), Effect::Unitary);
}

#[test]
fn coherent_qif_rejects_aliasing_and_bad_target_indices() {
    rejected(
        program(
            vec![bit_port(0, 0)],
            vec![],
            vec![RawOp::QuantumIf {
                control: t(0),
                target: t(0),
                control_out: t(1),
                target_out: t(2),
                zero_ops: vec![],
                one_ops: vec![],
            }],
            vec![t(1), t(2)],
            vec![],
            Effect::Unitary,
        ),
        "used twice",
    );

    for (step, phrase) in [
        (
            UnitaryStep::Gate {
                gate: SingleGate::H,
                target_index: 1,
            },
            "out of range",
        ),
        (
            UnitaryStep::Cnot {
                control_index: 0,
                target_index: 0,
            },
            "uses one target bit twice",
        ),
        (
            UnitaryStep::Toffoli {
                control_a_index: 0,
                control_b_index: 0,
                target_index: 0,
            },
            "uses one target bit twice",
        ),
    ] {
        rejected(
            program(
                vec![bit_port(0, 0), bit_port(1, 1)],
                vec![],
                vec![RawOp::QuantumIf {
                    control: t(0),
                    target: t(1),
                    control_out: t(2),
                    target_out: t(3),
                    zero_ops: vec![step],
                    one_ops: vec![],
                }],
                vec![t(2), t(3)],
                vec![],
                Effect::Unitary,
            ),
            phrase,
        );
    }
}

#[test]
fn classical_constants_and_conjunction_require_fresh_visible_ssa_values() {
    let checked = accept(program(
        vec![],
        vec![c(0)],
        vec![
            RawOp::ClassicalConst {
                value: true,
                output: c(1),
            },
            RawOp::ClassicalAnd {
                left: c(0),
                right: c(1),
                output: c(2),
            },
        ],
        vec![],
        vec![c(2)],
        Effect::Unitary,
    ))
    .unwrap();
    assert_eq!(checked.derived_effect(), Effect::Unitary);
    for operations in [
        vec![RawOp::ClassicalConst {
            value: false,
            output: c(0),
        }],
        vec![RawOp::ClassicalAnd {
            left: c(0),
            right: c(0),
            output: c(0),
        }],
    ] {
        rejected(
            program(
                vec![],
                vec![c(0)],
                operations,
                vec![],
                vec![],
                Effect::Unitary,
            ),
            "not fresh",
        );
    }
    for (left, right) in [(c(1), c(0)), (c(0), c(1))] {
        rejected(
            program(
                vec![],
                vec![c(0)],
                vec![RawOp::ClassicalAnd {
                    left,
                    right,
                    output: c(2),
                }],
                vec![],
                vec![],
                Effect::Unitary,
            ),
            "not defined in this scope",
        );
    }
    rejected(
        program(
            vec![],
            vec![c(0)],
            vec![
                RawOp::ClassicalBranch {
                    condition: c(0),
                    then_ops: vec![RawOp::ClassicalConst {
                        value: true,
                        output: c(1),
                    }],
                    else_ops: vec![],
                    quantum_phis: vec![],
                    classical_phis: vec![],
                },
                RawOp::ClassicalAnd {
                    left: c(0),
                    right: c(1),
                    output: c(2),
                },
            ],
            vec![],
            vec![],
            Effect::Unitary,
        ),
        "not defined in this scope",
    );
}
