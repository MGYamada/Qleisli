//! Function evidence is checked against independent raw operators and layouts.

use std::sync::Arc;

use qleisli::contract::exact::{Budget, Exact, ExactError, Matrix};
use qleisli::contract::function::{MAX_FUNCTION_DEPTH, MAX_FUNCTION_SOURCE_BYTES};
use qleisli::contract::{
    BasisType, ContractError, DEFAULT_EXACT_WORK, FunctionEvidence, FunctionIdentity,
};
use qleisli::ir::*;

fn work() -> Budget {
    Budget::new(DEFAULT_EXACT_WORK)
}
fn t(id: u32) -> TokenId {
    TokenId(id)
}
fn c(id: u32) -> ClassicalId {
    ClassicalId(id)
}
fn w(id: u32) -> WireId {
    WireId(id)
}

fn basis(bits: u8) -> BasisType {
    if bits == 0 {
        return BasisType::Unit;
    }
    (1..bits).fold(BasisType::Bit, |left, _| {
        BasisType::pair(left, BasisType::Bit)
    })
}

fn raw(bits: u8, operations: Vec<RawOp>, output: u32) -> RawProgram {
    RawProgram {
        quantum_inputs: vec![QuantumPort {
            token: t(0),
            wires: (0..u32::from(bits)).map(w).collect(),
            shape: BasisShape { bits },
        }],
        classical_inputs: vec![],
        operations,
        quantum_outputs: vec![t(output)],
        classical_outputs: vec![],
        declared_effect: Effect::Unitary,
    }
}

fn identity() -> FunctionIdentity {
    FunctionIdentity {
        implementation: "impl::operation".into(),
        specification: "spec::operation".into(),
        sources: vec![("module".into(), "exact source bytes".into())],
    }
}

fn monomial(indices: &[usize], permutation: &[u16], phases: &[u8]) -> CircuitStep {
    CircuitStep {
        controls: vec![],
        action: CircuitAction::Monomial {
            indices: indices.to_vec(),
            permutation: permutation.to_vec(),
            phases: phases.to_vec(),
        },
    }
}

fn gate(gate: SingleGate, input: u32, output: u32) -> RawOp {
    RawOp::Gate {
        gate,
        input: t(input),
        output: t(output),
    }
}

fn flat(bits: u8, steps: Vec<CircuitStep>) -> RawProgram {
    raw(
        bits,
        vec![RawOp::ApplyUnitary {
            input: t(0),
            output: t(1),
            steps,
        }],
        1,
    )
}

fn check(bits: u8, implementation: RawProgram, specification: RawProgram) -> FunctionEvidence {
    FunctionEvidence::check(
        basis(bits),
        implementation,
        specification,
        identity(),
        &mut work(),
    )
    .unwrap()
}

fn matrix(dim: usize, entry: impl Fn(usize, usize) -> Exact) -> Matrix {
    let mut entries = vec![];
    for row in 0..dim {
        for col in 0..dim {
            entries.push(entry(row, col));
        }
    }
    Matrix::new(dim, dim, entries).unwrap()
}

fn diagonal(phases: &[i32]) -> Matrix {
    matrix(phases.len(), |row, col| {
        if row == col {
            Exact::phase(phases[col])
        } else {
            Exact::zero()
        }
    })
}

fn call(evidence: Arc<FunctionEvidence>, indices: Vec<usize>, adjoint: bool) -> CircuitStep {
    CircuitStep {
        controls: vec![],
        action: CircuitAction::Contract {
            indices,
            evidence,
            adjoint,
        },
    }
}

#[test]
fn checks_two_raw_functions_and_retains_their_full_snapshots() {
    let implementation = raw(
        1,
        vec![gate(SingleGate::H, 0, 1), gate(SingleGate::H, 1, 2)],
        2,
    );
    let specification = raw(1, vec![], 0);
    let theorem = check(1, implementation.clone(), specification.clone());
    assert_eq!(theorem.meaning(), &Matrix::identity(2).unwrap());
    assert_eq!(theorem.implementation(), &implementation);
    assert_eq!(theorem.specification(), &specification);
    assert_eq!(theorem.depth(), 1);
    assert_eq!(theorem.expanded_steps(), 2);
    theorem
        .check_binding(
            &BasisType::Bit,
            &identity(),
            &implementation,
            &specification,
        )
        .unwrap();
    let mut renamed = identity();
    renamed.implementation.push_str("_changed");
    assert_eq!(
        theorem.check_binding(&BasisType::Bit, &renamed, &implementation, &specification),
        Err(ContractError::EvidenceMismatch)
    );
    let mut edited = identity();
    edited.sources[0].1.push(' ');
    assert_eq!(
        theorem.check_binding(&BasisType::Bit, &edited, &implementation, &specification),
        Err(ContractError::EvidenceMismatch)
    );
    assert_eq!(
        theorem.check_binding(&BasisType::Bit, &identity(), &specification, &specification),
        Err(ContractError::EvidenceMismatch)
    );
    assert_eq!(
        theorem.check_binding(
            &BasisType::Bit,
            &identity(),
            &implementation,
            &implementation
        ),
        Err(ContractError::EvidenceMismatch)
    );
}

#[test]
fn attachment_requires_the_exact_expected_basis_tree() {
    let cases = [
        (
            BasisType::Tuple(vec![BasisType::Bit; 3]),
            BasisType::pair(
                BasisType::Bit,
                BasisType::pair(BasisType::Bit, BasisType::Bit),
            ),
        ),
        (
            BasisType::Unit,
            BasisType::pair(BasisType::Unit, BasisType::Unit),
        ),
        (
            BasisType::Bit,
            BasisType::pair(BasisType::Unit, BasisType::Bit),
        ),
    ];
    for (retained, substituted) in cases {
        let bits = retained.bits().unwrap();
        assert_eq!(bits, substituted.bits().unwrap());
        assert_ne!(retained, substituted);
        let program = raw(bits as u8, vec![], 0);
        let receipt = FunctionEvidence::check(
            retained.clone(),
            program.clone(),
            program.clone(),
            identity(),
            &mut work(),
        )
        .unwrap();
        assert_eq!(
            receipt.check_binding(&retained, &identity(), &program, &program),
            Ok(())
        );
        assert_eq!(
            receipt.check_binding(&substituted, &identity(), &program, &program),
            Err(ContractError::EvidenceMismatch)
        );
    }
}

#[test]
fn whole_function_comparison_retains_global_phase_including_unit() {
    let negative = flat(0, vec![monomial(&[], &[0], &[4])]);
    let theorem = check(0, negative.clone(), negative.clone());
    assert_eq!(theorem.meaning(), &diagonal(&[4]));
    assert_eq!(
        FunctionEvidence::check(
            BasisType::Unit,
            negative,
            raw(0, vec![], 0),
            identity(),
            &mut work()
        )
        .unwrap_err(),
        ContractError::EquationMismatch
    );
}

#[test]
fn independent_output_reindexing_catches_a_reversed_join() {
    let swapped = raw(
        2,
        vec![
            RawOp::Split {
                input: t(0),
                left: t(1),
                right: t(2),
                left_bits: 1,
            },
            RawOp::Join {
                left: t(2),
                right: t(1),
                output: t(3),
            },
        ],
        3,
    );
    let specification = flat(2, vec![monomial(&[0, 1], &[0, 2, 1, 3], &[0; 4])]);
    let theorem = check(2, swapped.clone(), specification);
    assert_eq!(
        theorem.meaning(),
        &matrix(4, |row, col| {
            Exact::integer(i128::from(row == (((col & 1) << 1) | (col >> 1))))
        })
    );
    assert_eq!(
        FunctionEvidence::check(
            basis(2),
            swapped,
            raw(2, vec![], 0),
            identity(),
            &mut work()
        )
        .unwrap_err(),
        ContractError::EquationMismatch
    );
}

#[test]
fn independent_extraction_handles_lifts_cnot_and_toffoli() {
    let lifted = raw(
        1,
        vec![RawOp::LiftBasis {
            input: t(0),
            output: t(1),
            output_wires: vec![w(0)],
            table: vec![1, 0],
        }],
        1,
    );
    let theorem = check(1, lifted, raw(1, vec![gate(SingleGate::X, 0, 1)], 1));
    assert_eq!(
        theorem.meaning(),
        &matrix(2, |row, col| Exact::integer(i128::from(row != col)))
    );
    let composed = raw(
        3,
        vec![
            RawOp::Split {
                input: t(0),
                left: t(1),
                right: t(2),
                left_bits: 2,
            },
            RawOp::Split {
                input: t(1),
                left: t(3),
                right: t(4),
                left_bits: 1,
            },
            RawOp::Cnot {
                control: t(3),
                target: t(4),
                control_out: t(5),
                target_out: t(6),
            },
            RawOp::Toffoli {
                control_a: t(5),
                control_b: t(6),
                target: t(2),
                control_a_out: t(7),
                control_b_out: t(8),
                target_out: t(9),
            },
            RawOp::Join {
                left: t(7),
                right: t(8),
                output: t(10),
            },
            RawOp::Join {
                left: t(10),
                right: t(9),
                output: t(11),
            },
        ],
        11,
    );
    let permutation: Vec<u16> = (0..8)
        .map(|input| {
            let a = input & 1;
            let b = ((input >> 1) & 1) ^ a;
            let c = ((input >> 2) & 1) ^ (a & b);
            a | (b << 1) | (c << 2)
        })
        .collect();
    let theorem = check(
        3,
        composed,
        flat(3, vec![monomial(&[0, 1, 2], &permutation, &[0; 8])]),
    );
    assert_eq!(
        theorem.meaning(),
        &matrix(8, |row, col| Exact::integer(i128::from(
            row == usize::from(permutation[col])
        )))
    );
}

#[test]
fn quantum_if_extracts_both_coherent_arms_with_relative_phase() {
    let implementation = raw(
        2,
        vec![
            RawOp::Split {
                input: t(0),
                left: t(1),
                right: t(2),
                left_bits: 1,
            },
            RawOp::QuantumIf {
                control: t(1),
                target: t(2),
                control_out: t(3),
                target_out: t(4),
                zero_ops: vec![UnitaryStep::Gate {
                    gate: SingleGate::T,
                    target_index: 0,
                }],
                one_ops: vec![UnitaryStep::Gate {
                    gate: SingleGate::H,
                    target_index: 0,
                }],
            },
            RawOp::Join {
                left: t(3),
                right: t(4),
                output: t(5),
            },
        ],
        5,
    );
    let mut zero = monomial(&[1], &[0, 1], &[0, 1]);
    zero.controls.push(BitControl {
        index: 0,
        when_one: false,
    });
    let one = CircuitStep {
        controls: vec![BitControl {
            index: 0,
            when_one: true,
        }],
        action: CircuitAction::Hadamard { target: 1 },
    };
    let theorem = check(2, implementation, flat(2, vec![zero, one]));
    let expected = matrix(4, |row, col| {
        if row & 1 != col & 1 {
            Exact::zero()
        } else if col & 1 == 0 {
            if row == col {
                Exact::phase((col >> 1) as i32)
            } else {
                Exact::zero()
            }
        } else if row & 2 != 0 && col & 2 != 0 {
            Exact::inv_sqrt2().neg().unwrap()
        } else {
            Exact::inv_sqrt2()
        }
    });
    assert_eq!(theorem.meaning(), &expected);
}

#[test]
fn zero_width_quantum_if_target_keeps_controlled_scalar_phase() {
    let implementation = raw(
        1,
        vec![
            RawOp::Split {
                input: t(0),
                left: t(1),
                right: t(2),
                left_bits: 1,
            },
            RawOp::QuantumIf {
                control: t(1),
                target: t(2),
                control_out: t(3),
                target_out: t(4),
                zero_ops: vec![],
                one_ops: vec![UnitaryStep::ScalarPhase(ScalarPhase::MinusOne)],
            },
            RawOp::Join {
                left: t(3),
                right: t(4),
                output: t(5),
            },
        ],
        5,
    );
    let signature = BasisType::pair(BasisType::Bit, BasisType::Unit);
    let theorem = FunctionEvidence::check(
        signature.clone(),
        implementation,
        raw(1, vec![gate(SingleGate::Z, 0, 1)], 1),
        identity(),
        &mut work(),
    )
    .unwrap();
    assert_eq!(theorem.signature(), &signature);
    assert_eq!(theorem.meaning(), &diagonal(&[0, 4]));
}

#[test]
fn closed_classical_logic_and_both_kinds_of_phi_preserve_meaning() {
    let implementation = raw(
        1,
        vec![
            RawOp::ClassicalConst {
                value: false,
                output: c(0),
            },
            RawOp::ClassicalNot {
                input: c(0),
                output: c(1),
            },
            RawOp::ClassicalXor {
                left: c(0),
                right: c(1),
                output: c(2),
            },
            RawOp::ClassicalAnd {
                left: c(1),
                right: c(2),
                output: c(3),
            },
            RawOp::ClassicalBranch {
                condition: c(3),
                then_ops: vec![
                    gate(SingleGate::X, 0, 1),
                    RawOp::ClassicalConst {
                        value: false,
                        output: c(4),
                    },
                ],
                else_ops: vec![
                    gate(SingleGate::Z, 0, 2),
                    RawOp::ClassicalConst {
                        value: true,
                        output: c(5),
                    },
                ],
                quantum_phis: vec![QuantumPhi {
                    then_token: t(1),
                    else_token: t(2),
                    output: t(3),
                    output_wires: vec![w(1)],
                }],
                classical_phis: vec![ClassicalPhi {
                    then_id: c(4),
                    else_id: c(5),
                    output: c(6),
                }],
            },
            RawOp::ClassicalBranch {
                condition: c(6),
                then_ops: vec![gate(SingleGate::H, 3, 4)],
                else_ops: vec![gate(SingleGate::T, 3, 5)],
                quantum_phis: vec![QuantumPhi {
                    then_token: t(4),
                    else_token: t(5),
                    output: t(6),
                    output_wires: vec![w(2)],
                }],
                classical_phis: vec![],
            },
        ],
        6,
    );
    let specification = raw(
        1,
        vec![gate(SingleGate::X, 0, 1), gate(SingleGate::T, 1, 2)],
        2,
    );
    let theorem = check(1, implementation, specification);
    assert_eq!(
        theorem.meaning(),
        &matrix(2, |row, col| if row != col {
            Exact::phase(row as i32)
        } else {
            Exact::zero()
        })
    );
}

#[test]
fn a_statically_unselected_invalid_arm_is_still_rejected() {
    let implementation = raw(
        1,
        vec![
            RawOp::ClassicalConst {
                value: true,
                output: c(0),
            },
            RawOp::ClassicalBranch {
                condition: c(0),
                then_ops: vec![gate(SingleGate::X, 0, 1)],
                else_ops: vec![gate(SingleGate::X, 99, 2)],
                quantum_phis: vec![QuantumPhi {
                    then_token: t(1),
                    else_token: t(2),
                    output: t(3),
                    output_wires: vec![w(1)],
                }],
                classical_phis: vec![],
            },
        ],
        3,
    );
    assert!(matches!(
        FunctionEvidence::check(
            basis(1),
            implementation,
            raw(1, vec![gate(SingleGate::X, 0, 1)], 1),
            identity(),
            &mut work()
        ),
        Err(ContractError::InvalidCircuit(_))
    ));
}

fn computed(source_bits: u8, function: Vec<u16>, use_ops: Vec<ProtectedUse>) -> RawProgram {
    raw(
        source_bits,
        vec![RawOp::ComputeUseUncompute {
            source: t(0),
            source_out: t(1),
            targets: vec![],
            ancilla_wires: vec![w(u32::from(source_bits))],
            function,
            use_ops,
        }],
        1,
    )
}

#[test]
fn legacy_computed_phase_is_checked_against_asymmetric_direct_oracle() {
    let implementation = computed(
        2,
        vec![0, 1, 0, 0],
        vec![ProtectedUse::ProtectedGate {
            bit: ProtectedBit {
                region: ProtectedRegion::Ancilla,
                index: 0,
            },
            gate: SingleGate::Z,
        }],
    );
    let specification = flat(2, vec![monomial(&[0, 1], &[0, 1, 2, 3], &[0, 4, 0, 0])]);
    let theorem = check(2, implementation, specification);
    assert_eq!(theorem.meaning(), &diagonal(&[0, 4, 0, 0]));
}

#[test]
fn legacy_computed_target_gates_can_depend_on_source_and_auxiliary() {
    let a = ProtectedBit {
        region: ProtectedRegion::Source,
        index: 0,
    };
    let f = ProtectedBit {
        region: ProtectedRegion::Ancilla,
        index: 0,
    };
    let implementation = raw(
        2,
        vec![
            RawOp::Split {
                input: t(0),
                left: t(1),
                right: t(2),
                left_bits: 1,
            },
            RawOp::ComputeUseUncompute {
                source: t(1),
                source_out: t(3),
                targets: vec![TargetTransition {
                    input: t(2),
                    output: t(4),
                }],
                ancilla_wires: vec![w(2)],
                function: vec![1, 0],
                use_ops: vec![
                    ProtectedUse::ControlledTargetGate {
                        controls: vec![
                            Control {
                                bit: a,
                                when_one: false,
                            },
                            Control {
                                bit: f,
                                when_one: true,
                            },
                        ],
                        target_index: 0,
                        gate: SingleGate::H,
                    },
                    ProtectedUse::ControlledPhase {
                        controls: vec![Control {
                            bit: f,
                            when_one: true,
                        }],
                        phase: ScalarPhase::EighthTurn,
                    },
                ],
            },
            RawOp::Join {
                left: t(3),
                right: t(4),
                output: t(5),
            },
        ],
        5,
    );
    let h = CircuitStep {
        controls: vec![BitControl {
            index: 0,
            when_one: false,
        }],
        action: CircuitAction::Hadamard { target: 1 },
    };
    let scalar = monomial(&[0], &[0, 1], &[1, 0]);
    let theorem = check(2, implementation, flat(2, vec![h, scalar]));
    assert_eq!(
        theorem.meaning(),
        &matrix(4, |row, col| {
            if row & 1 != col & 1 {
                Exact::zero()
            } else if col & 1 != 0 {
                Exact::integer(i128::from(row == col))
            } else {
                let amplitude = Exact::inv_sqrt2().mul(Exact::phase(1)).unwrap();
                if row & 2 != 0 && col & 2 != 0 {
                    amplitude.neg().unwrap()
                } else {
                    amplitude
                }
            }
        })
    );
}

#[test]
fn certified_computation_reuses_only_its_rechecked_logical_meaning() {
    let x = |index| monomial(&[index], &[1, 0], &[0, 0]);
    let implementation = raw(
        1,
        vec![RawOp::CertifiedCompute {
            source: t(0),
            source_out: t(1),
            ancilla_wires: vec![w(1)],
            function: vec![0, 1],
            use_steps: vec![x(0), x(1)],
            logical_steps: vec![x(0)],
        }],
        1,
    );
    let theorem = check(
        1,
        implementation.clone(),
        raw(1, vec![gate(SingleGate::X, 0, 1)], 1),
    );
    assert_eq!(
        theorem.meaning(),
        &matrix(2, |row, col| Exact::integer(i128::from(row != col)))
    );
    let mut bad = implementation;
    if let RawOp::CertifiedCompute { use_steps, .. } = &mut bad.operations[0] {
        use_steps.remove(0);
    }
    assert!(matches!(
        FunctionEvidence::check(
            basis(1),
            bad,
            raw(1, vec![gate(SingleGate::X, 0, 1)], 1),
            identity(),
            &mut work()
        ),
        Err(ContractError::EquationMismatch)
    ));
}

#[test]
fn cached_calls_keep_opaque_dependencies_and_phase_under_control_and_adjoint() {
    let child = Arc::new(check(
        1,
        raw(1, vec![gate(SingleGate::T, 0, 1)], 1),
        flat(1, vec![monomial(&[0], &[0, 1], &[0, 1])]),
    ));
    let mut controlled = call(child.clone(), vec![1], true);
    controlled.controls.push(BitControl {
        index: 0,
        when_one: true,
    });
    let parent = check(
        2,
        flat(2, vec![controlled]),
        flat(2, vec![monomial(&[0, 1], &[0, 1, 2, 3], &[0, 0, 0, 7])]),
    );
    assert_eq!(parent.meaning(), &diagonal(&[0, 0, 0, -1]));
    assert_eq!(parent.depth(), 2);
    assert_eq!(parent.expanded_steps(), 1);
    let CircuitAction::Contract {
        evidence,
        indices,
        adjoint,
    } = &parent.circuit().steps()[0].action
    else {
        panic!("dependency was expanded")
    };
    assert!(!Arc::ptr_eq(evidence, &child)); // Fresh native decoding owns its receipt.
    assert_eq!(evidence.identity(), child.identity());
    assert_eq!(evidence.meaning(), child.meaning());
    child
        .check_binding(
            evidence.signature(),
            evidence.identity(),
            evidence.implementation(),
            evidence.specification(),
        )
        .unwrap();
    assert_eq!(indices, &[1]);
    assert!(*adjoint);
}

#[test]
fn cached_dependency_equality_is_identity_based_and_clone_stable() {
    let leaf = check(0, raw(0, vec![], 0), raw(0, vec![], 0));
    assert_eq!(leaf, leaf.clone());
    let separate = check(0, raw(0, vec![], 0), raw(0, vec![], 0));
    assert_ne!(leaf, separate);
    let implementation = flat(0, vec![call(Arc::new(leaf), vec![], false)]);
    let parent = check(0, implementation, raw(0, vec![], 0));
    let replaced = flat(0, vec![call(Arc::new(separate), vec![], false)]);
    assert_eq!(
        parent.check_binding(
            &BasisType::Unit,
            parent.identity(),
            &replaced,
            parent.specification()
        ),
        Ok(()) // Equal complete native snapshots can have distinct host Arc identities.
    );
}

#[test]
fn cached_contract_axes_follow_register_layout_and_final_output_order() {
    let leaf_raw = flat(2, vec![monomial(&[0, 1], &[0, 1, 2, 3], &[0, 4, 0, 0])]);
    let child = Arc::new(check(2, leaf_raw.clone(), leaf_raw));
    let implementation = raw(
        2,
        vec![
            RawOp::Split {
                input: t(0),
                left: t(1),
                right: t(2),
                left_bits: 1,
            },
            RawOp::Join {
                left: t(2),
                right: t(1),
                output: t(3),
            },
            RawOp::ApplyUnitary {
                input: t(3),
                output: t(4),
                steps: vec![call(child, vec![0, 1], false)],
            },
        ],
        4,
    );
    let specification = flat(2, vec![monomial(&[0, 1], &[0, 2, 1, 3], &[0, 0, 4, 0])]);
    let theorem = check(2, implementation, specification);
    assert_eq!(
        theorem.meaning(),
        &matrix(4, |row, col| {
            let swapped = ((col & 1) << 1) | (col >> 1);
            if row != swapped {
                Exact::zero()
            } else {
                Exact::phase(if col == 2 { 4 } else { 0 })
            }
        })
    );
    let CircuitAction::Contract { indices, .. } = &theorem.circuit().steps()[0].action else {
        panic!("dependency was expanded")
    };
    assert_eq!(indices, &[1, 0]);
}

#[test]
fn independent_raw_checks_share_work_across_certified_compute_regions() {
    let region = |input, output, wire| RawOp::CertifiedCompute {
        source: t(input),
        source_out: t(output),
        ancilla_wires: vec![w(wire)],
        function: vec![0],
        use_steps: vec![
            CircuitStep {
                controls: vec![],
                action: CircuitAction::Hadamard { target: 0 }
            };
            2
        ],
        logical_steps: vec![],
    };
    let one = raw(0, vec![region(0, 1, 0)], 1);
    let two = raw(0, vec![region(0, 1, 0), region(1, 2, 1)], 2);
    let mut measured = work();
    FunctionEvidence::check(
        BasisType::Unit,
        one.clone(),
        raw(0, vec![], 0),
        identity(),
        &mut measured,
    )
    .unwrap();
    let one_cost = DEFAULT_EXACT_WORK - measured.remaining();
    FunctionEvidence::check(
        BasisType::Unit,
        one,
        raw(0, vec![], 0),
        identity(),
        &mut Budget::new(one_cost),
    )
    .unwrap();
    let error = FunctionEvidence::check(
        BasisType::Unit,
        two,
        raw(0, vec![], 0),
        identity(),
        &mut Budget::new(one_cost),
    )
    .unwrap_err();
    assert!(
        matches!(
            error,
            ContractError::Limit(_) | ContractError::Arithmetic(ExactError::WorkLimit)
        ),
        "{error}"
    );
}

#[test]
fn untrusted_function_trees_reject_without_recursive_cloning() {
    const CHILD: &str = "QLEISLI_TEST_UNTRUSTED_FUNCTION_TREE";
    if let Ok(case) = std::env::var(CHILD) {
        std::thread::Builder::new()
            .stack_size(2 * 1024 * 1024)
            .spawn(move || {
                let mut signature = BasisType::Unit;
                let mut implementation = raw(0, vec![], 0);
                let mut specification = raw(0, vec![], 0);
                match case.as_str() {
                    "implementation" | "specification" => {
                        let mut operations = vec![];
                        for _ in 0..1000 {
                            operations = vec![RawOp::ClassicalBranch {
                                condition: c(0),
                                then_ops: operations,
                                else_ops: vec![],
                                quantum_phis: vec![],
                                classical_phis: vec![],
                            }];
                        }
                        if case == "implementation" {
                            implementation.operations = operations;
                        } else {
                            specification.operations = operations;
                        }
                    }
                    "signature" => {
                        for _ in 0..10_000 {
                            signature = BasisType::pair(BasisType::Unit, signature);
                        }
                    }
                    _ => panic!("unknown regression case"),
                }
                // Zero qubits and no execution: malformed trees must hit a
                // transport/type limit before any recursive clone or encoding.
                assert!(matches!(
                    FunctionEvidence::check(
                        signature,
                        implementation,
                        specification,
                        identity(),
                        &mut work(),
                    ),
                    Err(ContractError::Limit(_))
                ));
            })
            .unwrap()
            .join()
            .unwrap();
        return;
    }
    // A stack overflow aborts the process, so isolate each public-API call
    // rather than allowing a regression to terminate unrelated tests.
    for case in ["implementation", "specification", "signature"] {
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "untrusted_function_trees_reject_without_recursive_cloning",
                "--nocapture",
            ])
            .env(CHILD, case)
            .output()
            .unwrap();
        assert!(output.status.success(), "{case}: {output:?}");
    }
}

#[test]
fn branch_preflight_checks_both_functions_and_inactive_empty_arms() {
    for in_then_arm in [true, false] {
        for levels in [31, 32, 33] {
            for in_implementation in [true, false] {
                let mut operations = vec![];
                let mut output = t(0);
                for level in 1..=levels {
                    let (then_ops, else_ops, then_token, else_token) = if in_then_arm {
                        (operations, vec![], output, t(0))
                    } else {
                        (vec![], operations, t(0), output)
                    };
                    output = t(level);
                    operations = vec![RawOp::ClassicalBranch {
                        condition: c(0),
                        then_ops,
                        else_ops,
                        quantum_phis: vec![QuantumPhi {
                            then_token,
                            else_token,
                            output,
                            output_wires: vec![],
                        }],
                        classical_phis: vec![],
                    }];
                }
                // Extraction selects the shallow arm. Preflight must still
                // inspect the inactive nested arm before cloning raw IR.
                operations.insert(
                    0,
                    RawOp::ClassicalConst {
                        output: c(0),
                        value: !in_then_arm,
                    },
                );
                let nested = raw(0, operations, output.0);
                let empty = raw(0, vec![], 0);
                let (implementation, specification) = if in_implementation {
                    (nested, empty)
                } else {
                    (empty, nested)
                };
                let result = FunctionEvidence::check(
                    BasisType::Unit,
                    implementation,
                    specification,
                    identity(),
                    &mut work(),
                );
                if levels <= 32 {
                    assert_eq!(result.unwrap().meaning(), &Matrix::identity(1).unwrap());
                } else {
                    assert!(matches!(result, Err(ContractError::Limit(_))));
                }
            }
        }
    }
}

#[test]
#[ignore = "historical Rust maximum-depth/expansion stress; native transport bounds apply and maximum runs are deferred"]
fn dependency_depth_and_expanded_execution_cost_are_bounded() {
    let mut child = Arc::new(check(0, raw(0, vec![], 0), raw(0, vec![], 0)));
    for expected_depth in 2..=MAX_FUNCTION_DEPTH {
        child = Arc::new(check(
            0,
            flat(0, vec![call(child, vec![], false)]),
            raw(0, vec![], 0),
        ));
        assert_eq!(child.depth(), expected_depth);
    }
    assert!(matches!(
        FunctionEvidence::check(
            BasisType::Unit,
            flat(0, vec![call(child, vec![], false)]),
            raw(0, vec![], 0),
            identity(),
            &mut work()
        ),
        Err(ContractError::Limit(_))
    ));
    let mut child = Arc::new(check(0, raw(0, vec![], 0), raw(0, vec![], 0)));
    for exponent in 1..20 {
        child = Arc::new(check(
            0,
            flat(
                0,
                vec![
                    call(child.clone(), vec![], false),
                    call(child, vec![], false),
                ],
            ),
            raw(0, vec![], 0),
        ));
        assert_eq!(child.expanded_steps(), 1 << exponent);
    }
    assert!(matches!(
        FunctionEvidence::check(
            BasisType::Unit,
            flat(
                0,
                vec![
                    call(child.clone(), vec![], false),
                    call(child, vec![], false)
                ]
            ),
            raw(0, vec![], 0),
            identity(),
            &mut work()
        ),
        Err(ContractError::Limit(_))
    ));
}

#[test]
fn rejects_invalid_signatures_observation_and_zero_width_owner_loss() {
    let specification = raw(0, vec![], 0);
    let mut missing = specification.clone();
    missing.quantum_outputs.clear();
    assert!(
        FunctionEvidence::check(
            BasisType::Unit,
            missing,
            specification.clone(),
            identity(),
            &mut work()
        )
        .is_err()
    );
    let mut duplicate = specification.clone();
    duplicate.operations.push(RawOp::Join {
        left: t(0),
        right: t(0),
        output: t(1),
    });
    duplicate.quantum_outputs = vec![t(1)];
    assert!(matches!(
        FunctionEvidence::check(
            BasisType::Unit,
            duplicate,
            specification,
            identity(),
            &mut work()
        ),
        Err(ContractError::InvalidCircuit(_))
    ));
    let observe = raw(1, vec![RawOp::Discard { input: t(0) }], 0);
    assert!(
        FunctionEvidence::check(
            basis(1),
            observe,
            raw(1, vec![], 0),
            identity(),
            &mut work()
        )
        .is_err()
    );
    assert!(
        FunctionEvidence::check(
            BasisType::Unit,
            raw(1, vec![], 0),
            raw(1, vec![], 0),
            identity(),
            &mut work()
        )
        .is_err()
    );
    let mut classical = raw(1, vec![], 0);
    classical.classical_inputs.push(c(0));
    assert!(
        FunctionEvidence::check(
            basis(1),
            classical,
            raw(1, vec![], 0),
            identity(),
            &mut work()
        )
        .is_err()
    );
}

#[test]
fn rejects_untrusted_capacity_and_exhausted_shared_work() {
    let mut excessive = identity();
    excessive.sources[0].1 = "x".repeat(MAX_FUNCTION_SOURCE_BYTES);
    assert!(matches!(
        FunctionEvidence::check(
            BasisType::Unit,
            raw(0, vec![], 0),
            raw(0, vec![], 0),
            excessive,
            &mut work()
        ),
        Err(ContractError::Limit(_))
    ));
    let mut duplicate = identity();
    duplicate.sources.push(duplicate.sources[0].clone());
    assert!(matches!(
        FunctionEvidence::check(
            BasisType::Unit,
            raw(0, vec![], 0),
            raw(0, vec![], 0),
            duplicate,
            &mut work()
        ),
        Err(ContractError::Type(_))
    ));
    assert_eq!(
        FunctionEvidence::check(
            BasisType::Unit,
            raw(0, vec![], 0),
            raw(0, vec![], 0),
            identity(),
            &mut Budget::new(0)
        )
        .unwrap_err(),
        ContractError::Arithmetic(ExactError::WorkLimit)
    );
    let excessive = flat(0, vec![monomial(&[], &[0], &[0]); 1025]);
    assert!(matches!(
        FunctionEvidence::check(
            BasisType::Unit,
            excessive,
            raw(0, vec![], 0),
            identity(),
            &mut work()
        ),
        Err(ContractError::Limit(_))
    ));
}
