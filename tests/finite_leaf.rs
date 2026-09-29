mod common;

use std::process::Command;
use std::sync::Arc;

use qleisli::contract::exact::{Budget, Exact, Matrix};
use qleisli::contract::{BasisType, DEFAULT_EXACT_WORK, FunctionEvidence, FunctionIdentity};
use qleisli::interchange::finite_leaf::{UnitaryBoundary, check_serialized_unitary, check_unitary};
use qleisli::interchange::finite_matrix;
use qleisli::interchange::{self, RootInterface, Version};
use qleisli::ir::*;
use qleisli::verify;

fn port(token: u32, wires: &[u32]) -> QuantumPort {
    QuantumPort {
        token: TokenId(token),
        wires: wires.iter().copied().map(WireId).collect(),
        shape: BasisShape {
            bits: wires.len() as u8,
        },
    }
}

fn raw(input: QuantumPort, operations: Vec<RawOp>, output: u32) -> RawProgram {
    RawProgram {
        quantum_inputs: vec![input],
        classical_inputs: vec![],
        operations,
        quantum_outputs: vec![TokenId(output)],
        classical_outputs: vec![],
        declared_effect: Effect::Unitary,
    }
}

fn packet(raw: RawProgram, ty: BasisType, version: Version) -> Vec<u8> {
    interchange::export(
        &verify(raw).unwrap(),
        Some(&RootInterface {
            input: ty.clone(),
            output: ty,
        }),
        version,
    )
    .unwrap()
}

fn gate(gate: SingleGate) -> RawProgram {
    raw(
        port(0, &[7]),
        vec![RawOp::Gate {
            gate,
            input: TokenId(0),
            output: TokenId(1),
        }],
        1,
    )
}

fn hadamard() -> Matrix {
    let h = Exact::inv_sqrt2();
    Matrix::new(2, 2, vec![h, h, h, h.neg().unwrap()]).unwrap()
}

fn boundary() -> UnitaryBoundary {
    UnitaryBoundary::new(BasisType::Bit, port(0, &[7]), port(1, &[7])).unwrap()
}

fn permutation(table: &[usize]) -> Matrix {
    let n = table.len();
    let mut entries = vec![Exact::zero(); n * n];
    for (x, y) in table.iter().enumerate() {
        entries[y * n + x] = Exact::one();
    }
    Matrix::new(n, n, entries).unwrap()
}

#[test]
fn reconstruct_hadamard_in_both_formats_and_bind_complete_bytes() {
    for version in [Version::V1, Version::V2] {
        let mut bytes = packet(gate(SingleGate::H), BasisType::Bit, version);
        let b = boundary();
        let target = hadamard();
        let mut budget = Budget::new(DEFAULT_EXACT_WORK);
        let checked = check_unitary(&bytes, &b, &target, &mut budget).unwrap();
        assert_eq!(
            checked.exact_work(),
            DEFAULT_EXACT_WORK - budget.remaining()
        );
        assert!(checked.matches(&bytes.clone(), &b, &target));
        assert_eq!(checked.program().raw(), &gate(SingleGate::H));
        assert_eq!(checked.boundary().signature(), &BasisType::Bit);
        assert_eq!(checked.meaning(), &target);
        bytes.push(b' '); // Same parsed program, different immutable artifact binding.
        assert!(!checked.matches(&bytes, &b, &target));
        let again = check_unitary(&bytes, &b, &target, &mut budget).unwrap();
        assert_ne!(again.payload(), checked.payload());
        assert_eq!(again.meaning(), checked.meaning());
    }
}

#[test]
fn independently_specified_cnot_and_final_axis_order() {
    let ty = BasisType::pair(BasisType::Bit, BasisType::Bit);
    let ops = vec![
        RawOp::Split {
            input: TokenId(0),
            left: TokenId(1),
            right: TokenId(2),
            left_bits: 1,
        },
        RawOp::Cnot {
            control: TokenId(1),
            target: TokenId(2),
            control_out: TokenId(3),
            target_out: TokenId(4),
        },
        RawOp::Join {
            left: TokenId(3),
            right: TokenId(4),
            output: TokenId(5),
        },
    ];
    let bytes = packet(raw(port(0, &[7, 19]), ops, 5), ty.clone(), Version::V2);
    let b = UnitaryBoundary::new(ty.clone(), port(0, &[7, 19]), port(5, &[7, 19])).unwrap();
    let target = permutation(&[0, 3, 2, 1]); // First field is the low control bit.
    check_unitary(&bytes, &b, &target, &mut Budget::new(DEFAULT_EXACT_WORK)).unwrap();
    assert_eq!(
        check_unitary(
            &bytes,
            &b,
            &permutation(&[0, 1, 3, 2]),
            &mut Budget::new(DEFAULT_EXACT_WORK)
        )
        .unwrap_err()
        .code,
        "contract"
    );

    let swapped = packet(
        raw(
            port(0, &[7, 19]),
            vec![
                RawOp::Split {
                    input: TokenId(0),
                    left: TokenId(1),
                    right: TokenId(2),
                    left_bits: 1,
                },
                RawOp::Join {
                    left: TokenId(2),
                    right: TokenId(1),
                    output: TokenId(3),
                },
            ],
            3,
        ),
        ty.clone(),
        Version::V2,
    );
    let correct = UnitaryBoundary::new(ty.clone(), port(0, &[7, 19]), port(3, &[19, 7])).unwrap();
    let wrong = UnitaryBoundary::new(ty, port(0, &[7, 19]), port(3, &[7, 19])).unwrap();
    let swap = permutation(&[0, 2, 1, 3]);
    check_unitary(
        &swapped,
        &correct,
        &swap,
        &mut Budget::new(DEFAULT_EXACT_WORK),
    )
    .unwrap();
    assert_eq!(
        check_unitary(
            &swapped,
            &wrong,
            &swap,
            &mut Budget::new(DEFAULT_EXACT_WORK)
        )
        .unwrap_err()
        .code,
        "contract"
    );
}

#[test]
fn type_tree_owner_and_wire_mutations_are_not_dimension_equality() {
    let bytes = packet(gate(SingleGate::H), BasisType::Bit, Version::V2);
    let target = hadamard();
    for b in [
        UnitaryBoundary::new(
            BasisType::pair(BasisType::Unit, BasisType::Bit),
            port(0, &[7]),
            port(1, &[7]),
        )
        .unwrap(),
        UnitaryBoundary::new(BasisType::Bit, port(9, &[7]), port(1, &[7])).unwrap(),
        UnitaryBoundary::new(BasisType::Bit, port(0, &[7]), port(9, &[7])).unwrap(),
        UnitaryBoundary::new(BasisType::Bit, port(0, &[7]), port(1, &[8])).unwrap(),
    ] {
        assert_eq!(
            check_unitary(&bytes, &b, &target, &mut Budget::new(DEFAULT_EXACT_WORK))
                .unwrap_err()
                .code,
            "contract"
        );
    }
    let no_types =
        interchange::export(&verify(gate(SingleGate::H)).unwrap(), None, Version::V2).unwrap();
    assert_eq!(
        check_unitary(
            &no_types,
            &boundary(),
            &target,
            &mut Budget::new(DEFAULT_EXACT_WORK)
        )
        .unwrap_err()
        .code,
        "contract"
    );
}

#[test]
fn phase_on_unit_and_zero_width_owner_are_retained() {
    let bytes = packet(
        raw(
            port(0, &[]),
            vec![RawOp::ApplyUnitary {
                input: TokenId(0),
                output: TokenId(1),
                steps: vec![CircuitStep {
                    controls: vec![],
                    action: CircuitAction::Monomial {
                        indices: vec![],
                        permutation: vec![0],
                        phases: vec![4],
                    },
                }],
            }],
            1,
        ),
        BasisType::Unit,
        Version::V2,
    );
    let b = UnitaryBoundary::new(BasisType::Unit, port(0, &[]), port(1, &[])).unwrap();
    let minus = Matrix::new(1, 1, vec![Exact::integer(-1)]).unwrap();
    check_unitary(&bytes, &b, &minus, &mut Budget::new(DEFAULT_EXACT_WORK)).unwrap();
    assert_eq!(
        check_unitary(
            &bytes,
            &b,
            &Matrix::identity(1).unwrap(),
            &mut Budget::new(DEFAULT_EXACT_WORK)
        )
        .unwrap_err()
        .code,
        "contract"
    );
    let ghost = UnitaryBoundary::new(BasisType::Unit, port(0, &[]), port(2, &[])).unwrap();
    assert_eq!(
        check_unitary(&bytes, &ghost, &minus, &mut Budget::new(DEFAULT_EXACT_WORK))
            .unwrap_err()
            .code,
        "contract"
    );
}

#[test]
fn embedded_receipts_are_reconstructed_before_leaf_equality() {
    let evidence = Arc::new(
        FunctionEvidence::check(
            BasisType::Bit,
            gate(SingleGate::H),
            gate(SingleGate::H),
            FunctionIdentity {
                implementation: "impl".into(),
                specification: "spec".into(),
                sources: vec![],
            },
            &mut Budget::new(DEFAULT_EXACT_WORK),
        )
        .unwrap(),
    );
    let bytes = packet(
        raw(
            port(0, &[7]),
            vec![RawOp::ApplyUnitary {
                input: TokenId(0),
                output: TokenId(1),
                steps: vec![CircuitStep {
                    controls: vec![],
                    action: CircuitAction::Contract {
                        indices: vec![0],
                        evidence,
                        adjoint: false,
                    },
                }],
            }],
            1,
        ),
        BasisType::Bit,
        Version::V2,
    );
    check_unitary(
        &bytes,
        &boundary(),
        &hadamard(),
        &mut Budget::new(DEFAULT_EXACT_WORK),
    )
    .unwrap();
    let text = String::from_utf8(bytes).unwrap();
    assert!(text.contains("\"h\""));
    let forged = text.replacen("\"h\"", "\"x\"", 1);
    let error = check_unitary(
        forged.as_bytes(),
        &boundary(),
        &hadamard(),
        &mut Budget::new(DEFAULT_EXACT_WORK),
    )
    .unwrap_err();
    assert_eq!(error.code, "contract");
    assert!(error.json_pointer.starts_with("/evidence/"));
}

#[test]
fn shared_exact_budget_is_not_reset_for_each_leaf() {
    let bytes = packet(gate(SingleGate::H), BasisType::Bit, Version::V2);
    let b = boundary();
    let target = hadamard();
    let cost = check_unitary(&bytes, &b, &target, &mut Budget::new(DEFAULT_EXACT_WORK))
        .unwrap()
        .exact_work();
    assert!(cost > 0);
    let mut exactly = Budget::new(cost * 2);
    for _ in 0..2 {
        check_unitary(&bytes, &b, &target, &mut exactly).unwrap();
    }
    assert_eq!(exactly.remaining(), 0);
    let mut short = Budget::new(cost * 2 - 1);
    check_unitary(&bytes, &b, &target, &mut short).unwrap();
    assert_eq!(
        check_unitary(&bytes, &b, &target, &mut short)
            .unwrap_err()
            .code,
        "limit"
    );
    assert_eq!(
        check_unitary(
            &bytes,
            &b,
            &target,
            &mut Budget::new(DEFAULT_EXACT_WORK + 1)
        )
        .unwrap_err()
        .code,
        "limit"
    );
}

#[test]
fn malformed_payload_matrix_and_outside_six_bit_boundary_reject() {
    let bytes = packet(gate(SingleGate::H), BasisType::Bit, Version::V2);
    let mut text = String::from_utf8(bytes).unwrap();
    text.insert_str(1, "\"verified\":true,");
    assert_eq!(
        check_unitary(
            text.as_bytes(),
            &boundary(),
            &hadamard(),
            &mut Budget::new(DEFAULT_EXACT_WORK)
        )
        .unwrap_err()
        .code,
        "format"
    );
    let seven = BasisType::Tuple(vec![BasisType::Bit; 7]);
    assert_eq!(
        UnitaryBoundary::new(
            seven,
            port(0, &[0, 1, 2, 3, 4, 5, 6]),
            port(1, &[0, 1, 2, 3, 4, 5, 6])
        )
        .unwrap_err()
        .code,
        "limit"
    );
    let bytes = packet(gate(SingleGate::H), BasisType::Bit, Version::V2);
    for bad in [
        Matrix::identity(1).unwrap(),
        Matrix::new(2, 2, vec![Exact::zero(); 4]).unwrap(),
    ] {
        assert_eq!(
            check_unitary(
                &bytes,
                &boundary(),
                &bad,
                &mut Budget::new(DEFAULT_EXACT_WORK)
            )
            .unwrap_err()
            .code,
            "contract"
        );
    }
}

#[test]
fn classical_phi_output_uses_verified_fresh_axes() {
    let bytes = packet(
        raw(
            port(0, &[7]),
            vec![
                RawOp::ClassicalConst {
                    value: false,
                    output: ClassicalId(0),
                },
                RawOp::ClassicalBranch {
                    condition: ClassicalId(0),
                    then_ops: vec![RawOp::Gate {
                        gate: SingleGate::H,
                        input: TokenId(0),
                        output: TokenId(1),
                    }],
                    else_ops: vec![RawOp::Gate {
                        gate: SingleGate::X,
                        input: TokenId(0),
                        output: TokenId(2),
                    }],
                    quantum_phis: vec![QuantumPhi {
                        then_token: TokenId(1),
                        else_token: TokenId(2),
                        output: TokenId(3),
                        output_wires: vec![WireId(44)],
                    }],
                    classical_phis: vec![],
                },
            ],
            3,
        ),
        BasisType::Bit,
        Version::V2,
    );
    let correct = UnitaryBoundary::new(BasisType::Bit, port(0, &[7]), port(3, &[44])).unwrap();
    let wrong = UnitaryBoundary::new(BasisType::Bit, port(0, &[7]), port(3, &[7])).unwrap();
    let target = permutation(&[1, 0]);
    check_unitary(
        &bytes,
        &correct,
        &target,
        &mut Budget::new(DEFAULT_EXACT_WORK),
    )
    .unwrap();
    assert_eq!(
        check_unitary(
            &bytes,
            &wrong,
            &target,
            &mut Budget::new(DEFAULT_EXACT_WORK)
        )
        .unwrap_err()
        .code,
        "contract"
    );
}

#[test]
fn six_bit_identity_stays_within_the_finite_matrix_boundary() {
    let ty = BasisType::Tuple(vec![BasisType::Bit; 6]);
    let input = port(0, &[0, 1, 2, 3, 4, 5]);
    let b = UnitaryBoundary::new(ty.clone(), input.clone(), input.clone()).unwrap();
    let bytes = packet(raw(input, vec![], 0), ty, Version::V2);
    let checked = check_unitary(
        &bytes,
        &b,
        &Matrix::identity(64).unwrap(),
        &mut Budget::new(DEFAULT_EXACT_WORK),
    )
    .unwrap();
    assert_eq!(checked.meaning().rows(), 64);
    assert!(checked.exact_work() < DEFAULT_EXACT_WORK);
}

#[test]
fn fresh_process_child() {
    let Some(path) = std::env::var_os("QLEISLI_FINITE_LEAF_CHILD_PATH") else {
        return;
    };
    let bytes = std::fs::read(path).unwrap();
    // The required boundary and H matrix are independent of the transported IR.
    check_unitary(
        &bytes,
        &boundary(),
        &hadamard(),
        &mut Budget::new(DEFAULT_EXACT_WORK),
    )
    .unwrap();
}

#[test]
fn fresh_process_reconstruction_rejects_a_global_phase_mutation() {
    let root = common::SourceRoot::new("observe fn main() -> Unit { () }");
    let path = root.0.join("leaf.json");
    let negative = raw(
        port(0, &[7]),
        vec![RawOp::ApplyUnitary {
            input: TokenId(0),
            output: TokenId(1),
            steps: vec![
                CircuitStep {
                    controls: vec![],
                    action: CircuitAction::Hadamard { target: 0 },
                },
                CircuitStep {
                    controls: vec![],
                    action: CircuitAction::Monomial {
                        indices: vec![],
                        permutation: vec![0],
                        phases: vec![4],
                    },
                },
            ],
        }],
        1,
    );
    for (program, accepted) in [(gate(SingleGate::H), true), (negative, false)] {
        std::fs::write(&path, packet(program, BasisType::Bit, Version::V2)).unwrap();
        let result = Command::new(std::env::current_exe().unwrap())
            .args(["--exact", "fresh_process_child", "--nocapture"])
            .env("QLEISLI_FINITE_LEAF_CHILD_PATH", &path)
            .output()
            .unwrap();
        assert_eq!(result.status.success(), accepted, "{result:?}");
        if !accepted {
            assert!(String::from_utf8_lossy(&result.stderr).contains("does not hold"));
        }
    }
}

#[test]
fn serialized_meaning_retains_both_byte_strings_and_exact_work() {
    let bytes = packet(gate(SingleGate::H), BasisType::Bit, Version::V2);
    let description = finite_matrix::encode(&hadamard()).unwrap();
    let mut budget = Budget::new(DEFAULT_EXACT_WORK);
    let checked = check_serialized_unitary(&bytes, &boundary(), &description, &mut budget).unwrap();
    assert_eq!(
        checked.exact_work(),
        DEFAULT_EXACT_WORK - budget.remaining()
    );
    assert_eq!(checked.exact_work(), checked.leaf().exact_work() + 16);
    assert!(checked.matches(&bytes.clone(), &boundary(), &description.clone()));
    assert_eq!(checked.description(), description);
    assert_eq!(checked.leaf().meaning(), &hadamard());
    let mut changed = description.clone();
    changed.push(b' ');
    assert!(!checked.matches(&bytes, &boundary(), &changed));
    let again = check_serialized_unitary(&bytes, &boundary(), &changed, &mut budget).unwrap();
    assert_eq!(again.leaf().meaning(), checked.leaf().meaning());
    let mut changed_program = bytes.clone();
    changed_program.push(b' ');
    assert!(!checked.matches(&changed_program, &boundary(), &description));
    let wrong = UnitaryBoundary::new(BasisType::Bit, port(0, &[7]), port(1, &[8])).unwrap();
    assert!(!checked.matches(&bytes, &wrong, &description));
}

#[test]
fn serialized_equations_reject_phase_shape_and_authority_flag_mutations() {
    let bytes = packet(gate(SingleGate::H), BasisType::Bit, Version::V2);
    let minus = Matrix::new(
        2,
        2,
        hadamard()
            .entries()
            .iter()
            .map(|x| x.neg().unwrap())
            .collect(),
    )
    .unwrap();
    for bad in [
        minus,
        Matrix::new(1, 2, vec![Exact::one(), Exact::zero()]).unwrap(),
    ] {
        let description = finite_matrix::encode(&bad).unwrap();
        assert_eq!(
            check_serialized_unitary(
                &bytes,
                &boundary(),
                &description,
                &mut Budget::new(DEFAULT_EXACT_WORK)
            )
            .unwrap_err()
            .code,
            "contract"
        );
    }
    let good = String::from_utf8(finite_matrix::encode(&hadamard()).unwrap()).unwrap();
    let flagged = good.replacen('{', "{\"checked\":true,", 1);
    assert_eq!(
        check_serialized_unitary(
            &bytes,
            &boundary(),
            flagged.as_bytes(),
            &mut Budget::new(DEFAULT_EXACT_WORK)
        )
        .unwrap_err()
        .code,
        "format"
    );
    let mut padded = good.into_bytes();
    padded.resize(16 << 20, b' ');
    assert_eq!(
        check_serialized_unitary(
            &bytes,
            &boundary(),
            &padded,
            &mut Budget::new(DEFAULT_EXACT_WORK)
        )
        .unwrap_err()
        .code,
        "limit"
    );
}

#[test]
fn serialized_reconstruction_uses_one_budget_for_decode_and_all_leaves() {
    let bytes = packet(gate(SingleGate::H), BasisType::Bit, Version::V2);
    let description = finite_matrix::encode(&hadamard()).unwrap();
    let work = check_serialized_unitary(
        &bytes,
        &boundary(),
        &description,
        &mut Budget::new(DEFAULT_EXACT_WORK),
    )
    .unwrap()
    .exact_work();
    let mut budget = Budget::new(work + 15);
    check_serialized_unitary(&bytes, &boundary(), &description, &mut budget).unwrap();
    assert_eq!(budget.remaining(), 15);
    assert_eq!(
        check_serialized_unitary(&bytes, &boundary(), &description, &mut budget)
            .unwrap_err()
            .code,
        "limit"
    );
}

#[test]
fn fresh_serialized_process_child() {
    let Some(root) = std::env::var_os("QLEISLI_SERIALIZED_LEAF_CHILD_ROOT") else {
        return;
    };
    let root = std::path::PathBuf::from(root);
    let payload = std::fs::read(root.join("implementation.json")).unwrap();
    let description = std::fs::read(root.join("meaning.json")).unwrap();
    check_serialized_unitary(
        &payload,
        &boundary(),
        &description,
        &mut Budget::new(DEFAULT_EXACT_WORK),
    )
    .unwrap();
}

#[test]
fn fresh_process_decodes_both_sides_and_rejects_changed_meaning() {
    let root = common::SourceRoot::new("observe fn main() -> Unit { () }");
    std::fs::write(
        root.0.join("implementation.json"),
        packet(gate(SingleGate::H), BasisType::Bit, Version::V2),
    )
    .unwrap();
    let minus = Matrix::new(
        2,
        2,
        hadamard()
            .entries()
            .iter()
            .map(|x| x.neg().unwrap())
            .collect(),
    )
    .unwrap();
    for (meaning, accepted) in [(hadamard(), true), (minus, false)] {
        std::fs::write(
            root.0.join("meaning.json"),
            finite_matrix::encode(&meaning).unwrap(),
        )
        .unwrap();
        let result = Command::new(std::env::current_exe().unwrap())
            .args(["--exact", "fresh_serialized_process_child", "--nocapture"])
            .env("QLEISLI_SERIALIZED_LEAF_CHILD_ROOT", &root.0)
            .output()
            .unwrap();
        assert_eq!(result.status.success(), accepted, "{result:?}");
        if !accepted {
            assert!(String::from_utf8_lossy(&result.stderr).contains("does not hold"));
        }
    }
}
