//! VM-22 frozen, small-system migration inputs. No new acceptance API.
//! Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

use std::path::PathBuf;

use qleisli::contract::exact::{Budget, Exact, Matrix};
use qleisli::contract::{BasisType, DEFAULT_EXACT_WORK};
use qleisli::interchange::finite_leaf::{UnitaryBoundary, check_serialized_unitary};
use qleisli::interchange::{self, RootInterface, Version, finite_matrix};
use qleisli::ir::*;
use qleisli::verify;

fn port(token: u32, wires: &[u32]) -> QuantumPort {
    QuantumPort {
        token: TokenId(token),
        wires: wires.iter().copied().map(WireId).collect(),
        shape: BasisShape {
            bits: u8::try_from(wires.len()).unwrap(),
        },
    }
}

struct Case {
    name: &'static str,
    raw: RawProgram,
    boundary: UnitaryBoundary,
    required: Matrix,
}

fn case(
    name: &'static str,
    ty: BasisType,
    wires: &[u32],
    ops: Vec<RawOp>,
    output: u32,
    required: Matrix,
) -> Case {
    let input = port(0, wires);
    Case {
        name,
        raw: RawProgram {
            quantum_inputs: vec![input.clone()],
            classical_inputs: vec![],
            operations: ops,
            quantum_outputs: vec![TokenId(output)],
            classical_outputs: vec![],
            declared_effect: Effect::Unitary,
        },
        boundary: UnitaryBoundary::new(ty, input, port(output, wires)).unwrap(),
        required,
    }
}

fn permutation(table: &[usize]) -> Matrix {
    let n = table.len();
    let mut entries = vec![Exact::zero(); n * n];
    for (x, y) in table.iter().enumerate() {
        entries[y * n + x] = Exact::one();
    }
    Matrix::new(n, n, entries).unwrap()
}

fn cases() -> Vec<Case> {
    let h = Exact::inv_sqrt2();
    let t = Matrix::new(
        2,
        2,
        vec![Exact::one(), Exact::zero(), Exact::zero(), Exact::phase(1)],
    )
    .unwrap();
    // The required equations are fixed here, before inspecting/extracting IR.
    vec![
        case(
            "h",
            BasisType::Bit,
            &[7],
            vec![RawOp::Gate {
                gate: SingleGate::H,
                input: TokenId(0),
                output: TokenId(1),
            }],
            1,
            Matrix::new(2, 2, vec![h, h, h, h.neg().unwrap()]).unwrap(),
        ),
        case(
            "t",
            BasisType::Bit,
            &[7],
            vec![RawOp::Gate {
                gate: SingleGate::T,
                input: TokenId(0),
                output: TokenId(1),
            }],
            1,
            t.clone(),
        ),
        case(
            "unit_phase",
            BasisType::Unit,
            &[],
            vec![RawOp::ApplyUnitary {
                input: TokenId(0),
                output: TokenId(1),
                steps: vec![CircuitStep {
                    controls: vec![],
                    action: CircuitAction::Monomial {
                        indices: vec![],
                        permutation: vec![0],
                        phases: vec![1],
                    },
                }],
            }],
            1,
            Matrix::new(1, 1, vec![Exact::phase(1)]).unwrap(),
        ),
        case(
            "toffoli",
            BasisType::Tuple(vec![BasisType::Bit; 3]),
            &[7, 19, 31],
            vec![
                RawOp::Split {
                    input: TokenId(0),
                    left: TokenId(1),
                    right: TokenId(2),
                    left_bits: 1,
                },
                RawOp::Split {
                    input: TokenId(2),
                    left: TokenId(3),
                    right: TokenId(4),
                    left_bits: 1,
                },
                RawOp::Toffoli {
                    control_a: TokenId(1),
                    control_b: TokenId(3),
                    target: TokenId(4),
                    control_a_out: TokenId(5),
                    control_b_out: TokenId(6),
                    target_out: TokenId(7),
                },
                RawOp::Join {
                    left: TokenId(5),
                    right: TokenId(6),
                    output: TokenId(8),
                },
                RawOp::Join {
                    left: TokenId(8),
                    right: TokenId(7),
                    output: TokenId(9),
                },
            ],
            9,
            permutation(&[0, 1, 2, 7, 4, 5, 6, 3]),
        ),
        case(
            "raw_qif_unit",
            BasisType::pair(BasisType::Bit, BasisType::Unit),
            &[7],
            vec![
                RawOp::Split {
                    input: TokenId(0),
                    left: TokenId(1),
                    right: TokenId(2),
                    left_bits: 1,
                },
                RawOp::QuantumIf {
                    control: TokenId(1),
                    target: TokenId(2),
                    control_out: TokenId(3),
                    target_out: TokenId(4),
                    zero_ops: vec![],
                    one_ops: vec![UnitaryStep::ScalarPhase(ScalarPhase::EighthTurn)],
                },
                RawOp::Join {
                    left: TokenId(3),
                    right: TokenId(4),
                    output: TokenId(5),
                },
            ],
            5,
            t,
        ),
        case(
            "raw_computed_target",
            BasisType::pair(BasisType::Bit, BasisType::Bit),
            &[7, 19],
            vec![
                RawOp::Split {
                    input: TokenId(0),
                    left: TokenId(1),
                    right: TokenId(2),
                    left_bits: 1,
                },
                RawOp::ComputeUseUncompute {
                    source: TokenId(1),
                    source_out: TokenId(3),
                    targets: vec![TargetTransition {
                        input: TokenId(2),
                        output: TokenId(4),
                    }],
                    ancilla_wires: vec![WireId(31)],
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
                        gate: SingleGate::X,
                    }],
                },
                RawOp::Join {
                    left: TokenId(3),
                    right: TokenId(4),
                    output: TokenId(5),
                },
            ],
            5,
            permutation(&[0, 3, 2, 1]),
        ),
    ]
}

fn frozen(name: &str, generated: &[u8]) -> Vec<u8> {
    let fixture = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/verification_v022/finite")
        .join(name);
    // An explicit local capture only; CI and ordinary tests never refresh data.
    if let Some(directory) = std::env::var_os("QLEISLI_VM22_CAPTURE") {
        let directory = PathBuf::from(directory);
        std::fs::create_dir_all(&directory).unwrap();
        std::fs::write(directory.join(name), generated).unwrap();
        return generated.to_vec();
    }
    let bytes = std::fs::read(&fixture).unwrap_or_else(|e| panic!("{}: {e}", fixture.display()));
    assert_eq!(
        bytes, generated,
        "frozen bytes changed: {name}; review the independent request and inventory"
    );
    bytes
}

#[test]
fn frozen_finite_artifacts_match_independent_phase_exact_requests() {
    for case in cases() {
        let request = frozen(
            &format!("{}.matrix.json", case.name),
            &finite_matrix::encode(&case.required).unwrap(),
        );
        let wrong = Matrix::new(
            case.required.rows(),
            case.required.cols(),
            case.required
                .entries()
                .iter()
                .map(|x| x.neg().unwrap())
                .collect(),
        )
        .unwrap();
        let wrong = frozen(
            &format!("{}.wrong-phase.json", case.name),
            &finite_matrix::encode(&wrong).unwrap(),
        );
        for (version, tag) in [(Version::V1, "v1"), (Version::V2, "v2")] {
            let artifact = interchange::export(
                &verify(case.raw.clone()).unwrap(),
                Some(&RootInterface {
                    input: case.boundary.signature().clone(),
                    output: case.boundary.signature().clone(),
                }),
                version,
            )
            .unwrap();
            let artifact = frozen(&format!("{}.{tag}.qirf", case.name), &artifact);
            check_serialized_unitary(
                &artifact,
                &case.boundary,
                &request,
                &mut Budget::new(DEFAULT_EXACT_WORK),
            )
            .unwrap();
            assert_eq!(
                check_serialized_unitary(
                    &artifact,
                    &case.boundary,
                    &wrong,
                    &mut Budget::new(DEFAULT_EXACT_WORK)
                )
                .unwrap_err()
                .code,
                "contract"
            );
            assert!(
                check_serialized_unitary(&artifact, &case.boundary, &request, &mut Budget::new(0))
                    .is_err()
            );
        }
    }
}

#[test]
fn frozen_raw_inputs_reject_aliases_and_missing_zero_width_owners() {
    let mut all = cases();
    let mut toffoli = all.remove(3).raw;
    if let RawOp::Toffoli { control_b, .. } = &mut toffoli.operations[2] {
        *control_b = TokenId(1);
    }
    assert!(verify(toffoli).is_err());
    let mut unit = all.remove(2).raw;
    unit.quantum_outputs.clear();
    assert!(verify(unit).is_err());
}

#[test]
fn frozen_request_rejects_axis_identity_type_and_domain_changes() {
    let mut all = cases();
    let case = all.remove(5);
    let artifact = interchange::export(
        &verify(case.raw).unwrap(),
        Some(&RootInterface {
            input: case.boundary.signature().clone(),
            output: case.boundary.signature().clone(),
        }),
        Version::V2,
    )
    .unwrap();
    let request = finite_matrix::encode(&case.required).unwrap();
    for boundary in [
        UnitaryBoundary::new(
            case.boundary.signature().clone(),
            port(0, &[19, 7]),
            port(5, &[19, 7]),
        )
        .unwrap(),
        UnitaryBoundary::new(
            case.boundary.signature().clone(),
            port(10, &[7, 19]),
            port(5, &[7, 19]),
        )
        .unwrap(),
        UnitaryBoundary::new(
            BasisType::pair(
                BasisType::Unit,
                BasisType::pair(BasisType::Bit, BasisType::Bit),
            ),
            port(0, &[7, 19]),
            port(5, &[7, 19]),
        )
        .unwrap(),
    ] {
        assert_eq!(
            check_serialized_unitary(
                &artifact,
                &boundary,
                &request,
                &mut Budget::new(DEFAULT_EXACT_WORK)
            )
            .unwrap_err()
            .code,
            "contract"
        );
    }
    let wrong_domain = String::from_utf8(request)
        .unwrap()
        .replace("zeta8-dyadic-v1", "phase256-word-v1");
    assert_eq!(
        check_serialized_unitary(
            &artifact,
            &case.boundary,
            wrong_domain.as_bytes(),
            &mut Budget::new(DEFAULT_EXACT_WORK)
        )
        .unwrap_err()
        .code,
        "format"
    );
}
