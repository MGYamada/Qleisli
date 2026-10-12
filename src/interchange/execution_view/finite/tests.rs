// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::contract::exact::Exact;
use crate::interchange::{Decoder, codec::Codec, json};

fn write(body: impl FnOnce(&mut View<'_>) -> Result<()>) -> Vec<u8> {
    let dependencies = BTreeMap::new();
    let mut view = View {
        writer: Writer {
            bytes: b"QDV1".to_vec(),
            limit: MAX_BYTES,
            depth: 0,
        },
        dependencies: &dependencies,
    };
    body(&mut view).unwrap();
    view.writer.bytes
}

fn vectors() -> json::Value {
    json::parse(include_bytes!(
        "../../../../tests/fixtures/verification_v030/execution-view-binding/finite-walker-vectors.json"
    )).unwrap()
}

fn program(row: &json::Value) -> RawProgram {
    let data = if row.field("kind").unwrap().text().unwrap() == "raw-source" {
        let directory = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/verification_v030/execution-view-binding/"
        );
        let artifact = json::parse(
            &std::fs::read(format!(
                "{directory}{}",
                row.field("source").unwrap().text().unwrap()
            ))
            .unwrap(),
        )
        .unwrap();
        artifact.field("programs").unwrap().array().unwrap()[0].clone()
    } else {
        row.field("program").unwrap().clone()
    };
    RawProgram::read(&data, &Decoder { evidence: &[] }).unwrap()
}

#[test]
fn typed_raw_basis_and_matrix_walkers_match_shared_descriptions() {
    for row in vectors().array().unwrap() {
        let actual = match row.field("kind").unwrap().text().unwrap() {
            "raw" | "raw-source" => raw(&program(row), &[]).unwrap(),
            "basis" => {
                let basis =
                    BasisType::read(row.field("basis").unwrap(), &Decoder { evidence: &[] })
                        .unwrap();
                write(|w| w.basis(&basis))
            }
            "matrix" => {
                let data = row.field("matrix").unwrap();
                let entries = data
                    .field("entries")
                    .unwrap()
                    .array()
                    .unwrap()
                    .iter()
                    .map(|scalar| {
                        let coefficients: Vec<_> = scalar
                            .array()
                            .unwrap()
                            .iter()
                            .map(|pair| {
                                let pair = pair.array().unwrap();
                                (
                                    pair[0].text().unwrap().parse().unwrap(),
                                    pair[1].number().unwrap() as u32,
                                )
                            })
                            .collect();
                        Exact::from_dyadics(coefficients.try_into().unwrap()).unwrap()
                    })
                    .collect();
                let matrix = Matrix::new(
                    data.field("rows").unwrap().number().unwrap() as usize,
                    data.field("cols").unwrap().number().unwrap() as usize,
                    entries,
                )
                .unwrap();
                write(|w| w.matrix(&matrix))
            }
            _ => panic!("unknown finite vector kind"),
        };
        let expected = super::super::encode(&super::super::tests::vector_value(
            row.field("view").unwrap(),
        ))
        .unwrap();
        assert_eq!(
            actual,
            expected,
            "{}",
            row.field("name").unwrap().text().unwrap()
        );
    }
}

#[test]
fn actual_mutations_preserve_neither_phase_axis_owner_effect_nor_branch_view() {
    let rows = vectors();
    let original = program(&rows.array().unwrap()[3]);
    let original_bytes = raw(&original, &[]).unwrap();
    let mut mutations = Vec::new();
    let mut altered = original.clone();
    altered.quantum_inputs[0].wires.reverse();
    mutations.push(altered);
    let mut altered = original.clone();
    altered.quantum_inputs[1].token = TokenId(100);
    mutations.push(altered);
    let mut altered = original.clone();
    altered.quantum_outputs.reverse();
    mutations.push(altered);
    let mut altered = original.clone();
    altered.declared_effect = Effect::Unitary;
    mutations.push(altered);
    for field in 0..5 {
        let mut altered = original.clone();
        let RawOp::ClassicalBranch {
            then_ops,
            else_ops,
            quantum_phis,
            classical_phis,
            ..
        } = altered.operations.last_mut().unwrap()
        else {
            panic!("expected both branch arms")
        };
        match field {
            0 => then_ops.clear(),
            1 => else_ops.clear(),
            2 => quantum_phis[0].output_wires.reverse(),
            3 => quantum_phis[1].output = TokenId(101),
            _ => classical_phis[0].else_id = ClassicalId(102),
        }
        mutations.push(altered);
    }
    let mut altered = original.clone();
    let RawOp::ApplyUnitary { steps, .. } = &mut altered.operations[10] else {
        panic!("expected circuit")
    };
    let CircuitAction::Monomial { phases, .. } = &mut steps[1].action else {
        panic!("expected phase")
    };
    phases[0] = 4;
    mutations.push(altered);
    for altered in mutations {
        assert_ne!(raw(&altered, &[]).unwrap(), original_bytes);
    }
    // The retained input remains unchanged. These are transport checks; native
    // acceptance and decoded_view rejection are separate integration tests.
    assert_eq!(raw(&original, &[]).unwrap(), original_bytes);
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn retained_evidence_caches_and_original_dependency_indices_are_read() {
    use crate::contract::{
        DEFAULT_EXACT_WORK, FunctionIdentity,
        exact::Budget,
        meaning::{FiniteMeaning, MeaningEvidence},
    };
    let meaning = FiniteMeaning::permutation(BasisType::Bit, vec![1, 0]).unwrap();
    let receipt = MeaningEvidence::check(
        meaning.target_ir().unwrap(),
        meaning,
        FunctionIdentity {
            implementation: "x".into(),
            specification: "flip".into(),
            sources: vec![("𝄞.qli".into(), "source identity only".into())],
        },
        &mut Budget::new(DEFAULT_EXACT_WORK),
    )
    .unwrap()
    .receipt();
    let actual = write(|w| w.evidence(&receipt));
    assert!(
        actual
            .windows("𝄞.qli".len())
            .any(|s| s == "𝄞.qli".as_bytes())
    );
    assert_ne!(
        write(|w| w.matrix(receipt.meaning())),
        write(|w| w.matrix(&Matrix::identity(2).unwrap()))
    );
    let program = RawProgram {
        quantum_inputs: vec![QuantumPort {
            token: TokenId(0),
            wires: vec![WireId(0)],
            shape: BasisShape { bits: 1 },
        }],
        classical_inputs: vec![],
        operations: vec![RawOp::ApplyUnitary {
            input: TokenId(0),
            output: TokenId(1),
            steps: vec![CircuitStep {
                controls: vec![],
                action: CircuitAction::Contract {
                    indices: vec![0],
                    evidence: receipt.clone(),
                    adjoint: false,
                },
            }],
        }],
        quantum_outputs: vec![TokenId(1)],
        classical_outputs: vec![],
        declared_effect: Effect::Unitary,
    };
    assert_eq!(raw(&program, &[]).unwrap_err().code, "format");
    let bytes = raw(&program, std::slice::from_ref(&receipt)).unwrap();
    let mut altered = program.clone();
    let RawOp::ApplyUnitary { steps, .. } = &mut altered.operations[0] else {
        unreachable!()
    };
    let CircuitAction::Contract { adjoint, .. } = &mut steps[0].action else {
        unreachable!()
    };
    *adjoint = true;
    assert_ne!(
        bytes,
        raw(&altered, std::slice::from_ref(&receipt)).unwrap()
    );
    assert_eq!(
        raw(&program, &[receipt.clone(), receipt]).unwrap_err().code,
        "format"
    );
}
