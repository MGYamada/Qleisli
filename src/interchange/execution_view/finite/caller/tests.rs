// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::contract::{
    DEFAULT_EXACT_WORK, FunctionIdentity, exact::Budget, meaning::FiniteMeaning,
};
use crate::interchange::{Encoder, Version, json};

fn apply(evidence: Arc<FunctionEvidence>, input: u32, output: u32) -> RawOp {
    RawOp::ApplyUnitary {
        input: TokenId(input),
        output: TokenId(output),
        steps: contract_steps(evidence),
    }
}

fn contract_steps(evidence: Arc<FunctionEvidence>) -> Vec<CircuitStep> {
    vec![CircuitStep {
        controls: vec![],
        action: CircuitAction::Contract {
            indices: vec![0],
            evidence,
            adjoint: false,
        },
    }]
}

fn branch_certified(leaf: &Arc<FunctionEvidence>) -> RawProgram {
    let use_alias = Arc::new(leaf.as_ref().clone());
    let logical_alias = Arc::new(leaf.as_ref().clone());
    body(
        vec![
            RawOp::ClassicalConst {
                value: true,
                output: ClassicalId(0),
            },
            RawOp::ClassicalBranch {
                condition: ClassicalId(0),
                then_ops: vec![apply(leaf.clone(), 0, 1)],
                else_ops: vec![RawOp::CertifiedCompute {
                    source: TokenId(0),
                    source_out: TokenId(2),
                    ancilla_wires: vec![WireId(1)],
                    function: vec![0, 0],
                    use_steps: contract_steps(use_alias),
                    logical_steps: contract_steps(logical_alias),
                }],
                quantum_phis: vec![QuantumPhi {
                    then_token: TokenId(1),
                    else_token: TokenId(2),
                    output: TokenId(3),
                    output_wires: vec![WireId(2)],
                }],
                classical_phis: vec![],
            },
        ],
        3,
    )
}
fn body(operations: Vec<RawOp>, output: u32) -> RawProgram {
    RawProgram {
        quantum_inputs: vec![QuantumPort {
            token: TokenId(0),
            wires: vec![WireId(0)],
            shape: BasisShape { bits: 1 },
        }],
        classical_inputs: vec![],
        operations,
        quantum_outputs: vec![TokenId(output)],
        classical_outputs: vec![],
        declared_effect: Effect::Unitary,
    }
}
fn checked(implementation: RawProgram, name: &str) -> Arc<FunctionEvidence> {
    let target = FiniteMeaning::permutation(BasisType::Bit, vec![1, 0])
        .unwrap()
        .target_ir()
        .unwrap();
    Arc::new(
        FunctionEvidence::check(
            BasisType::Bit,
            implementation,
            target,
            FunctionIdentity {
                implementation: name.into(),
                specification: "flip".into(),
                sources: vec![],
            },
            &mut Budget::new(DEFAULT_EXACT_WORK),
        )
        .unwrap(),
    )
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn aliases_include_children_hidden_by_equal_snapshot_deduplication() {
    let refusal = json::parse(include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/",
        "tests/fixtures/verification_v030/execution-view-binding/first-caller-branch-refusal.json"
    )))
    .unwrap();
    let original = refusal
        .field("original_artifact_text")
        .unwrap()
        .text()
        .unwrap();
    assert_eq!(
        crate::interchange::native::Kernel::selected()
            .unwrap()
            .inspect(original.as_bytes(), None)
            .unwrap_err()
            .code,
        refusal.field("native_error_code").unwrap().text().unwrap()
    );
    let recipes = json::parse(include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/",
        "tests/fixtures/verification_v030/execution-view-binding/caller-alias-recipes.json"
    )))
    .unwrap();
    let target = FiniteMeaning::permutation(BasisType::Bit, vec![1, 0])
        .unwrap()
        .target_ir()
        .unwrap();
    let leaf = checked(target, "leaf");
    for row in recipes.array().unwrap() {
        let recipe = row.field("recipe").unwrap().text().unwrap();
        let root = if recipe == "branch-certified" {
            branch_certified(&leaf)
        } else {
            let (first, second) = match recipe {
                "same-arc" => (leaf.clone(), leaf.clone()),
                "cloned-arc" => (leaf.clone(), Arc::new(leaf.as_ref().clone())),
                "independent-parents" => (
                    checked(body(vec![apply(leaf.clone(), 0, 1)], 1), "same-parent"),
                    checked(body(vec![apply(leaf.clone(), 0, 1)], 1), "same-parent"),
                ),
                _ => panic!("unknown frozen alias recipe"),
            };
            assert_eq!(first.snapshot_key(), second.snapshot_key());
            body(
                vec![apply(first.clone(), 0, 1), apply(second.clone(), 1, 2)],
                2,
            )
        };
        let mut encoder = Encoder::new(Version::V2);
        let root_index = encoder.program(&root).unwrap();
        assert_eq!(root_index, 0);
        assert_eq!(
            encoder.entries.len(),
            if recipe == "independent-parents" {
                2
            } else {
                1
            }
        );
        let origin = Origin::collect(&root, None, &encoder.canonical_evidence).unwrap();
        let mut exhausted = 0;
        assert_eq!(
            raw(&root, &mut vec![], &mut exhausted).unwrap_err().code,
            "limit"
        );
        let expected: Vec<_> = row
            .field("indices")
            .unwrap()
            .array()
            .unwrap()
            .iter()
            .map(|index| index.number().unwrap() as usize)
            .collect();
        assert_eq!(
            origin
                .aliases
                .iter()
                .map(|(index, _)| *index)
                .collect::<Vec<_>>(),
            expected
        );
        if recipe == "independent-parents" {
            let hidden = &origin.aliases[3].1;
            assert!(!encoder.seen.contains_key(&(Arc::as_ptr(hidden) as usize)));
            assert!(origin.indices.contains_key(&(Arc::as_ptr(hidden) as usize)));
            assert!(!Arc::ptr_eq(&origin.aliases[1].1, hidden));
        }
        let description = origin.describe().unwrap();
        let expected_view = crate::interchange::execution_view::encode(
            &crate::interchange::execution_view::tests::vector_value(row.field("view").unwrap()),
        )
        .unwrap();
        assert_eq!(description, expected_view, "recipe {recipe}");
        let mut missing = encoder.canonical_evidence.clone();
        missing.remove(origin.aliases.last().unwrap().1.snapshot_key());
        assert!(Origin::collect(&root, None, &missing).is_err());
        // The actual serialized original remains valid independently of the
        // proposed alias descriptions; no alias is minted into fresh evidence.
        let artifact = crate::interchange::finish_proposal(root_index, None, encoder).unwrap();
        assert_eq!(
            artifact,
            json::encode(row.field("artifact").unwrap()).unwrap(),
            "recipe {recipe}"
        );
        let accepted = crate::interchange::native::Kernel::selected()
            .unwrap()
            .check(&artifact, None)
            .unwrap();
        let expected_graph = crate::interchange::execution_view::encode(
            &crate::interchange::execution_view::tests::vector_value(
                row.field("graph_view").unwrap(),
            ),
        )
        .unwrap();
        assert_eq!(
            accepted.program().execution_view_description().unwrap(),
            expected_graph
        );
        let result = crate::interchange::native::Kernel::selected()
            .unwrap()
            .inspect(&artifact, None);
        assert!(
            result.is_ok(),
            "recipe {recipe}: {result:?}; original artifact: {}",
            String::from_utf8_lossy(&artifact)
        );
    }
}
