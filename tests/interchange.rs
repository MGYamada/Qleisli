mod common;
use common::SourceRoot;
use qleisli::contract::exact::Budget;
use qleisli::contract::meaning::{FiniteMeaning, MeaningEvidence};
use qleisli::contract::{BasisType, DEFAULT_EXACT_WORK, FunctionIdentity};
use qleisli::frontend::compile::compile_project;
use qleisli::interchange::{self, RootInterface, Version};
use qleisli::ir::*;
use qleisli::{VerifiedProgram, verify};
use std::process::Command;

fn identity() -> RawProgram {
    RawProgram {
        quantum_inputs: vec![QuantumPort {
            token: TokenId(0),
            wires: vec![WireId(17)],
            shape: BasisShape { bits: 1 },
        }],
        classical_inputs: vec![],
        operations: vec![],
        quantum_outputs: vec![TokenId(0)],
        classical_outputs: vec![],
        declared_effect: Effect::Unitary,
    }
}
fn request(signature: &str, tag: &str, table: &str) -> Vec<u8> {
    format!(r#"{{"format":"qleisli.request","version":1,"signature":{signature},"meaning":{{"tag":"{tag}","table":{table}}},"source_snapshot":null}}"#).into_bytes()
}
const BIT: &str = r#"{"tag":"bit"}"#;
const UNIT_BIT: &str = r#"{"tag":"pair","left":{"tag":"unit"},"right":{"tag":"bit"}}"#;
const BIT_UNIT: &str = r#"{"tag":"pair","left":{"tag":"bit"},"right":{"tag":"unit"}}"#;
const FLAT_UNIT_BIT_UNIT: &str =
    r#"{"tag":"tuple","fields":[{"tag":"unit"},{"tag":"bit"},{"tag":"unit"}]}"#;
const NESTED_UNIT_BIT_UNIT: &str = r#"{"tag":"pair","left":{"tag":"pair","left":{"tag":"unit"},"right":{"tag":"bit"}},"right":{"tag":"unit"}}"#;
fn interface(ty: BasisType) -> RootInterface {
    RootInterface {
        input: ty.clone(),
        output: ty,
    }
}

#[test]
fn nary_external_requests_reject_reassociation_and_noncanonical_arity() {
    let root = SourceRoot::new("observe fn main()->Unit {()} ");
    let path = root.0.join("artifact.json");
    let req = root.0.join("request.json");
    let bytes = interchange::export(
        &verify(identity()).unwrap(),
        Some(&interface(BasisType::Tuple(vec![
            BasisType::Unit,
            BasisType::Bit,
            BasisType::Unit,
        ]))),
        Version::V2,
    )
    .unwrap();
    std::fs::write(&path, &bytes).unwrap();
    for (shape, accepted) in [
        (FLAT_UNIT_BIT_UNIT, true),
        (NESTED_UNIT_BIT_UNIT, false),
        (BIT, false),
        (r#"{"tag":"tuple","fields":[]}"#, false),
        (r#"{"tag":"tuple","fields":[{"tag":"bit"}]}"#, false),
        (
            r#"{"tag":"tuple","fields":[{"tag":"unit"},{"tag":"bit"}]}"#,
            false,
        ),
    ] {
        std::fs::write(&req, request(shape, "permutation", "[0,1]")).unwrap();
        let result = Command::new(env!("CARGO_BIN_EXE_qleisli"))
            .arg("verify-ir")
            .arg(&path)
            .arg(format!("--against={}", req.display()))
            .arg("--format=json")
            .output()
            .unwrap();
        assert_eq!(result.status.success(), accepted, "{shape}: {result:?}");
    }
    // Mutating the artifact's own type cannot inherit the original request.
    let changed = interchange::export(
        &verify(identity()).unwrap(),
        Some(&interface(BasisType::pair(
            BasisType::pair(BasisType::Unit, BasisType::Bit),
            BasisType::Unit,
        ))),
        Version::V2,
    )
    .unwrap();
    assert_ne!(bytes, changed);
    assert_eq!(
        interchange::import(
            &changed,
            Some(&request(FLAT_UNIT_BIT_UNIT, "permutation", "[0,1]"))
        )
        .unwrap_err()
        .code,
        "contract"
    );
}

#[test]
fn matching_types_are_required_independently_of_width_and_operator() {
    let program = verify(identity()).unwrap();
    for version in [Version::V1, Version::V2] {
        for (ty, matching, others) in [
            (BasisType::Bit, BIT, [UNIT_BIT, BIT_UNIT]),
            (
                BasisType::pair(BasisType::Unit, BasisType::Bit),
                UNIT_BIT,
                [BIT, BIT_UNIT],
            ),
            (
                BasisType::Tuple(vec![BasisType::Unit, BasisType::Bit, BasisType::Unit]),
                FLAT_UNIT_BIT_UNIT,
                [NESTED_UNIT_BIT_UNIT, BIT],
            ),
        ] {
            let types = interface(ty);
            let bytes = interchange::export(&program, Some(&types), version).unwrap();
            let result =
                interchange::import(&bytes, Some(&request(matching, "permutation", "[0,1]")))
                    .unwrap();
            assert!(result.request_checked);
            assert_eq!(result.root_interface, Some(types.clone()));
            for wrong in others {
                assert_eq!(
                    interchange::import(&bytes, Some(&request(wrong, "permutation", "[0,1]")))
                        .unwrap_err()
                        .code,
                    "contract"
                );
            }
            assert_eq!(
                interchange::import(&bytes, Some(&request(matching, "phase8", "[0,1]")))
                    .unwrap_err()
                    .code,
                "contract"
            );
            let converted = interchange::convert(
                &bytes,
                if version == Version::V1 {
                    Version::V2
                } else {
                    Version::V1
                },
            )
            .unwrap();
            assert_eq!(
                interchange::import(&converted, None)
                    .unwrap()
                    .root_interface,
                Some(types)
            );
        }
        let bytes = interchange::export(&program, None, version).unwrap();
        assert!(!interchange::import(&bytes, None).unwrap().request_checked);
        assert_eq!(
            interchange::import(&bytes, Some(&request(BIT, "permutation", "[0,1]")))
                .unwrap_err()
                .code,
            "contract"
        );
    }
}

fn shared_meaning() -> (VerifiedProgram, MeaningEvidence) {
    let target = FiniteMeaning::phase(BasisType::Bit, vec![0, 1]).unwrap();
    let evidence = MeaningEvidence::check(
        target.target_ir().unwrap(),
        target,
        FunctionIdentity {
            implementation: "impl".into(),
            specification: "pi/4 phase".into(),
            sources: vec![(
                "/not/a/file/../input.qli".into(),
                "not executable source 🦀".into(),
            )],
        },
        &mut Budget::new(DEFAULT_EXACT_WORK),
    )
    .unwrap();
    let mut raw = identity();
    raw.operations = vec![RawOp::ApplyUnitary {
        input: TokenId(0),
        output: TokenId(1),
        steps: vec![
            CircuitStep {
                controls: vec![],
                action: CircuitAction::Contract {
                    indices: vec![0],
                    evidence: evidence.receipt(),
                    adjoint: false,
                },
            },
            CircuitStep {
                controls: vec![],
                action: CircuitAction::Contract {
                    indices: vec![0],
                    evidence: evidence.receipt(),
                    adjoint: true,
                },
            },
        ],
    }];
    raw.quantum_outputs = vec![TokenId(1)];
    (verify(raw).unwrap(), evidence)
}

#[test]
fn shared_receipts_are_rebuilt_once_and_meaning_tags_have_checked_migration() {
    let (program, evidence) = shared_meaning();
    let types = interface(BasisType::Bit);
    let bytes = interchange::export_with_meanings(&program, Some(&types), &[evidence]).unwrap();
    let text = std::str::from_utf8(&bytes).unwrap();
    assert_eq!(text.matches(r#""tag":"meaning""#).count(), 1);
    let imported =
        interchange::import(&bytes, Some(&request(BIT, "permutation", "[0,1]"))).unwrap();
    let RawOp::ApplyUnitary { steps, .. } = &imported.program.raw().operations[0] else {
        panic!()
    };
    let CircuitAction::Contract { evidence: a, .. } = &steps[0].action else {
        panic!()
    };
    let CircuitAction::Contract { evidence: b, .. } = &steps[1].action else {
        panic!()
    };
    assert!(std::sync::Arc::ptr_eq(a, b));
    assert_eq!(
        interchange::convert(&bytes, Version::V1).unwrap_err().code,
        "unsupported"
    );
    let tampered = text.replacen(r#""table":[0,1]"#, r#""table":[0,2]"#, 1);
    assert_eq!(
        interchange::import(tampered.as_bytes(), None)
            .unwrap_err()
            .code,
        "contract"
    );
    let snapshot = request(BIT, "permutation", "[0,1]");
    let snapshot=String::from_utf8(snapshot).unwrap().replace("\"source_snapshot\":null",r#""source_snapshot":[{"path":"/not/a/file/../input.qli","text":"not executable source 🦀"}]"#);
    interchange::import(&bytes, Some(snapshot.as_bytes())).unwrap();
    let changed = text.replace("not executable source 🦀", "changed source");
    assert_eq!(
        interchange::import(changed.as_bytes(), Some(snapshot.as_bytes()))
            .unwrap_err()
            .code,
        "contract"
    );
    // Metadata is not a claim that Rust lowering preserves the source meaning.
    interchange::import(changed.as_bytes(), None).unwrap();
}

#[test]
fn portable_artifacts_run_in_fresh_processes_after_source_removal() {
    let root = SourceRoot::new("observe fn main() -> CBit { true }");
    let path = root.0.join("artifact 日本語.json");
    let emit = || {
        Command::new(env!("CARGO_BIN_EXE_qleisli"))
            .arg("emit-ir")
            .arg(&root.0)
            .arg(format!("--output={}", path.display()))
            .arg("--format=json")
            .output()
            .unwrap()
    };
    let first = emit();
    assert!(first.status.success(), "{first:?}");
    assert!(first.stderr.is_empty());
    let bytes = std::fs::read(&path).unwrap();
    let again = emit();
    assert_eq!(again.status.code(), Some(1));
    assert_eq!(std::fs::read(&path).unwrap(), bytes);
    assert!(std::fs::read_dir(&root.0).unwrap().all(|e| {
        !e.unwrap()
            .file_name()
            .to_string_lossy()
            .starts_with(".qleisli-ir-")
    }));
    std::fs::remove_file(root.0.join("main.qli")).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_qleisli"))
        .arg("verify-ir")
        .arg(&path)
        .arg("--format=json")
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    assert!(output.stderr.is_empty());
    assert!(
        String::from_utf8(output.stdout)
            .unwrap()
            .contains(r#""request_checked":false"#)
    );
    let typed = interchange::export(
        &verify(identity()).unwrap(),
        Some(&interface(BasisType::Bit)),
        Version::V1,
    )
    .unwrap();
    std::fs::write(&path, typed).unwrap();
    let req = root.0.join("request.json");
    for (ty, status) in [(BIT, 0), (UNIT_BIT, 1), (BIT_UNIT, 1)] {
        std::fs::write(&req, request(ty, "permutation", "[0,1]")).unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_qleisli"))
            .arg("verify-ir")
            .arg(&path)
            .arg(format!("--against={}", req.display()))
            .arg("--format=json")
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(status), "{output:?}");
        assert!(output.stderr.is_empty());
        if status == 1 {
            assert!(
                String::from_utf8(output.stdout)
                    .unwrap()
                    .contains("json_pointer:")
            );
        }
    }
}

#[test]
fn fixed_size_algorithm_and_feedback_artifacts_preserve_distributions() {
    use qleisli::sim::{SimulationLimits, run_closed};
    for example in [
        "bell",
        "feedback",
        "function_contracts",
        "operation_contracts",
        "phase_oracle",
        "phase_estimation",
        "iterative_phase_estimation",
        "grover",
        "order_finding",
        "bit_flip_code",
        "semantic_contracts",
    ] {
        let program = compile_project(
            &std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("examples")
                .join(example),
        )
        .unwrap();
        let expected = run_closed(&program, SimulationLimits::default()).unwrap();
        for version in [Version::V1, Version::V2] {
            let bytes = interchange::export(&program, None, version)
                .unwrap_or_else(|e| panic!("{example}: {e}"));
            let imported = interchange::import(&bytes, None).unwrap();
            let actual = run_closed(&imported.program, SimulationLimits::default()).unwrap();
            assert_eq!(actual, expected, "{example}");
        }
    }
}

#[test]
fn malformed_transport_and_declared_root_bindings_are_rejected() {
    let bytes = interchange::export(
        &verify(identity()).unwrap(),
        Some(&interface(BasisType::Bit)),
        Version::V1,
    )
    .unwrap();
    let text = std::str::from_utf8(&bytes).unwrap();
    for (from, to) in [
        (r#""version":1"#, r#""version":3"#),
        (r#""root":0"#, r#""root":1"#),
        (r#""root":0"#, r#""root":0,"root":0"#),
        (r#""root":0"#, r#""root":0.0"#),
        (r#""root":0"#, r#""root":0e0"#),
        (r#""root":0"#, r#""root":-1"#),
        (r#""root":0"#, r#""root":4294967296"#),
        (r#""root":0"#, r#""root":0,"verified":true"#),
        (r#""quantum_outputs":[0]"#, r#""quantum_outputs":[1]"#),
    ] {
        assert!(text.contains(from));
        assert!(
            interchange::import(text.replacen(from, to, 1).as_bytes(), None).is_err(),
            "{to}"
        );
    }
    let wrong = RootInterface {
        input: BasisType::Bit,
        output: BasisType::pair(BasisType::Bit, BasisType::Bit),
    };
    assert_eq!(
        interchange::export(&verify(identity()).unwrap(), Some(&wrong), Version::V2)
            .unwrap_err()
            .code,
        "invalid_ir"
    );
    assert_eq!(
        interchange::import(&vec![b' '; (16 << 20) + 1], None)
            .unwrap_err()
            .code,
        "limit"
    );
    assert_eq!(
        interchange::import("[".repeat(10_000).as_bytes(), None)
            .unwrap_err()
            .code,
        "limit"
    );
    assert!(interchange::import(&[0xff], None).is_err());
}
