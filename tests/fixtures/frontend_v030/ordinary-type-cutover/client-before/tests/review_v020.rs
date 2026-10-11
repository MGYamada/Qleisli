//! Reproductions from the user-supplied 0.2.0 review, repaired in 0.2.1.
mod common;
use common::SourceRoot;
use common::accept;
use qleisli::frontend::compile::{ErrorCode, check_project, compile_project};
use qleisli::interchange::{self, Version};
use qleisli::ir::*;
use qleisli::sim::{SampleError, SampleLimits, sample_closed};
use std::path::Path;
use std::process::Command;

#[test]
#[ignore = "historical large Rust trajectory; maximum-size runs are deferred during native cutover"]
fn long_source_trajectory_samples_with_the_original_cli_budget() {
    let output = Command::new(env!("CARGO_BIN_EXE_qleisli"))
        .args([
            "sample",
            "tests/fixtures/review_v020/long_trajectory",
            "--shots=3",
            "--seed=0",
            "--format=json",
        ])
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    let json = String::from_utf8(output.stdout).unwrap();
    assert_eq!(json.matches("\"bits\":[false]").count(), 3, "{json}");
}

#[test]
#[ignore = "historical large Rust trajectory; maximum-size runs are deferred during native cutover"]
fn long_identity_circuits_normalize_both_flat_and_compound_steps() {
    const GATES: u32 = 12_000;
    for compound in [false, true] {
        let mut operations = vec![RawOp::Init0 {
            output: TokenId(0),
            wire: WireId(0),
        }];
        let output = if compound {
            operations.push(RawOp::ApplyUnitary {
                input: TokenId(0),
                output: TokenId(1),
                steps: (0..GATES)
                    .map(|_| CircuitStep {
                        controls: vec![],
                        action: CircuitAction::Hadamard { target: 0 },
                    })
                    .collect(),
            });
            TokenId(1)
        } else {
            operations.extend((0..GATES).map(|i| RawOp::Gate {
                gate: SingleGate::H,
                input: TokenId(i),
                output: TokenId(i + 1),
            }));
            TokenId(GATES)
        };
        operations.push(RawOp::MeasureZ {
            input: output,
            output: ClassicalId(0),
        });
        let program = accept(RawProgram {
            quantum_inputs: vec![],
            classical_inputs: vec![],
            operations,
            quantum_outputs: vec![],
            classical_outputs: vec![ClassicalId(0)],
            declared_effect: Effect::Observe,
        })
        .unwrap();
        let mut draws = 0;
        let mut rng = || {
            draws += 1;
            Ok::<_, ()>(0)
        };
        let sample = sample_closed(&program, &mut rng, SampleLimits::default()).unwrap();
        // H^(2k) is the identity, independently of numerical execution.
        assert_eq!(sample.bits, vec![false]);
        assert_eq!(
            sample.execution_steps,
            u64::from(GATES) + 2 + u64::from(compound)
        );
        assert!(matches!(
            sample_closed(
                &program,
                &mut rng,
                SampleLimits {
                    max_execution_steps: GATES as usize,
                    ..SampleLimits::default()
                }
            ),
            Err(SampleError::Limit(_))
        ));
        assert_eq!(draws, 1); // Renormalization consumes no random words.
    }
}

#[test]
#[ignore = "historical many-receipt/300KB stress exceeds aggregate fresh-native work; batching is tracked in #274"]
fn many_receipts_round_trip_shared_source_without_repeated_storage_work() {
    let original = include_str!("fixtures/review_v020/shared_identities/main.qli");
    for extra in [0, 300_000] {
        let root = SourceRoot::new(&format!("{original}\n/*{}*/", "p".repeat(extra)));
        let program = compile_project(&root.0).unwrap();
        for version in [Version::V1, Version::V2] {
            let bytes = interchange::export(&program, None, version).unwrap();
            let imported = interchange::import(&bytes, None).unwrap();
            // Native work is charged for the complete original graph; source storage remains shared.
            assert!(
                imported.exact_work <= qleisli::contract::DEFAULT_EXACT_WORK,
                "{}",
                imported.exact_work
            );
            assert_eq!(
                interchange::export(&imported.program, None, version).unwrap(),
                bytes
            );
        }
        let artifact = root.0.join("artifact.json");
        let emitted = Command::new(env!("CARGO_BIN_EXE_qleisli"))
            .arg("emit-ir")
            .arg(&root.0)
            .arg(format!("--output={}", artifact.display()))
            .output()
            .unwrap();
        assert!(emitted.status.success(), "{emitted:?}");
        let verified = Command::new(env!("CARGO_BIN_EXE_qleisli"))
            .arg("verify-ir")
            .arg(&artifact)
            .output()
            .unwrap();
        assert!(verified.status.success(), "{verified:?}");
    }
}

#[test]
fn small_native_receipts_round_trip_shared_source() {
    let source = "use std::quantum::init0; use std::observe::measure_z;
        unitary fn actual(q:Q<Bit>)->Q<Bit>{q}
        unitary fn specified(q:Q<Bit>)->Q<Bit>{q}
        observe fn main()->CBit{
            let q=init0();
            let q=apply_contract(actual,specified,q);
            let q=apply_contract(actual,specified,q);
            measure_z(q)}";
    let root = SourceRoot::new(&format!("{source}\n/*{}*/", "p".repeat(20_000)));
    let program = compile_project(&root.0).unwrap();
    for version in [Version::V1, Version::V2] {
        let bytes = interchange::export(&program, None, version).unwrap();
        let imported = interchange::import(&bytes, None).unwrap();
        assert_eq!(
            interchange::export(&imported.program, None, version).unwrap(),
            bytes
        );
        let artifact = root.0.join("small-native.qirf");
        std::fs::write(&artifact, &bytes).unwrap();
        let verified = Command::new(env!("CARGO_BIN_EXE_qleisli"))
            .arg("verify-ir")
            .arg(&artifact)
            .output()
            .unwrap();
        assert!(verified.status.success(), "{verified:?}");
    }
}

#[test]
fn usage_in_both_formats_lists_every_command_and_option() {
    for args in [vec![], vec!["--format=json"]] {
        let output = Command::new(env!("CARGO_BIN_EXE_qleisli"))
            .args(&args)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(2));
        let text = String::from_utf8(if args.is_empty() {
            output.stderr
        } else {
            output.stdout
        })
        .unwrap();
        for required in [
            "check",
            "run",
            "sample",
            "emit-ir",
            "verify-ir",
            "doc",
            "--shots=",
            "--seed=",
            "--output=",
            "--against=",
            "--format=json",
            "--source-bytes=",
            "--project-bytes=",
            "--legacy-source-limits",
        ] {
            assert!(text.contains(required), "missing {required}: {text}");
        }
    }
}

#[test]
#[ignore = "historical large expansion exceeds native time/work bounds before the former Rust diagnostic"]
fn capacity_diagnostics_identify_the_declaration_and_exact_arithmetic_limit() {
    let root = Path::new("tests/fixtures/review_v020");
    let error = check_project(&root.join("expansion_limit")).unwrap_err();
    assert_eq!(error.code, ErrorCode::Limit);
    assert!(
        error.message.contains("project-wide work limit of 1000000"),
        "{error}"
    );
    assert!(
        error.message.contains("while checking main::main"),
        "{error}"
    );
    let source = include_str!("fixtures/review_v020/expansion_limit/main.qli");
    assert!(source[error.span.start..error.span.end].contains("fn main"));
    check_project(&root.join("repeat_300")).unwrap();
    // Historical repeat failure is repaired by structural copy validation.
    check_project(&root.join("repeat_1000")).unwrap();
    let explicit = SourceRoot::new(
        "use std::quantum::{h,t,init0}; use std::observe::measure_z;
         unitary fn ht(q:Q<Bit>)->Q<Bit>{t(h(q))}
         unitary fn long(q:Q<Bit>)->Q<Bit>{repeat_static(512,ht,q)}
         observe fn main()->CBit{measure_z(apply_contract(long,long,init0()))}",
    );
    let error = check_project(&explicit.0).unwrap_err();
    assert_eq!(error.code, ErrorCode::Limit);
    assert!(
        error
            .message
            .contains("exact arithmetic capacity exhausted"),
        "{error}"
    );
    assert!(error.message.contains("no approximate fallback"), "{error}");
}
