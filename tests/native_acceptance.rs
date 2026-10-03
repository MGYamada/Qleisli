//! The first #276 vertical slice starts with the Bell .qli quickstart's raw
//! meaning and a feed-forward variant. Expected distributions are independent
//! of both verifiers; no legacy AcceptedProgram is constructed in these tests.
// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
use qleisli::interchange::Version;
use qleisli::interchange::native::{Kernel, Proposal};
use qleisli::ir::{
    ClassicalId, Effect, QuantumPhi, RawOp, RawProgram, SingleGate, TokenId, WireId,
};
use qleisli::sim::{self, SampleLimits, SimulationLimits, SplitMix64};

fn bell(feed_forward: bool) -> RawProgram {
    let mut operations = vec![
        RawOp::Init0 {
            output: TokenId(0),
            wire: WireId(11),
        },
        RawOp::Init0 {
            output: TokenId(1),
            wire: WireId(7),
        },
        RawOp::Gate {
            gate: SingleGate::H,
            input: TokenId(0),
            output: TokenId(2),
        },
        RawOp::Cnot {
            control: TokenId(2),
            target: TokenId(1),
            control_out: TokenId(3),
            target_out: TokenId(4),
        },
        RawOp::MeasureZ {
            input: TokenId(3),
            output: ClassicalId(0),
        },
    ];
    let last = if feed_forward {
        operations.push(RawOp::ClassicalBranch {
            condition: ClassicalId(0),
            then_ops: vec![RawOp::Gate {
                gate: SingleGate::X,
                input: TokenId(4),
                output: TokenId(5),
            }],
            else_ops: vec![RawOp::Gate {
                gate: SingleGate::Z,
                input: TokenId(4),
                output: TokenId(6),
            }],
            quantum_phis: vec![QuantumPhi {
                then_token: TokenId(5),
                else_token: TokenId(6),
                output: TokenId(7),
                output_wires: vec![WireId(41)],
            }],
            classical_phis: vec![],
        });
        TokenId(7)
    } else {
        TokenId(4)
    };
    operations.push(RawOp::MeasureZ {
        input: last,
        output: ClassicalId(1),
    });
    RawProgram {
        quantum_inputs: vec![],
        classical_inputs: vec![],
        operations,
        quantum_outputs: vec![],
        classical_outputs: vec![ClassicalId(0), ClassicalId(1)],
        declared_effect: Effect::Observe,
    }
}

fn native() -> Kernel {
    Kernel::new(std::env::var_os("QLEISLI_KERNEL").expect("explicit native checker"))
}

#[test]
fn proposals_are_untrusted_and_owned_and_missing_checkers_reject() {
    let mut artifact = b"not even JSON".to_vec();
    let mut request = b"untrusted request".to_vec();
    let proposal = Proposal::new(&artifact, Some(&request)).unwrap();
    artifact.fill(0);
    request.fill(0);
    assert_eq!(proposal.artifact(), b"not even JSON");
    assert_eq!(proposal.request(), Some(b"untrusted request".as_slice()));
    assert!(Proposal::new(b"", None).is_err());
    assert!(Proposal::new(b"{}", Some(b"")).is_err());
    let kernel = Kernel::new("/missing-explicit-native-kernel");
    assert_eq!(kernel.accept(&proposal).unwrap_err().code, "io");
    let mut raw = bell(false);
    raw.operations.push(RawOp::Discard { input: TokenId(3) });
    // Serialization grants nothing, including for consumed-owner misuse.
    let proposal = Proposal::from_raw(&raw, None, Version::V2, None).unwrap();
    assert_eq!(kernel.accept(&proposal).unwrap_err().code, "io");
}

#[test]
#[ignore = "requires the freshly built native Lean checker"]
fn native_handles_execute_bell_and_feedback_without_legacy_receipts() {
    let kernel = native();
    for version in [Version::V1, Version::V2] {
        for feedback in [false, true] {
            let mut raw = bell(feedback);
            let proposal = Proposal::from_raw(&raw, None, version, None).unwrap();
            let accepted = kernel.accept(&proposal).unwrap();
            assert_eq!(accepted.artifact(), proposal.artifact());
            assert_eq!(accepted.raw(), &raw);
            assert!(accepted.checker().is_absolute());
            raw.operations.clear();
            let distribution = sim::run_closed(&accepted, SimulationLimits::default()).unwrap();
            let mut nonzero = 0;
            for (bits, probability) in distribution {
                if probability > 1e-12 {
                    nonzero += 1;
                    assert_eq!(bits[1], if feedback { false } else { bits[0] });
                    assert!((probability - 0.5).abs() < 1e-12);
                }
            }
            assert_eq!(nonzero, 2);
            let mut rng = SplitMix64::new(2903102026);
            let mut seen = [false; 2];
            for _ in 0..32 {
                let sample =
                    sim::sample_closed(&accepted, &mut rng, SampleLimits::default()).unwrap();
                assert_eq!(
                    sample.bits[1],
                    if feedback { false } else { sample.bits[0] }
                );
                seen[usize::from(sample.bits[0])] = true;
            }
            assert_eq!(seen, [true, true]);
            assert!(
                sim::run_closed(
                    &accepted,
                    SimulationLimits {
                        max_execution_steps: 0,
                        ..SimulationLimits::default()
                    }
                )
                .is_err()
            );
        }
    }
}

#[test]
#[ignore = "requires the freshly built native Lean checker"]
fn native_rejection_and_independent_requests_bind_exact_bytes() {
    let kernel = native();
    let mut raw = bell(false);
    raw.operations.push(RawOp::Discard { input: TokenId(3) });
    let proposal = Proposal::from_raw(&raw, None, Version::V2, None).unwrap();
    assert_eq!(kernel.accept(&proposal).unwrap_err().code, "invalid_ir");
    raw = bell(true);
    if let RawOp::ClassicalBranch { else_ops, .. } = &mut raw.operations[5] {
        else_ops.push(RawOp::Discard { input: TokenId(4) });
    }
    let proposal = Proposal::from_raw(&raw, None, Version::V2, None).unwrap();
    assert!(
        kernel.accept(&proposal).is_err(),
        "both arms must be checked"
    );

    let bytes = include_bytes!("fixtures/verification_v022/finite/t.v2.qirf");
    let request = br#"{"format":"qleisli.request","version":1,"signature":{"tag":"bit"},"meaning":{"tag":"phase8","table":[0,1]},"source_snapshot":null}"#;
    let proposal = Proposal::new(bytes, Some(request)).unwrap();
    let accepted = kernel.accept(&proposal).unwrap();
    assert_eq!(accepted.artifact(), bytes);
    assert_eq!(accepted.request(), Some(request.as_slice()));
    assert!(accepted.root_interface().is_some());
    assert!(accepted.native_exact_work() > 0);
    assert!(
        sim::run_closed(&accepted, SimulationLimits::default()).is_err(),
        "open program"
    );
    let wrong = String::from_utf8(request.to_vec())
        .unwrap()
        .replace("[0,1]", "[0,7]");
    assert_eq!(
        kernel
            .accept(&Proposal::new(bytes, Some(wrong.as_bytes())).unwrap())
            .unwrap_err()
            .code,
        "contract"
    );
    assert!(kernel.accept(&Proposal::new(b"{}", None).unwrap()).is_err());
}

#[test]
#[ignore = "requires the freshly built native Lean checker"]
fn evidence_dags_decode_from_the_native_ticket_and_execute() {
    let bytes = include_bytes!("fixtures/verification_v029/native/t-contract.qirf");
    let kernel = native();
    let accepted = kernel.accept(&Proposal::new(bytes, None).unwrap()).unwrap();
    assert_eq!(accepted.artifact(), bytes);
    assert!(accepted.native_exact_work() > 0);
    let qleisli::ir::RawOp::ApplyUnitary { steps, .. } = &accepted.raw().operations[0] else {
        panic!("call root")
    };
    let qleisli::ir::CircuitAction::Contract { evidence, .. } = &steps[0].action else {
        panic!("native evidence")
    };
    assert_eq!(evidence.meaning().rows(), 2);
    assert_eq!(
        evidence.meaning().entries()[3],
        qleisli::contract::exact::Exact::phase(1)
    );
}
