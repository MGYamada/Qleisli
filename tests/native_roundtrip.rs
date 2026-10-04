//! Accepted-view correspondence after the v0.2.9 Lean-only cutover.
//!
//! Rust decodes the exact bytes Lean accepted into an execution view. These
//! tests check two properties of that untrusted view, without adding authority:
//! (1) it re-encodes to the same proposal, so no field is dropped or normalized;
//! (2) every evidence receipt's cached execution matrix, which Rust computes
//! from the specification, equals the exact matrix of the implementation
//! circuit that Lean actually compared against the specification.
//! QIRF2 `meaning` entries are built explicitly because neither the retained
//! 799-pair comparison inputs nor the compiled corpus contain one.
// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

use qleisli::AcceptedProgram;
use qleisli::contract::exact::Budget;
use qleisli::contract::meaning::{FiniteMeaning, MeaningEvidence};
use qleisli::contract::{BasisType, DEFAULT_EXACT_WORK, FunctionEvidence, FunctionIdentity};
use qleisli::interchange::native::{Kernel, Proposal};
use qleisli::interchange::{Version, export_with_meanings};
use qleisli::ir::{
    BasisShape, BitControl, CircuitAction, CircuitStep, Effect, QuantumPort, RawOp, RawProgram,
    SingleGate, TokenId, WireId,
};
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::sync::Arc;

fn kernel() -> Kernel {
    Kernel::selected().expect("set QLEISLI_KERNEL to the matching native checker")
}

/// Every receipt reachable from a program, including nested receipts used by
/// implementations and specifications. Shared receipts are visited once.
fn receipts(program: &RawProgram) -> Vec<Arc<FunctionEvidence>> {
    fn steps(steps: &[CircuitStep], out: &mut Vec<Arc<FunctionEvidence>>) {
        for step in steps {
            if let CircuitAction::Contract { evidence, .. } = &step.action {
                out.push(Arc::clone(evidence));
            }
        }
    }
    fn ops(list: &[RawOp], out: &mut Vec<Arc<FunctionEvidence>>) {
        for op in list {
            match op {
                RawOp::ApplyUnitary { steps: s, .. } => steps(s, out),
                RawOp::CertifiedCompute {
                    use_steps,
                    logical_steps,
                    ..
                } => {
                    steps(use_steps, out);
                    steps(logical_steps, out);
                }
                RawOp::ClassicalBranch {
                    then_ops, else_ops, ..
                } => {
                    ops(then_ops, out);
                    ops(else_ops, out);
                }
                _ => {}
            }
        }
    }
    let (mut seen, mut found, mut pending) = (BTreeSet::new(), Vec::new(), Vec::new());
    ops(&program.operations, &mut pending);
    while let Some(receipt) = pending.pop() {
        if seen.insert(Arc::as_ptr(&receipt) as usize) {
            ops(&receipt.implementation().operations, &mut pending);
            ops(&receipt.specification().operations, &mut pending);
            found.push(receipt);
        }
    }
    found
}

/// The execution cache must agree with the implementation Lean checked.
fn assert_cache_matches_implementation(program: &AcceptedProgram, context: &str) -> usize {
    let found = receipts(program.raw());
    for receipt in &found {
        let mut budget = Budget::new(DEFAULT_EXACT_WORK);
        let implementation = receipt.circuit().matrix(&mut budget).unwrap();
        assert_eq!(
            &implementation,
            receipt.meaning(),
            "{context}: cached execution matrix differs from the implementation"
        );
    }
    found.len()
}

fn encode(program: &AcceptedProgram) -> Vec<u8> {
    Proposal::from_raw(program.raw(), program.root_interface(), Version::V2, None)
        .unwrap()
        .artifact()
        .to_vec()
}

fn projects(root: &Path, out: &mut Vec<PathBuf>) {
    let mut entries: Vec<_> = std::fs::read_dir(root)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .collect();
    entries.sort();
    for path in entries {
        let name = path.file_name().unwrap().to_string_lossy().into_owned();
        if !path.is_dir()
            || [
                "authoring",
                "negative",
                "semantic_faults",
                "upstream",
                "sized",
            ]
            .contains(&name.as_str())
        {
            continue;
        }
        if path.join("main.qli").is_file() {
            out.push(path);
        } else {
            projects(&path, out);
        }
    }
}

#[test]
fn compiled_programs_reencode_exactly_and_caches_match_implementations() {
    let kernel = kernel();
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut roots = Vec::new();
    projects(&manifest.join("examples"), &mut roots);
    projects(&manifest.join("corpus"), &mut roots);
    assert!(
        roots.len() >= 100,
        "project discovery found {}",
        roots.len()
    );
    let mut evidence = 0;
    for root in &roots {
        let context = root.display().to_string();
        let compiled = qleisli::frontend::compile::compile_project(root).unwrap();
        let first = encode(&compiled);
        let checked = kernel.check(&first, None).unwrap();
        assert_eq!(
            first,
            encode(checked.program()),
            "{context}: decode/encode changed the proposal"
        );
        evidence += assert_cache_matches_implementation(checked.program(), &context);
    }
    // Coverage guard: the examples currently produce five receipts and the
    // corpus none. A drop means this test stopped exercising evidence at all.
    assert!(
        evidence >= 5,
        "only {evidence} evidence receipts were exercised"
    );
}

fn port(bits: usize) -> QuantumPort {
    QuantumPort {
        token: TokenId(0),
        wires: (0..bits as u32).map(WireId).collect(),
        shape: BasisShape { bits: bits as u8 },
    }
}

fn gates(sequence: &[SingleGate]) -> RawProgram {
    let operations = sequence
        .iter()
        .enumerate()
        .map(|(i, &gate)| RawOp::Gate {
            gate,
            input: TokenId(i as u32),
            output: TokenId(i as u32 + 1),
        })
        .collect();
    RawProgram {
        quantum_inputs: vec![port(1)],
        classical_inputs: vec![],
        operations,
        quantum_outputs: vec![TokenId(sequence.len() as u32)],
        classical_outputs: vec![],
        declared_effect: Effect::Unitary,
    }
}

fn circuit(bits: usize, steps: Vec<CircuitStep>) -> RawProgram {
    RawProgram {
        quantum_inputs: vec![port(bits)],
        classical_inputs: vec![],
        operations: vec![RawOp::ApplyUnitary {
            input: TokenId(0),
            output: TokenId(1),
            steps,
        }],
        quantum_outputs: vec![TokenId(1)],
        classical_outputs: vec![],
        declared_effect: Effect::Unitary,
    }
}

/// A one-bit monomial on axis 1, enabled by axis 0 (the low bit).
fn low_controlled(permutation: Vec<u16>, phases: Vec<u8>) -> CircuitStep {
    CircuitStep {
        controls: vec![BitControl {
            index: 0,
            when_one: true,
        }],
        action: CircuitAction::Monomial {
            indices: vec![1],
            permutation,
            phases,
        },
    }
}

fn identity() -> FunctionIdentity {
    FunctionIdentity {
        implementation: "independent provider".into(),
        specification: "finite table".into(),
        sources: vec![("provider".into(), "immutable source".into())],
    }
}

#[test]
fn qirf2_meaning_entries_execute_the_checked_table() {
    use SingleGate::{H, T, X, Z};
    let kernel = kernel();
    let bit = || BasisType::Bit;
    let pair = || BasisType::pair(BasisType::Bit, BasisType::Bit);
    // Implementations deliberately differ in shape from the table they claim.
    let cases = [
        ("T", gates(&[T]), FiniteMeaning::phase(bit(), vec![0, 1])),
        (
            "S = T T",
            gates(&[T, T]),
            FiniteMeaning::phase(bit(), vec![0, 2]),
        ),
        ("Z", gates(&[Z]), FiniteMeaning::phase(bit(), vec![0, 4])),
        (
            "X = H Z H",
            gates(&[H, Z, H]),
            FiniteMeaning::permutation(bit(), vec![1, 0]),
        ),
        (
            "X",
            gates(&[X]),
            FiniteMeaning::permutation(bit(), vec![1, 0]),
        ),
        (
            "CNOT (low control)",
            circuit(2, vec![low_controlled(vec![1, 0], vec![0, 0])]),
            FiniteMeaning::permutation(pair(), vec![0, 3, 2, 1]),
        ),
        (
            "CZ",
            circuit(2, vec![low_controlled(vec![0, 1], vec![0, 4])]),
            FiniteMeaning::phase(pair(), vec![0, 0, 0, 4]),
        ),
    ];
    for (name, implementation, target) in cases {
        let target = target.unwrap();
        let bits = target.signature().bits().unwrap();
        let mut budget = Budget::new(DEFAULT_EXACT_WORK);
        let evidence = MeaningEvidence::check(implementation, target, identity(), &mut budget)
            .unwrap_or_else(|e| panic!("{name}: {e:?}"));
        let caller = circuit(
            bits,
            vec![CircuitStep {
                controls: vec![],
                action: CircuitAction::Contract {
                    indices: (0..bits).collect(),
                    evidence: evidence.receipt(),
                    adjoint: false,
                },
            }],
        );
        let accepted = kernel.accept_raw(caller).unwrap();
        let bytes = export_with_meanings(&accepted, None, std::slice::from_ref(&evidence)).unwrap();
        let text = String::from_utf8(bytes.clone()).unwrap();
        assert!(
            text.contains("\"tag\":\"meaning\""),
            "{name}: no QIRF2 meaning entry"
        );

        let checked = kernel.check(&bytes, None).unwrap();
        assert_eq!(
            assert_cache_matches_implementation(checked.program(), name),
            1
        );

        // The decoded view does not retain the table: plain re-encoding turns
        // the meaning entry into a circuit entry, which Lean accepts again.
        let plain = encode(checked.program());
        assert!(
            !String::from_utf8(plain.clone())
                .unwrap()
                .contains("\"tag\":\"meaning\"")
        );
        kernel.check(&plain, None).unwrap();
        // Supplying the same table again restores the original bytes exactly.
        let restored =
            export_with_meanings(checked.program(), None, std::slice::from_ref(&evidence)).unwrap();
        assert_eq!(
            restored, bytes,
            "{name}: meaning round trip changed the artifact"
        );
    }
}

#[test]
fn a_wrong_table_is_rejected_before_any_receipt_exists() {
    let mut budget = Budget::new(DEFAULT_EXACT_WORK);
    // T claims the S table: the exact global/relative phase must be checked.
    let wrong = FiniteMeaning::phase(BasisType::Bit, vec![0, 2]).unwrap();
    assert!(
        MeaningEvidence::check(gates(&[SingleGate::T]), wrong, identity(), &mut budget).is_err()
    );
    // CNOT with the control on the high bit is a different permutation.
    let high = FiniteMeaning::permutation(
        BasisType::pair(BasisType::Bit, BasisType::Bit),
        vec![0, 1, 3, 2],
    )
    .unwrap();
    let low = circuit(2, vec![low_controlled(vec![1, 0], vec![0, 0])]);
    assert!(MeaningEvidence::check(low, high, identity(), &mut budget).is_err());
}
