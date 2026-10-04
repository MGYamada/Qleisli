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
use qleisli::contract::exact::{Budget, Exact, Matrix};
use qleisli::contract::meaning::{FiniteMeaning, MeaningEvidence};
use qleisli::contract::{BasisType, DEFAULT_EXACT_WORK, FunctionEvidence, FunctionIdentity};
use qleisli::interchange::native::{Kernel, Proposal};
use qleisli::interchange::{Version, export_with_meanings};
use qleisli::ir::{
    BasisShape, BitControl, CircuitAction, CircuitStep, ClassicalId, Effect, QuantumPhi,
    QuantumPort, RawOp, RawProgram, SingleGate, TokenId, WireId,
};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
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

const CORPUS_SOURCES: [&str; 3] = ["quantum_katas", "qualtran", "pennylane_demos"];

fn compiled_projects(manifest: &Path) -> Vec<PathBuf> {
    let mut roots = Vec::new();
    projects(&manifest.join("examples"), &mut roots);
    // Migration and authoring snapshots retain historical source syntax. Only
    // the approved provider roots are current executable corpus projects.
    for source in CORPUS_SOURCES {
        projects(&manifest.join("corpus").join(source), &mut roots);
    }
    roots
}

#[test]
fn compiled_project_discovery_selects_current_sources() {
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    let roots = compiled_projects(manifest);
    let selected: BTreeSet<_> = roots.iter().cloned().collect();
    assert_eq!(selected.len(), roots.len(), "duplicate compiled project");

    // Independently enumerate the current flat provider layout. This guards
    // against excluding active projects while avoiding preserved snapshots.
    let corpus = manifest.join("corpus");
    let mut expected = BTreeSet::new();
    for source in CORPUS_SOURCES {
        let provider: BTreeSet<_> = std::fs::read_dir(corpus.join(source))
            .unwrap()
            .map(|entry| entry.unwrap().path())
            .filter(|path| path.join("main.qli").is_file())
            .collect();
        assert!(!provider.is_empty(), "missing corpus provider {source}");
        expected.extend(provider);
    }
    let actual: BTreeSet<_> = roots
        .iter()
        .filter(|path| path.starts_with(&corpus))
        .cloned()
        .collect();
    assert_eq!(actual, expected, "current corpus discovery changed");

    let mut historical = Vec::new();
    projects(&corpus.join("migrations"), &mut historical);
    assert!(
        !historical.is_empty(),
        "missing migration regression inputs"
    );
    for path in historical {
        assert!(
            !selected.contains(&path),
            "historical project selected for current compilation: {}",
            path.display()
        );
    }
}

#[test]
fn compiled_programs_reencode_exactly_and_caches_match_implementations() {
    let kernel = kernel();
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    let roots = compiled_projects(manifest);
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

/// Count actual receipt edges after native decoding, including both snapshots
/// and both branch arms. A traversal implementation alone is not coverage.
fn receipt_coverage(program: &RawProgram) -> BTreeMap<&'static str, usize> {
    fn steps(
        steps: &[CircuitStep],
        placement: &'static str,
        snapshot: &'static str,
        branch: Option<bool>,
        pending: &mut Vec<Arc<FunctionEvidence>>,
        counts: &mut BTreeMap<&'static str, usize>,
    ) {
        for step in steps {
            if let CircuitAction::Contract { evidence, .. } = &step.action {
                *counts.entry(placement).or_default() += 1;
                if snapshot != "root" {
                    *counts.entry(snapshot).or_default() += 1;
                }
                if let Some(arm) = branch {
                    *counts
                        .entry(if arm { "then_calls" } else { "else_calls" })
                        .or_default() += 1;
                }
                pending.push(Arc::clone(evidence));
            }
        }
    }
    fn ops(
        list: &[RawOp],
        snapshot: &'static str,
        branch: Option<bool>,
        pending: &mut Vec<Arc<FunctionEvidence>>,
        counts: &mut BTreeMap<&'static str, usize>,
    ) {
        for op in list {
            match op {
                RawOp::ApplyUnitary { steps: calls, .. } => {
                    steps(
                        calls,
                        "apply_unitary_calls",
                        snapshot,
                        branch,
                        pending,
                        counts,
                    );
                }
                RawOp::CertifiedCompute {
                    use_steps,
                    logical_steps,
                    ..
                } => {
                    steps(
                        use_steps,
                        "certified_use_calls",
                        snapshot,
                        branch,
                        pending,
                        counts,
                    );
                    steps(
                        logical_steps,
                        "certified_logical_calls",
                        snapshot,
                        branch,
                        pending,
                        counts,
                    );
                }
                RawOp::ClassicalBranch {
                    then_ops, else_ops, ..
                } => {
                    ops(then_ops, snapshot, Some(true), pending, counts);
                    ops(else_ops, snapshot, Some(false), pending, counts);
                }
                _ => {}
            }
        }
    }
    let (mut counts, mut pending, mut seen) = (BTreeMap::new(), Vec::new(), BTreeSet::new());
    ops(&program.operations, "root", None, &mut pending, &mut counts);
    while let Some(receipt) = pending.pop() {
        if seen.insert(Arc::as_ptr(&receipt) as usize) {
            *counts.entry("unique_receipts").or_default() += 1;
            ops(
                &receipt.implementation().operations,
                "implementation_calls",
                None,
                &mut pending,
                &mut counts,
            );
            ops(
                &receipt.specification().operations,
                "specification_calls",
                None,
                &mut pending,
                &mut counts,
            );
        } else {
            *counts.entry("shared_receipts").or_default() += 1;
        }
    }
    counts
}

fn phase_matrix(exponent: i32) -> Matrix {
    Matrix::new(
        2,
        2,
        vec![
            Exact::one(),
            Exact::zero(),
            Exact::zero(),
            Exact::phase(exponent),
        ],
    )
    .unwrap()
}

fn call(receipt: &Arc<FunctionEvidence>) -> CircuitStep {
    CircuitStep {
        controls: vec![],
        action: CircuitAction::Contract {
            indices: vec![0],
            evidence: Arc::clone(receipt),
            adjoint: false,
        },
    }
}

fn named_receipt(
    name: &str,
    implementation: RawProgram,
    specification: RawProgram,
) -> Arc<FunctionEvidence> {
    Arc::new(
        FunctionEvidence::check(
            BasisType::Bit,
            implementation,
            specification,
            FunctionIdentity {
                implementation: name.into(),
                ..identity()
            },
            &mut Budget::new(DEFAULT_EXACT_WORK),
        )
        .unwrap(),
    )
}

fn certified(receipt: &Arc<FunctionEvidence>, output: u32) -> RawOp {
    RawOp::CertifiedCompute {
        source: TokenId(0),
        source_out: TokenId(output),
        ancilla_wires: vec![WireId(1)],
        function: vec![0, 1],
        use_steps: vec![call(receipt)],
        logical_steps: vec![call(receipt)],
    }
}

fn record_case(name: &str, bytes: &[u8], counts: &BTreeMap<&'static str, usize>) {
    // The fixture recorder preserves these exact accepted proposals separately
    // from the immutable 799-pair baseline. The gate itself always runs in CI.
    let mut hex = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        write!(hex, "{byte:02x}").expect("writing to String cannot fail");
    }
    println!("ROUNDTRIP_ARTIFACT\t{name}\t{hex}");
    println!("ROUNDTRIP_COVERAGE\t{name}\t{counts:?}");
}

#[test]
fn positive_evidence_coverage_reaches_every_retained_path() {
    let kernel = kernel();
    let t = named_receipt(
        "coverage:T",
        gates(&[SingleGate::T]),
        FiniteMeaning::phase(BasisType::Bit, vec![0, 1])
            .unwrap()
            .target_ir()
            .unwrap(),
    );
    // Two distinct parents share T; one retains it in the implementation and
    // the other in the specification. The accepted graph must retain both.
    let calls = || circuit(1, vec![call(&t), call(&t)]);
    let s_impl = named_receipt(
        "coverage:S-implementation",
        calls(),
        gates(&[SingleGate::T, SingleGate::T]),
    );
    let s_spec = named_receipt(
        "coverage:S-specification",
        gates(&[SingleGate::T, SingleGate::T]),
        calls(),
    );
    let mut computed = gates(&[]);
    computed.operations = vec![certified(&t, 1)];
    computed.quantum_outputs = vec![TokenId(1)];
    let branch = |condition| RawProgram {
        quantum_inputs: vec![port(1)],
        classical_inputs: vec![],
        operations: vec![
            RawOp::ClassicalConst {
                value: condition,
                output: ClassicalId(0),
            },
            RawOp::ClassicalBranch {
                condition: ClassicalId(0),
                then_ops: vec![RawOp::ApplyUnitary {
                    input: TokenId(0),
                    output: TokenId(1),
                    steps: vec![call(&s_impl)],
                }],
                else_ops: vec![certified(&t, 2)],
                quantum_phis: vec![QuantumPhi {
                    then_token: TokenId(1),
                    else_token: TokenId(2),
                    output: TokenId(3),
                    output_wires: vec![WireId(2)],
                }],
                classical_phis: vec![],
            },
        ],
        quantum_outputs: vec![TokenId(3)],
        classical_outputs: vec![],
        declared_effect: Effect::Unitary,
    };
    let cases = [
        (
            "nested-shared-dag",
            circuit(1, vec![call(&s_impl), call(&s_spec)]),
            4,
            vec![
                "apply_unitary_calls",
                "implementation_calls",
                "specification_calls",
                "shared_receipts",
            ],
        ),
        (
            "certified-use-and-logical",
            computed,
            1,
            vec![
                "certified_use_calls",
                "certified_logical_calls",
                "shared_receipts",
            ],
        ),
        (
            "branch-true",
            branch(true),
            2,
            vec![
                "then_calls",
                "else_calls",
                "implementation_calls",
                "certified_use_calls",
                "certified_logical_calls",
            ],
        ),
        (
            "branch-false",
            branch(false),
            1,
            vec![
                "then_calls",
                "else_calls",
                "implementation_calls",
                "certified_use_calls",
                "certified_logical_calls",
            ],
        ),
    ];
    let mut total = BTreeMap::new();
    for (name, raw, phase, required) in cases {
        let bytes = Proposal::from_raw(&raw, None, Version::V2, None)
            .unwrap()
            .artifact()
            .to_vec();
        let checked = kernel.check(&bytes, None).unwrap();
        assert_eq!(
            bytes,
            encode(checked.program()),
            "{name}: accepted shape or bindings changed"
        );
        let counts = receipt_coverage(checked.program().raw());
        for key in required {
            assert!(
                counts.get(key).copied().unwrap_or(0) > 0,
                "{name}: missing {key}"
            );
        }
        let found = receipts(checked.program().raw());
        assert_eq!(found.len(), counts["unique_receipts"]);
        assert_eq!(
            assert_cache_matches_implementation(checked.program(), name),
            found.len()
        );
        for receipt in found {
            let expected = match receipt.identity().implementation.as_str() {
                "coverage:T" => phase_matrix(1),
                "coverage:S-implementation" | "coverage:S-specification" => phase_matrix(2),
                other => panic!("{name}: unexpected receipt {other}"),
            };
            assert_eq!(
                receipt.meaning(),
                &expected,
                "{name}: independent receipt coefficients"
            );
        }
        // Check the complete decoded root against an independent 2x2 phase
        // table, including the selected branch and cleanup's logical action.
        let meaning = MeaningEvidence::check(
            checked.program().raw().clone(),
            FiniteMeaning::phase(BasisType::Bit, vec![0, phase]).unwrap(),
            identity(),
            &mut Budget::new(DEFAULT_EXACT_WORK),
        )
        .unwrap();
        assert_eq!(
            meaning
                .receipt()
                .circuit()
                .matrix(&mut Budget::new(DEFAULT_EXACT_WORK))
                .unwrap(),
            phase_matrix(i32::from(phase))
        );
        for (&key, &count) in &counts {
            *total.entry(key).or_insert(0) += count;
        }
        record_case(name, &bytes, &counts);
    }
    assert_eq!(
        total["unique_receipts"], 8,
        "positive evidence coverage shrank"
    );
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
    let mut covered = 0;
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
        record_case(
            &format!("meaning/{name}"),
            &bytes,
            &receipt_coverage(checked.program().raw()),
        );
        covered += 1;
    }
    assert_eq!(covered, 7, "positive meaning coverage shrank");
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
