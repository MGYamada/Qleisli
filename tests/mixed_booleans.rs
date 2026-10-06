//! Independent small-system oracles for mixed Boolean Raw proposals.
//! Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
mod common;

use common::SourceRoot;
use qleisli::contract::exact::{Budget, Exact};
use qleisli::contract::meaning::FiniteMeaning;
use qleisli::contract::{BasisType, DEFAULT_EXACT_WORK, FunctionEvidence, FunctionIdentity};
use qleisli::frontend::compile::compile_project;
use qleisli::frontend::parser::parse_module;
use qleisli::frontend::sized::{ElaboratedProgram, ParsedProgram};
use qleisli::interchange::native::{AcceptedProgram, Kernel};
use qleisli::ir::{Effect, RawOp, SingleGate};
use qleisli::sim::{SimulationError, SimulationLimits, run_closed};
use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

fn source(category: &str, name: &str) -> String {
    std::fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/authoring_sessions/mixed-boolean-v030")
            .join(category)
            .join(name)
            .join("main.qli"),
    )
    .unwrap()
}

fn elaborate(source: &str, entry: &str, naturals: BTreeMap<String, u32>) -> ElaboratedProgram {
    let parsed = ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap();
    let owned = parsed.clone();
    drop(parsed);
    owned
        .instantiate(entry, naturals, BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap()
}

fn accept(graph: &ElaboratedProgram) -> AcceptedProgram {
    let proposal = graph.lower_raw().unwrap();
    assert_eq!(
        proposal.source().instantiation().program().source("main"),
        graph.instantiation().program().source("main")
    );
    let kernel = Kernel::new(std::env::var_os("QLEISLI_KERNEL").expect("explicit native checker"));
    let accepted = kernel.accept(proposal.proposal()).unwrap();
    assert_eq!(accepted.artifact(), proposal.payload());
    proposal.validate_source_steps(&accepted).unwrap();
    accepted
}

fn distribution(program: &AcceptedProgram, expected: &[(&[bool], f64)]) {
    let actual = run_closed(program, SimulationLimits::default()).unwrap();
    assert_eq!(actual.len(), expected.len(), "{actual:?}");
    for (bits, probability) in expected {
        assert!(
            (actual.get(*bits).expect("expected ordered output") - probability).abs() < 1e-12,
            "{bits:?}: {actual:?}"
        );
    }
}

fn both_closed(name: &str, expected: &[(&[bool], f64)]) -> AcceptedProgram {
    let text = source("attempt-01", name);
    let finite = compile_project(&SourceRoot::new(&text).0).unwrap();
    distribution(&finite, expected);
    let graph = elaborate(&text, "main::f", BTreeMap::new());
    let accepted = accept(&graph);
    distribution(&accepted, expected);
    assert!(accepted.raw().quantum_inputs.is_empty());
    assert!(accepted.raw().quantum_outputs.is_empty());
    accepted
}

#[test]
fn eager_zero_and_measurement_retains_actual_quantum_work_before_boolean_use() {
    let accepted = both_closed("eager-zero", &[(&[false], 1.0)]);
    assert_eq!(accepted.derived_effect(), Effect::Observe);
    let operations = &accepted.raw().operations;
    assert_eq!(
        operations
            .iter()
            .filter(|op| matches!(op, RawOp::Init0 { .. }))
            .count(),
        1
    );
    assert_eq!(
        operations
            .iter()
            .filter(|op| matches!(
                op,
                RawOp::Gate {
                    gate: SingleGate::H,
                    ..
                }
            ))
            .count(),
        1
    );
    let measured = operations
        .iter()
        .position(|op| matches!(op, RawOp::MeasureZ { .. }))
        .unwrap();
    let used = operations
        .iter()
        .position(|op| matches!(op, RawOp::ClassicalAnd { .. }))
        .unwrap();
    assert!(measured < used);
    let RawOp::MeasureZ { output, .. } = operations[measured] else {
        unreachable!()
    };
    let RawOp::ClassicalAnd { right, .. } = operations[used] else {
        unreachable!()
    };
    assert_eq!(output, right);
}

#[test]
fn bell_measurements_and_boolean_postprocessing_preserve_correlations_and_order() {
    // Bell outcomes (a,b) are 00/11. The requested output is (a,a XOR b),
    // hence 00/10, not two independent fair bits or a reversed tuple.
    let accepted = both_closed("bell-xor", &[(&[false, false], 0.5), (&[true, false], 0.5)]);
    let operations = &accepted.raw().operations;
    assert_eq!(
        operations
            .iter()
            .filter(|op| matches!(op, RawOp::Cnot { .. }))
            .count(),
        1
    );
    let measured = operations
        .iter()
        .filter_map(|op| match op {
            RawOp::MeasureZ { output, .. } => Some(*output),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(measured.len(), 2);
    let (left, right, output) = operations
        .iter()
        .find_map(|op| match op {
            RawOp::ClassicalXor {
                left,
                right,
                output,
            } => Some((*left, *right, *output)),
            _ => None,
        })
        .unwrap();
    assert_eq!((left, right), (measured[0], measured[1]));
    assert_eq!(accepted.raw().classical_outputs, vec![measured[0], output]);
}

#[test]
fn pending_first_argument_keeps_entangled_owner_during_later_argument_measurement() {
    // keep(q,measure_z(r)) must preserve the pending q owner through the RHS
    // observation. X(q) then makes the measured ordered pair anticorrelated.
    let accepted = both_closed(
        "pending-argument",
        &[(&[true, false], 0.5), (&[false, true], 0.5)],
    );
    let operations = &accepted.raw().operations;
    let (q, r) = operations
        .iter()
        .find_map(|op| match op {
            RawOp::Cnot {
                control_out,
                target_out,
                ..
            } => Some((*control_out, *target_out)),
            _ => None,
        })
        .unwrap();
    let (index, x_input, x_output) = operations
        .iter()
        .enumerate()
        .find_map(|(i, op)| match op {
            RawOp::Gate {
                gate: SingleGate::X,
                input,
                output,
            } => Some((i, *input, *output)),
            _ => None,
        })
        .unwrap();
    let measured = operations
        .iter()
        .enumerate()
        .filter_map(|(i, op)| match op {
            RawOp::MeasureZ { input, output } => Some((i, *input, *output)),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(measured.len(), 2);
    assert!(measured[0].0 < index && index < measured[1].0);
    assert_eq!((measured[0].1, x_input, measured[1].1), (r, q, x_output));
    assert_eq!(
        accepted.raw().classical_outputs,
        vec![measured[1].2, measured[0].2]
    );
}

#[test]
fn repeated_calls_and_static_folds_allocate_fresh_quantum_and_classical_ids() {
    let repeated = both_closed("repeated-helper", &[(&[true, true], 1.0)]);
    assert_eq!(
        repeated
            .raw()
            .classical_outputs
            .iter()
            .collect::<BTreeSet<_>>()
            .len(),
        2
    );
    let initialized = repeated
        .raw()
        .operations
        .iter()
        .filter_map(|op| match op {
            RawOp::Init0 { output, wire } => Some((*output, *wire)),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(initialized.len(), 2);
    assert_ne!(initialized[0].0, initialized[1].0);
    assert_ne!(initialized[0].1, initialized[1].1);

    let text = source("attempt-01", "static-fold");
    for n in 0..=2 {
        let graph = elaborate(&text, "main::f", BTreeMap::from([("n".into(), n)]));
        let accepted = accept(&graph);
        distribution(&accepted, &[(&[n == 1], 1.0)]);
        let wires = accepted
            .raw()
            .operations
            .iter()
            .filter_map(|op| match op {
                RawOp::Init0 { wire, .. } => Some(*wire),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(wires.len(), n as usize);
        assert_eq!(wires.iter().collect::<BTreeSet<_>>().len(), n as usize);
        assert_eq!(
            accepted
                .raw()
                .operations
                .iter()
                .filter(|op| matches!(op, RawOp::MeasureZ { .. }))
                .count(),
            n as usize
        );
        assert_eq!(
            accepted
                .raw()
                .operations
                .iter()
                .filter(|op| matches!(op, RawOp::ClassicalXor { .. }))
                .count(),
            n as usize
        );
    }
}

#[test]
fn ignored_measurement_and_unit_return_keep_observation_before_later_logic() {
    let accepted = both_closed("unit-effect", &[(&[true], 1.0)]);
    assert_eq!(accepted.derived_effect(), Effect::Observe);
    let operations = &accepted.raw().operations;
    let measured = operations
        .iter()
        .position(|op| matches!(op, RawOp::MeasureZ { .. }))
        .unwrap();
    let negated = operations
        .iter()
        .position(|op| matches!(op, RawOp::ClassicalNot { .. }))
        .unwrap();
    assert!(measured < negated);
    let RawOp::MeasureZ { output, .. } = operations[measured] else {
        unreachable!()
    };
    assert!(!accepted.raw().classical_outputs.contains(&output));
    assert!(accepted.raw().quantum_outputs.is_empty());
}

#[test]
fn representable_phases_match_independent_exact_targets_and_interference() {
    for (numerator, denominator, eighths) in [(1, 3, 1), (2, 4, 1), (3, 3, 3), (0, 4, 0)] {
        let text = format!(
            "use std::quantum::phase; pub unitary fn f(q: Q<Bit>) -> Q<Bit> {{ phase[{numerator},{denominator}](q) }}"
        );
        let graph = elaborate(&text, "main::f", BTreeMap::new());
        let definition = &graph.definitions()[graph.root()];
        assert_eq!(definition.steps().len(), 1);
        assert_eq!(
            definition.steps()[0].primitive(),
            Some("std::quantum::phase")
        );
        assert_eq!(
            definition.steps()[0].natural_arguments(),
            &[numerator, denominator]
        );
        let accepted = accept(&graph);
        assert_eq!(accepted.raw().operations.len(), eighths as usize);
        assert!(accepted.raw().operations.iter().all(|op| matches!(
            op,
            RawOp::Gate {
                gate: SingleGate::T,
                ..
            }
        )));

        // The reference is an explicitly requested diagonal mathematical target,
        // not a circuit obtained from either source compiler or the common emitter.
        let expected = FiniteMeaning::phase(BasisType::Bit, vec![0, eighths]).unwrap();
        let evidence = FunctionEvidence::check(
            BasisType::Bit,
            accepted.raw().clone(),
            expected.target_ir().unwrap(),
            FunctionIdentity {
                implementation: "main::f".into(),
                specification: "independent::eighth_turn_diagonal".into(),
                sources: vec![("main".into(), text)],
            },
            &mut Budget::new(DEFAULT_EXACT_WORK),
        )
        .unwrap();
        let actual = evidence
            .circuit()
            .matrix(&mut Budget::new(DEFAULT_EXACT_WORK))
            .unwrap();
        assert_eq!(actual.get(0, 0), Some(Exact::integer(1)));
        assert_eq!(actual.get(0, 1), Some(Exact::integer(0)));
        assert_eq!(actual.get(1, 0), Some(Exact::integer(0)));
        assert_eq!(actual.get(1, 1), Some(Exact::phase(i32::from(eighths))));
        assert!(matches!(
            run_closed(&accepted, SimulationLimits::default()),
            Err(SimulationError::NotClosed("quantum inputs are present"))
        ));
    }

    // The source domain is j < 2^k, independently of whether modular reduction
    // could represent an equal operator. Do not broaden it at the Raw target.
    let invalid =
        "use std::quantum::phase; pub unitary fn f(q: Q<Bit>) -> Q<Bit> { phase[9,3](q) }";
    let error = ParsedProgram::parse(BTreeMap::from([("main".into(), invalid.into())]))
        .unwrap()
        .instantiate("main::f", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap_err();
    assert_eq!(error.code(), "limit", "{error}");
    assert_eq!(error.module(), Some("main"), "{error}");
    assert_eq!(
        &invalid[error.span().start..error.span().end],
        "phase[9,3](q)"
    );

    let expected = [
        (&[false][..], (2.0 + 2.0_f64.sqrt()) / 4.0),
        (&[true][..], (2.0 - 2.0_f64.sqrt()) / 4.0),
    ];
    let finite = compile_project(&SourceRoot::new(&source("controls", "finite-t")).0).unwrap();
    distribution(&finite, &expected);
    let graph = elaborate(
        &source("attempt-01", "exact-phase"),
        "main::main",
        BTreeMap::new(),
    );
    distribution(&accept(&graph), &expected);
}

#[test]
fn unsupported_capabilities_remain_explicit_instead_of_weakening_the_selected_target() {
    for name in ["fine-phase", "packed-bits"] {
        let text = source("counterexamples", name);
        let graph = elaborate(&text, "main::f", BTreeMap::new());
        let error = graph.lower_raw().unwrap_err();
        assert_eq!(error.code(), "unsupported", "{name}: {error}");
        assert_eq!(error.module(), Some("main"), "{name}: {error}");
        assert!(error.span().end > error.span().start, "{name}: {error}");
    }
    // The retained provider source is now supported by the closed-operation
    // adapter. Require native acceptance, independent source replay and its
    // intended observed result instead of the historical target refusal.
    let provider = elaborate(
        &source("counterexamples", "provider"),
        "main::f",
        BTreeMap::new(),
    );
    distribution(&accept(&provider), &[(&[true], 1.0)]);
    let text = source("counterexamples", "runtime-if");
    let program = ParsedProgram::parse(BTreeMap::from([("main".into(), text.clone())])).unwrap();
    assert_eq!(program.source("main"), Some(text.as_str()));
    assert_eq!(program.syntax("main"), Some(&parse_module(&text).unwrap()));
    let error = program
        .instantiate("main::f", BTreeMap::new(), BTreeMap::new())
        .unwrap_err();
    assert_eq!(error.code(), "unsupported");
    assert_eq!(error.module(), Some("main"));
    assert_eq!(
        error.message(),
        "sized preparation profile: unsupported runtime expression"
    );
    assert_eq!(
        &text[error.span().start..error.span().end],
        "if b { 0 } else { 1 }"
    );

    // The old finite endpoint already supports providers and runtime branches;
    // their retained controls must not be reclassified as language-wide errors.
    for (name, expected) in [
        ("provider", vec![(&[true][..], 1.0)]),
        ("runtime-if", vec![(&[false][..], 0.5), (&[true][..], 0.5)]),
    ] {
        let finite = compile_project(&SourceRoot::new(&source("counterexamples", name)).0).unwrap();
        distribution(&finite, &expected);
    }
}
