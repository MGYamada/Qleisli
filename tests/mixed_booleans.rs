//! Independent small-system oracles for mixed Boolean Raw proposals.
//! Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
mod common;

use common::SourceRoot;
use qleisli::contract::exact::{Budget, Exact};
use qleisli::contract::meaning::FiniteMeaning;
use qleisli::contract::{
    BasisType, Circuit, DEFAULT_EXACT_WORK, FunctionEvidence, FunctionIdentity,
};
use qleisli::frontend::compile::compile_project;
use qleisli::frontend::compile::{ElaboratedProgram, ParsedProgram};
use qleisli::frontend::parser::parse_module;
use qleisli::interchange::native::{AcceptedProgram, Kernel};
use qleisli::ir::{
    BasisShape, Effect, QuantumPort, RawOp, RawProgram, SingleGate, TokenId, WireId,
};
use qleisli::sim::{SimulationError, SimulationLimits, run_closed};
use std::collections::{BTreeMap, BTreeSet};

fn source(category: &str, name: &str) -> String {
    common::current_source_text(&format!(
        "tests/fixtures/authoring_sessions/mixed-boolean-v030/{category}/{name}/main.qli"
    ))
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
    for (bits, probability) in expected {
        assert!(
            (actual.get(*bits).expect("expected ordered output") - probability).abs() < 1e-12,
            "{bits:?}: {actual:?}"
        );
    }
    // Ordinary H Z H can leave numerical zero outcomes in the simulator.
    // Check their mass with the same existing tolerance; do not renormalize.
    for (bits, probability) in &actual {
        let requested = expected
            .iter()
            .find(|(outcome, _)| *outcome == bits.as_slice())
            .map_or(0.0, |(_, probability)| *probability);
        assert_eq!(bits.len(), program.raw().classical_outputs.len());
        assert!(probability.is_finite() && *probability >= 0.0);
        assert!((probability - requested).abs() < 1e-12, "{actual:?}");
    }
    assert!((actual.values().sum::<f64>() - 1.0).abs() < 1e-12);
}

fn ordinary_cnot_outputs(program: &AcceptedProgram) -> (TokenId, TokenId) {
    let operations = &program.raw().operations;
    let applications = operations
        .iter()
        .filter_map(|operation| match operation {
            RawOp::ApplyUnitary { output, steps, .. } => Some((*output, steps)),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(applications.len(), 1);
    assert!(!operations.iter().any(|op| matches!(op, RawOp::Cnot { .. })));
    let (output, steps) = applications[0];
    let matrix = Circuit::new(
        BasisType::pair(BasisType::Bit, BasisType::Bit),
        steps.clone(),
    )
    .unwrap()
    .matrix(&mut Budget::new(DEFAULT_EXACT_WORK))
    .unwrap();
    // Independent little-endian |a,b> -> |a,b XOR a>, with exact phase +1.
    for column in 0..4 {
        for row in 0..4 {
            let coefficient = if row == [0, 3, 2, 1][column] {
                Exact::one()
            } else {
                Exact::zero()
            };
            assert_eq!(matrix.get(row, column), Some(coefficient));
        }
    }
    operations
        .iter()
        .find_map(|operation| match operation {
            RawOp::Split {
                input,
                left,
                right,
                left_bits: 1,
            } if *input == output => Some((*left, *right)),
            _ => None,
        })
        .expect("ordinary CNOT returns both ordered owners")
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

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn eager_zero_and_measurement_retains_actual_quantum_work_before_boolean_use() {
    let accepted = both_closed("eager-zero", &[(&[false], 1.0)]);
    assert_eq!(accepted.derived_effect(), Effect::Observe);
    let operations = &accepted.raw().operations;
    assert_eq!(
        operations
            .iter()
            .filter(|op| matches!(op, RawOp::LiftBasis { output_wires, table, .. } if output_wires.len() == 1 && table == &[0]))
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

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn bell_measurements_and_boolean_postprocessing_preserve_correlations_and_order() {
    // Bell outcomes (a,b) are 00/11. The requested output is (a,a XOR b),
    // hence 00/10, not two independent fair bits or a reversed tuple.
    let accepted = both_closed("bell-xor", &[(&[false, false], 0.5), (&[true, false], 0.5)]);
    let operations = &accepted.raw().operations;
    ordinary_cnot_outputs(&accepted);
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

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn pending_first_argument_keeps_entangled_owner_during_later_argument_measurement() {
    // keep(q,measure_z(r)) must preserve the pending q owner through the RHS
    // observation. X(q) then makes the measured ordered pair anticorrelated.
    let accepted = both_closed(
        "pending-argument",
        &[(&[true, false], 0.5), (&[false, true], 0.5)],
    );
    let operations = &accepted.raw().operations;
    let (q, r) = ordinary_cnot_outputs(&accepted);
    let measured = operations
        .iter()
        .enumerate()
        .filter_map(|(i, op)| match op {
            RawOp::MeasureZ { input, output } => Some((i, *input, *output)),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(measured.len(), 2);
    assert_eq!(measured[0].1, r);
    let x_body = &operations[measured[0].0 + 1..measured[1].0];
    assert!(!x_body.is_empty(), "ordinary X must retain actual work");
    let mut live = q;
    for operation in x_body {
        let RawOp::Gate { input, output, .. } = operation else {
            panic!("unexpected operation in ordinary X");
        };
        assert_eq!(*input, live, "the pending first owner must survive the RHS");
        assert_ne!(input, output);
        live = *output;
    }
    assert_eq!(measured[1].1, live);
    // Request the exact X equation for the actual retained gate interval.
    // Source-step replay above and the numerical outcome oracle are separate.
    FunctionEvidence::check(
        BasisType::Bit,
        RawProgram {
            quantum_inputs: vec![QuantumPort {
                token: q,
                wires: vec![WireId(0)],
                shape: BasisShape { bits: 1 },
            }],
            classical_inputs: vec![],
            operations: x_body.to_vec(),
            quantum_outputs: vec![live],
            classical_outputs: vec![],
            declared_effect: Effect::Unitary,
        },
        FiniteMeaning::permutation(BasisType::Bit, vec![1, 0])
            .unwrap()
            .target_ir()
            .unwrap(),
        FunctionIdentity {
            implementation: "retained::pending_x_body".into(),
            specification: "independent |b> -> |b XOR 1>, phase +1".into(),
            sources: vec![],
        },
        &mut Budget::new(DEFAULT_EXACT_WORK),
    )
    .unwrap();
    assert_eq!(
        accepted.raw().classical_outputs,
        vec![measured[1].2, measured[0].2]
    );
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
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
            RawOp::LiftBasis {
                output,
                output_wires,
                table,
                ..
            } if output_wires.len() == 1 && table == &[0] => Some((*output, output_wires[0])),
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
                RawOp::LiftBasis {
                    output_wires,
                    table,
                    ..
                } if output_wires.len() == 1 && table == &[0] => Some(output_wires[0]),
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

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
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

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn representable_phases_match_independent_exact_targets_and_interference() {
    for (numerator, denominator, eighths) in [(1, 3, 1), (2, 4, 1), (3, 3, 3), (0, 4, 0)] {
        let text = format!(
            " pub unitary fn f(q: Q<Bit>) -> Q<Bit> {{ phase[{numerator},{denominator}](q) }}"
        );
        let graph = elaborate(&text, "main::f", BTreeMap::new());
        let definition = &graph.definitions()[graph.root()];
        assert_eq!(definition.steps().len(), 1);
        assert_eq!(definition.steps()[0].primitive(), Some("phase"));
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
    let invalid = " pub unitary fn f(q: Q<Bit>) -> Q<Bit> { phase[9,3](q) }";
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

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn unsupported_capabilities_remain_explicit_instead_of_weakening_the_selected_target() {
    {
        let name = "fine-phase";
        let text = source("counterexamples", name);
        let graph = elaborate(&text, "main::f", BTreeMap::new());
        let error = graph.lower_raw().unwrap_err();
        assert_eq!(error.code(), "unsupported", "{name}: {error}");
        assert_eq!(error.module(), Some("main"), "{name}: {error}");
        assert!(error.span().end > error.span().start, "{name}: {error}");
    }
    // The preserved empty-register counterexample now lowers through the
    // ordinary Bits adapter. Check its empty classical result independently;
    // it creates no quantum owner or operation, including at width zero.
    let empty = elaborate(
        &source("counterexamples", "packed-bits"),
        "main::f",
        BTreeMap::new(),
    );
    let accepted_empty = accept(&empty);
    distribution(&accepted_empty, &[(&[], 1.0)]);
    assert!(accepted_empty.raw().quantum_inputs.is_empty());
    assert!(accepted_empty.raw().quantum_outputs.is_empty());
    assert!(accepted_empty.raw().classical_inputs.is_empty());
    assert!(accepted_empty.raw().classical_outputs.is_empty());
    assert!(accepted_empty.raw().operations.is_empty());
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
