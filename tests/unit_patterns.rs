//! Exact ordinary Unit patterns across the common type judgment's consumers.
//! Bounded native tests do not constitute a universal preservation theorem.
//! Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
mod common;

use common::SourceRoot;
use qleisli::contract::BasisType;
use qleisli::contract::exact::Exact;
use qleisli::frontend::compile::{ErrorCode, check_project, compile_project};
use qleisli::frontend::parser::parse_module;
use qleisli::frontend::sized::ParsedProgram;
use qleisli::interchange::hierarchical::{Kernel, execution::ExecutionLimits};
use qleisli::ir::{CircuitAction, Effect, RawOp};
use qleisli::sim::{SimulationLimits, run_closed};
use std::collections::BTreeMap;
use std::path::Path;

fn source(category: &str, name: &str) -> String {
    std::fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/authoring_sessions/finite-unit-pattern-v030")
            .join(category)
            .join(name)
            .join("main.qli"),
    )
    .unwrap()
}

fn reject(category: &str, name: &str, code: ErrorCode) {
    let input = source(category, name);
    let error = check_project(&SourceRoot::new(&input).0).unwrap_err();
    assert_eq!(error.code, code, "{name}: {error}");
    assert!(error.span.end > error.span.start, "{name}: {error}");
}

fn parsed(input: &str) -> ParsedProgram {
    ParsedProgram::parse(BTreeMap::from([("main".into(), input.into())])).unwrap()
}

#[test]
fn finite_named_unit_parameters_and_nested_patterns_are_ordinary_values() {
    for name in [
        "runtime-unit",
        "runtime-nested",
        "runtime-mixed-owner",
        "basis-unit",
    ] {
        check_project(&SourceRoot::new(&source("attempt-01", name)).0).unwrap();
    }
    for name in ["unit-copy-drop", "nested-unit-only", "basis-literal-call"] {
        check_project(&SourceRoot::new(&source("validation-sources", name)).0).unwrap();
    }
    let checked =
        compile_project(&SourceRoot::new(&source("attempt-01", "runtime-nested")).0).unwrap();
    assert_eq!(
        run_closed(&checked, SimulationLimits::default()).unwrap(),
        BTreeMap::from([(vec![true], 1.0)])
    );
}

#[test]
fn exact_pattern_shapes_reject_quantum_bit_and_equal_width_products() {
    for name in [
        "runtime-quantum-unit",
        "runtime-bit",
        "runtime-unit-product",
        "basis-bit",
        "coherent-unit-product",
    ] {
        reject("counterexamples", name, ErrorCode::TypeMismatch);
    }
    reject(
        "counterexamples",
        "ordinary-bits-zero",
        ErrorCode::Unsupported,
    );
    reject(
        "validation-sources",
        "first-shape-error",
        ErrorCode::TypeMismatch,
    );
    reject(
        "validation-sources",
        "duplicate-owner",
        ErrorCode::Ownership,
    );
    reject("validation-sources", "lost-owner", ErrorCode::Ownership);
}

#[test]
fn unit_basis_patterns_keep_exact_unary_function_and_predicate_arity() {
    check_project(&SourceRoot::new(&source("attempt-01", "computed-unit")).0).unwrap();
    reject("counterexamples", "nullary-predicate", ErrorCode::Arity);
    reject("validation-sources", "basis-nullary-call", ErrorCode::Arity);
}

#[test]
fn runtime_parameter_pattern_now_uses_the_common_exact_shape_rule() {
    let input = source("desired-unsupported", "runtime-parameter-pattern");
    parse_module(&input).unwrap();
    check_project(&SourceRoot::new(&input).0).unwrap();
}

#[test]
fn effectful_unit_rhs_is_retained_before_the_empty_result_is_bound() {
    let current =
        compile_project(&SourceRoot::new(&source("attempt-01", "effectful-unit")).0).unwrap();
    let control =
        compile_project(&SourceRoot::new(&source("controls", "named-effectful-unit")).0).unwrap();
    assert_eq!(current.raw(), control.raw());
    assert_eq!(current.raw().declared_effect, Effect::Observe);
    assert_eq!(
        current
            .raw()
            .operations
            .iter()
            .filter(|op| matches!(op, RawOp::Discard { .. }))
            .count(),
        1
    );
    assert!(
        current
            .raw()
            .operations
            .iter()
            .any(|op| matches!(op, RawOp::Init0 { .. }))
    );
    let distribution = run_closed(&current, SimulationLimits::default()).unwrap();
    assert_eq!(distribution.len(), 1);
    // H uses floating complex amplitudes in this simulator. Exact phase and
    // retained IR above/below are checked independently of this tolerance.
    assert!((distribution[&vec![true]] - 1.0).abs() < 1e-12);
    reject("counterexamples", "unitary-effect", ErrorCode::Effect);
}

#[test]
fn coherent_unit_lift_retains_exact_scalar_and_reference_action() {
    let input = source("validation-sources", "coherent-contract");
    let accepted = compile_project(&SourceRoot::new(&input).0).unwrap();
    let evidence = accepted
        .raw()
        .operations
        .iter()
        .flat_map(|op| match op {
            RawOp::ApplyUnitary { steps, .. } => steps
                .iter()
                .filter_map(|step| match &step.action {
                    CircuitAction::Contract { evidence, .. } => Some(evidence),
                    _ => None,
                })
                .collect::<Vec<_>>(),
            _ => Vec::new(),
        })
        .collect::<Vec<_>>();
    assert_eq!(evidence.len(), 1);
    let evidence = evidence[0];
    assert_eq!(evidence.signature(), &BasisType::Unit);
    assert_eq!(
        (evidence.meaning().rows(), evidence.meaning().cols()),
        (1, 1)
    );
    let actual = evidence.meaning().get(0, 0).unwrap();
    let omega = Exact::phase(1);
    assert_eq!(actual, omega);
    assert!(
        evidence
            .implementation()
            .operations
            .iter()
            .any(|op| matches!(op, RawOp::LiftBasis { .. }))
    );
    // Algebraic extension of the already checked scalar equality, not three
    // additional native executions. Sized cases below execute reference slices.
    for reference in 0..3_i128 {
        let amplitude = Exact::new([reference - 2, 1, 3 - reference, reference], 2).unwrap();
        assert_eq!(
            actual.mul(amplitude).unwrap(),
            omega.mul(amplitude).unwrap()
        );
    }
    assert!(
        evidence
            .identity()
            .sources
            .iter()
            .any(|(module, text)| module == "main" && text == &input)
    );
}

#[test]
fn coherent_control_exposes_unit_phase_for_lift_and_computed_pattern() {
    for (name, probability_one) in [
        ("coherent-control", (2.0 - 2.0_f64.sqrt()) / 4.0),
        ("computed-control", 1.0),
    ] {
        let accepted =
            compile_project(&SourceRoot::new(&source("validation-sources", name)).0).unwrap();
        let distribution = run_closed(&accepted, SimulationLimits::default()).unwrap();
        assert!(
            (distribution.get(&vec![true]).copied().unwrap_or(0.0) - probability_one).abs() < 1e-12
        );
        assert!(
            (distribution.get(&vec![false]).copied().unwrap_or(0.0) - (1.0 - probability_one))
                .abs()
                < 1e-12
        );
    }
}

#[test]
fn sized_symbolic_and_concrete_patterns_share_the_same_unit_shape_rule() {
    let kernel = Kernel::new(std::env::var_os("QLEISLI_KERNEL").expect("explicit native checker"));
    for (category, name, input) in [
        ("attempt-01", "runtime-unit", vec![[0.2, 0.3], [-0.4, 0.7]]),
        (
            "validation-sources",
            "nested-unit-only",
            vec![[0.2, 0.3], [-0.4, 0.7]],
        ),
        (
            "validation-sources",
            "sized-consume",
            vec![[0.2, 0.3], [-0.4, 0.7]],
        ),
        (
            "attempt-01",
            "runtime-mixed-owner",
            vec![[0.2, 0.3], [-0.4, 0.7], [0.6, -0.1], [-0.5, -0.2]],
        ),
    ] {
        let graph = parsed(&source(category, name))
            .instantiate("main::f", BTreeMap::new(), BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap();
        let proposal = graph.lower().unwrap();
        let accepted = kernel
            .check_against_native(proposal.payload(), proposal.comparison_request())
            .unwrap();
        let output = accepted
            .execute_pure(
                &input,
                2,
                ExecutionLimits {
                    max_amplitudes: 16,
                    max_steps: 1000,
                },
            )
            .unwrap();
        assert_eq!(output.amplitudes, input, "{name}");
    }
    for (category, name) in [
        ("counterexamples", "ordinary-bits-zero"),
        ("counterexamples", "runtime-bit"),
        ("counterexamples", "runtime-unit-product"),
        ("validation-sources", "sized-zero-owner"),
        ("validation-sources", "sized-nested-exact-mismatch"),
    ] {
        let error = ParsedProgram::parse(BTreeMap::from([("main".into(), source(category, name))]))
            .unwrap_err();
        assert_eq!(error.code(), "type", "{name}: {error}");
    }
}
