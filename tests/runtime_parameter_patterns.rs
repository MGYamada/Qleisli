//! Bounded independent oracles for exact runtime parameter patterns.
//! Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
mod common;

use common::SourceRoot;
use qleisli::frontend::ast::PatternKind;
use qleisli::frontend::compile::{ErrorCode, check_project, compile_project};
use qleisli::frontend::compile::{OperationBinding, ParsedProgram};
use qleisli::frontend::parser::parse_module;
use qleisli::interchange::hierarchical::{Kernel, execution::ExecutionLimits};
use qleisli::ir::{Effect, RawOp};
use qleisli::sim::{SimulationLimits, run_closed};
use std::collections::BTreeMap;
use std::path::Path;

fn source(path: &str) -> String {
    std::fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/authoring_sessions/runtime-parameter-pattern-v030")
            .join(path),
    )
    .unwrap()
}

fn case(category: &str, name: &str) -> String {
    // Explicit derivatives preserve the first missing-static sources and their
    // actual baseline diagnostics; source-map.json binds both byte identities.
    match (category, name) {
        ("followups", "zero-fold-quantum-wildcard") => {
            let original = Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("tests/fixtures/authoring_sessions/runtime-parameter-pattern-v030")
                .join(format!("{category}/{name}/main.qli"));
            std::fs::read_to_string(common::current_namespace_fixture(&original)).unwrap()
        }
        ("counterexamples", "static-collision") | ("attempt-01", "static-mixed") => {
            source(&format!("validation-repairs/{name}.qli"))
        }
        _ => source(&format!("{category}/{name}/main.qli")),
    }
}

fn validation(name: &str) -> String {
    if name == "phase-through-product" {
        // Preserve the original source and its hosted parse failure. This
        // explicit current translation changes only the retired coherent form;
        // the Unit/product owners, scalar phase and independent oracle remain.
        let original = source("validation-sources/phase-through-product.qli");
        let current = std::fs::read_to_string(
            Path::new(env!("CARGO_MANIFEST_DIR")).join(
                "tests/fixtures/review_v030alpha/hosted-ci-runtime-pattern-repair/phase-through-product.qli",
            ),
        )
        .unwrap();
        assert_eq!(
            current,
            original.replace(
                "let pair = do bit <- init0(); pure ((),bit);",
                "let pair = basis init0() as bit { ((),bit) };",
            ),
            "current phase source must preserve every other original byte",
        );
        return current;
    }
    let directory = match name {
        "static-forwarding"
        | "operation-binding"
        | "static-operation-collision"
        | "unitary-argument-effect" => "validation-repairs",
        _ => "validation-sources",
    };
    source(&format!("{directory}/{name}.qli"))
}

fn parsed(input: &str) -> ParsedProgram {
    let parsed = ParsedProgram::parse(BTreeMap::from([("main".into(), input.into())])).unwrap();
    let cloned = parsed.clone();
    drop(parsed);
    assert_eq!(cloned.source("main"), Some(input));
    cloned
}

fn finite_reject(input: &str, code: ErrorCode) {
    let error = check_project(&SourceRoot::new(input).0).unwrap_err();
    assert_eq!(error.code, code, "{error}");
    assert!(error.span.end > error.span.start, "{error}");
}

fn sized_reject(input: &str, code: &str) {
    let error = ParsedProgram::parse(BTreeMap::from([("main".into(), input.into())])).unwrap_err();
    assert_eq!(error.code(), code, "{error}");
    assert_eq!(error.module(), Some("main"));
    assert!(error.span().end > error.span().start, "{error}");
}

fn execute(
    program: &qleisli::frontend::compile::ElaboratedProgram,
    input: &[[f64; 2]],
) -> Vec<[f64; 2]> {
    let proposal = program.lower().unwrap();
    let kernel = Kernel::new(std::env::var_os("QLEISLI_KERNEL").expect("explicit native checker"));
    let accepted = kernel
        .check_against_native(proposal.payload(), proposal.comparison_request())
        .unwrap();
    assert_eq!(accepted.payload(), proposal.payload());
    let result = accepted
        .execute_pure(
            input,
            2,
            ExecutionLimits {
                max_amplitudes: 16,
                max_steps: 1000,
            },
        )
        .unwrap();
    assert_eq!(result.reference_dimension, 2);
    result.amplitudes
}

#[test]
fn common_ast_keeps_argument_count_exact_patterns_and_original_spans() {
    let input = case("attempt-01", "unit");
    let module = parse_module(&input).unwrap();
    let parameters = &module.decls[0].params;
    assert_eq!(parameters.len(), 2);
    assert!(matches!(&parameters[0].pattern.kind, PatternKind::Tuple(fields) if fields.is_empty()));
    assert_eq!(
        &input[parameters[0].pattern.span.start..parameters[0].pattern.span.end],
        "()"
    );
    let module = parse_module(&validation("repeated-ordinary-wildcards")).unwrap();
    assert_eq!(module.decls[0].params.len(), 3);
    assert!(matches!(
        module.decls[0].params[0].pattern.kind,
        PatternKind::Wildcard
    ));
    assert!(matches!(
        module.decls[0].params[1].pattern.kind,
        PatternKind::Wildcard
    ));
}

#[test]
fn finite_ordinary_fields_may_copy_drop_and_match_unit_without_changing_arity() {
    for name in [
        "unit",
        "nested-copy-wildcard",
        "mixed-swap",
        "wildcard-ordinary",
    ] {
        check_project(&SourceRoot::new(&case("attempt-01", name)).0).unwrap();
    }
    check_project(&SourceRoot::new(&validation("repeated-ordinary-wildcards")).0).unwrap();
    for (name, expected) in [
        ("copy-result", vec![true, true]),
        ("unit-explicit-call", vec![true]),
    ] {
        let checked = compile_project(&SourceRoot::new(&validation(name)).0).unwrap();
        assert_eq!(
            run_closed(&checked, SimulationLimits::default()).unwrap(),
            BTreeMap::from([(expected, 1.0)])
        );
    }
    finite_reject(&case("counterexamples", "call-arity"), ErrorCode::Arity);
    finite_reject(&validation("unit-nullary-call"), ErrorCode::Arity);
    let input = validation("non-nullary-entry");
    finite_reject(&input, ErrorCode::InvalidEntry);
    let error = compile_project(&SourceRoot::new(&input).0).unwrap_err();
    assert_eq!(error.code, ErrorCode::InvalidEntry);
}

#[test]
fn exact_shape_owner_and_unused_declaration_failures_remain_located() {
    for name in ["quantum-tuple-pattern", "unit-shape", "unused-bad"] {
        finite_reject(&case("counterexamples", name), ErrorCode::TypeMismatch);
    }
    for name in [
        "quantum-wildcard",
        "duplicate-across-parameters",
        "lost-owner",
    ] {
        finite_reject(&case("counterexamples", name), ErrorCode::Ownership);
    }
    for name in ["quantum-unit-wildcard", "quantum-tuple-wildcard"] {
        finite_reject(&validation(name), ErrorCode::Ownership);
    }
    finite_reject(
        &validation("static-operation-collision"),
        ErrorCode::Ownership,
    );
    let input = case("counterexamples", "lost-owner");
    let error = check_project(&SourceRoot::new(&input).0).unwrap_err();
    assert_eq!(&input[error.span.start..error.span.end], "r");
    sized_reject(&case("counterexamples", "unit-shape"), "type");
    sized_reject(&case("counterexamples", "unused-bad"), "type");
    sized_reject(
        &case("counterexamples", "duplicate-across-parameters"),
        "name",
    );
    sized_reject(&case("counterexamples", "static-collision"), "name");
    sized_reject(&case("counterexamples", "lost-owner"), "ownership");
}

#[test]
fn sized_inputs_retain_whole_parameter_trees_and_independent_swap_action() {
    let input = [
        [0.1, -0.2],
        [0.3, 0.4],
        [-0.5, 0.6],
        [0.7, -0.8],
        [-0.9, 0.2],
        [0.4, -0.3],
        [0.6, 0.1],
        [-0.2, -0.7],
    ];
    let mut expected = input;
    for reference in 0..2 {
        for a in 0..2 {
            for b in 0..2 {
                expected[reference * 4 + b + 2 * a] = input[reference * 4 + a + 2 * b];
            }
        }
    }
    for (category, name) in [
        ("attempt-01", "mixed-swap"),
        ("controls", "named-mixed-swap"),
    ] {
        let text = case(category, name);
        let graph = parsed(&text)
            .instantiate("main::f", BTreeMap::new(), BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap();
        let definition = &graph.definitions()[graph.root()];
        assert_eq!(definition.inputs().len(), 1);
        let value = &definition.inputs()[0];
        assert_eq!(value.fields().len(), 2);
        assert_eq!(value.fields()[0].fields().len(), 2);
        assert_eq!(value.fields()[0].fields()[0].ty().kind(), "unit");
        assert!(value.fields()[0].fields()[1].ty().is_quantum());
        assert!(value.fields()[1].ty().is_quantum());
        assert_ne!(
            value.fields()[0].fields()[1].identity(),
            value.fields()[1].identity()
        );
        assert_eq!(execute(&graph, &input), expected);
        assert_eq!(
            graph.instantiation().program().source("main"),
            Some(text.as_str())
        );
    }
}

#[test]
fn sized_nonlinear_wildcards_are_shared_by_parameters_let_and_zero_fold() {
    let input = [[0.1, -0.2], [0.3, 0.4], [-0.5, 0.6], [0.7, -0.8]];
    for text in [
        validation("repeated-ordinary-wildcards"),
        case("additional-wildcards", "let-wildcard"),
        case("additional-wildcards", "zero-fold-wildcard"),
    ] {
        let graph = parsed(&text)
            .instantiate("main::f", BTreeMap::new(), BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap();
        assert_eq!(execute(&graph, &input), input);
    }
    // Ordinary Bits<0> remains its own source type. Checking/elaboration of a
    // wildcard is distinct from this profile's unfinished classical lowering.
    let graph = parsed(&validation("ordinary-bits-wildcard"))
        .instantiate("main::f", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap();
    let first = &graph.definitions()[graph.root()].inputs()[0];
    assert_eq!(first.ty().kind(), "bits");
    assert_eq!(first.ty().width(), Some(0));
    assert!(!first.ty().is_quantum());
}

#[test]
fn sized_wildcards_cannot_erase_nested_or_zero_width_owners_even_in_zero_folds() {
    for text in [
        case("counterexamples", "quantum-wildcard"),
        case("counterexamples", "zero-owner-wildcard"),
        validation("quantum-tuple-wildcard"),
        case("additional-wildcards", "quantum-let-wildcard"),
        case("followups", "zero-fold-quantum-wildcard"),
        case("followups", "let-nested-quantum-wildcard"),
    ] {
        sized_reject(&text, "ownership");
    }
}

#[test]
fn static_substitutions_and_provider_bindings_keep_declaration_and_source_identity() {
    parsed(&case("attempt-01", "static-mixed"))
        .instantiate(
            "main::f",
            BTreeMap::from([("n".into(), 1)]),
            BTreeMap::new(),
        )
        .unwrap()
        .elaborate()
        .unwrap();
    let text = validation("static-forwarding");
    for n in [0, 1] {
        let graph = parsed(&text)
            .instantiate(
                "main::f",
                BTreeMap::from([("n".into(), n)]),
                BTreeMap::new(),
            )
            .unwrap()
            .elaborate()
            .unwrap();
        assert_eq!(graph.definitions().len(), 2);
        for definition in graph.definitions() {
            assert_eq!(definition.inputs().len(), 1);
            assert_eq!(definition.naturals().get("n"), Some(&n));
        }
        let input = vec![[0.25, -0.5]; 2 << n];
        assert_eq!(execute(&graph, &input), input);
    }
    let text = validation("operation-binding");
    check_project(&SourceRoot::new(&text).0).unwrap();
    let graph = parsed(&text)
        .instantiate(
            "main::f",
            BTreeMap::new(),
            BTreeMap::from([(
                "U".into(),
                OperationBinding::new("main::gate", BTreeMap::new()),
            )]),
        )
        .unwrap()
        .elaborate()
        .unwrap();
    assert_eq!(graph.definitions()[graph.root()].inputs().len(), 1);
    assert!(
        graph
            .definitions()
            .iter()
            .any(|definition| definition.path() == "main::gate")
    );
    assert_eq!(
        graph.instantiation().program().source("main"),
        Some(text.as_str())
    );
    let input = [[0.1, -0.2], [0.3, 0.4], [-0.5, 0.6], [0.7, -0.8]];
    assert_eq!(
        execute(&graph, &input),
        [input[1], input[0], input[3], input[2]]
    );
}

#[test]
fn discarded_unit_parameters_do_not_erase_argument_effects_or_scalar_phase() {
    let control =
        compile_project(&SourceRoot::new(&case("controls", "named-effectful-unit")).0).unwrap();
    for text in [
        case("attempt-01", "effectful-unit"),
        validation("unit-wildcard-effects"),
    ] {
        let checked = compile_project(&SourceRoot::new(&text).0).unwrap();
        assert_eq!(checked.raw(), control.raw());
        assert_eq!(checked.raw().declared_effect, Effect::Observe);
        assert_eq!(
            checked
                .raw()
                .operations
                .iter()
                .filter(|op| matches!(op, RawOp::Discard { .. }))
                .count(),
            1
        );
        let distribution = run_closed(&checked, SimulationLimits::default()).unwrap();
        assert!((distribution[&vec![true]] - 1.0).abs() < 1e-12);
    }
    finite_reject(&validation("unitary-argument-effect"), ErrorCode::Effect);
    // The first effectful argument consumes q. The diagnostic must identify
    // the second use, preserving left-to-right argument evaluation order.
    let input = validation("argument-owner-order");
    let error = check_project(&SourceRoot::new(&input).0).unwrap_err();
    assert_eq!(error.code, ErrorCode::Ownership);
    assert_eq!(error.span.start, input.rfind("q)").unwrap());
    assert_eq!(&input[error.span.start..error.span.end], "q");
    // Independent controlled scalar omega: p(1)=(2-sqrt(2))/4. A dropped
    // zero-wire owner or erased phase would instead yield probability zero.
    let checked =
        compile_project(&SourceRoot::new(&validation("phase-through-product")).0).unwrap();
    let distribution = run_closed(&checked, SimulationLimits::default()).unwrap();
    let expected = (2.0 - 2.0_f64.sqrt()) / 4.0;
    assert!((distribution.get(&vec![true]).copied().unwrap_or(0.0) - expected).abs() < 1e-12);
    assert!(
        (distribution.get(&vec![false]).copied().unwrap_or(0.0) - (1.0 - expected)).abs() < 1e-12
    );
}
