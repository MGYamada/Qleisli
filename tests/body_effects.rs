//! Principal effect facts and false-annotation diagnostics, with no new evidence.
mod common;

use std::collections::BTreeMap;
use std::process::Command;

use common::SourceRoot;
use qleisli::frontend::compile::{ErrorCode, check_project, project_effects_with_kernel};
use qleisli::frontend::project::SourcePolicy;
use qleisli::frontend::sized::{OperationBinding, ParsedProgram};
use qleisli::interchange::native::Kernel;
use qleisli::ir::Effect;

const IMPORTS: &str = "use std::quantum::init0; use std::observe::measure_z;";
const UNSUPPORTED: &str = "Semantic error: \"externally unitary\" is not supported";

fn explanation(message: &str, inferred: &str, asserted: &str) {
    assert!(
        message.contains(&format!("body effect `{inferred}`")),
        "{message}"
    );
    assert!(
        message.contains(&format!("asserted `{asserted}`")),
        "{message}"
    );
    assert!(message.contains(UNSUPPORTED), "{message}");
    assert!(
        message.contains("cannot override the effect inferred from the body"),
        "{message}"
    );
    assert!(!message.contains("github.com"), "{message}");
    assert!(!message.contains("#283"), "{message}");
    assert!(!message.contains("#315"), "{message}");
}

#[test]
fn false_annotations_reject_direct_and_transitive_effects_in_both_profiles() {
    for (body, inferred, asserted) in [
        (
            "unitary fn f(q:Q<Bit>)->Bit{measure_z(q)}",
            "Observe",
            "Unitary",
        ),
        ("iso fn f(q:Q<Bit>)->Bit{measure_z(q)}", "Observe", "Iso"),
        ("unitary fn f()->Q<Bit>{init0()}", "Iso", "Unitary"),
        (
            "fn g(q:Q<Bit>)->Bit{measure_z(q)} unitary fn f(q:Q<Bit>)->Bit{g(q)}",
            "Observe",
            "Unitary",
        ),
        (
            "unitary fn f(q:Q<Bit>)->Q<Bit>{let a=init0();let b=measure_z(a);q}",
            "Observe",
            "Unitary",
        ),
    ] {
        let source = format!("{IMPORTS}{body}");
        let finite = check_project(&SourceRoot::new(&source).0).unwrap_err();
        assert_eq!(finite.code, ErrorCode::Effect, "{finite}");
        explanation(&finite.message, inferred, asserted);
        let sized = ParsedProgram::parse(BTreeMap::from([("main".into(), source)])).unwrap_err();
        assert_eq!(sized.code(), "effect", "{sized}");
        explanation(sized.message(), inferred, asserted);
    }
}

#[test]
fn broad_assertions_do_not_inflate_caller_or_interface_effects() {
    for prefix in ["", "unitary ", "iso ", "observe "] {
        let source = format!(
            "{prefix}fn g(q:Q<Bit>)->Q<Bit>{{q}} pub unitary fn f(q:Q<Bit>)->Q<Bit>{{g(q)}}"
        );
        check_project(&SourceRoot::new(&source).0).unwrap();
        let sized = ParsedProgram::parse(BTreeMap::from([("main".into(), source)])).unwrap();
        let fact = sized.function_effect("main::g").unwrap();
        assert_eq!(fact.inferred(), Effect::Unitary);
        assert_eq!(
            fact.asserted(),
            match prefix {
                "unitary " => Some(Effect::Unitary),
                "iso " => Some(Effect::Iso),
                "observe " => Some(Effect::Observe),
                _ => None,
            }
        );
        assert_eq!(
            sized.function_effect("main::f").unwrap().inferred(),
            Effect::Unitary
        );
    }
}

#[test]
fn cli_text_and_json_explain_the_semantic_limit_without_tracker_links() {
    let root = SourceRoot::new(&format!(
        "{IMPORTS}unitary fn f(q:Q<Bit>)->Bit{{measure_z(q)}}"
    ));
    for json in [false, true] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_qleisli"));
        command.arg("check").arg(&root.0);
        if json {
            command.arg("--format=json");
        }
        let output = command.output().unwrap();
        assert!(!output.status.success());
        if json {
            assert!(output.stderr.is_empty(), "{output:?}");
            let result = String::from_utf8(output.stdout).unwrap();
            assert!(result.contains("\"code\":\"effect\""), "{result}");
            assert!(result.contains("\\\"externally unitary\\\""), "{result}");
            explanation(&result.replace("\\\"", "\""), "Observe", "Unitary");
        } else {
            explanation(
                &String::from_utf8(output.stderr).unwrap(),
                "Observe",
                "Unitary",
            );
        }
    }
}

#[test]
fn immutable_metadata_and_documentation_use_the_checked_source_bytes() {
    let original = "/// A broader assertion is separate from the inferred fact.\nobserve fn f(q:Q<Bit>)->Q<Bit>{q}";
    let root = SourceRoot::new(original);
    let finite =
        project_effects_with_kernel(&root.0, SourcePolicy::Legacy, &Kernel::selected().unwrap())
            .unwrap();
    let sized = ParsedProgram::parse(BTreeMap::from([("main".into(), original.into())])).unwrap();
    // Mutating the input file cannot rebind either immutable checked report.
    root.write("main.qli", "unitary fn f(q:Q<Bit>)->Bit{missing(q)}");
    for text in [
        finite.documentation("main").unwrap().unwrap(),
        sized.documentation("main").unwrap().unwrap(),
    ] {
        assert!(text.contains("Inferred quantum effect: `Unitary`"));
        assert!(text.contains("Checked upper-bound assertion: `Observe`"));
        assert!(text.contains("A broader assertion"));
        assert!(!text.contains("missing(q)"));
        assert!(text.contains("does not establish exact Meaning"));
    }
    assert_eq!(
        finite.function_effect("main::f"),
        sized.function_effect("main::f")
    );
    assert!(finite.documentation("absent").is_none());
    assert!(sized.documentation("absent").is_none());
    let source_only = qleisli::frontend::documentation::render_markdown(original).unwrap();
    assert!(source_only.contains("Source documentation only"));
    assert!(!source_only.contains("Inferred quantum effect"));
    assert!(
        project_effects_with_kernel(&root.0, SourcePolicy::Legacy, &Kernel::selected().unwrap())
            .is_err()
    );
}

#[test]
fn all_checked_arms_zero_folds_and_decreasing_recursion_contribute_effects() {
    for source in [
        include_str!(
            "fixtures/authoring_sessions/body-effects-v030/attempt-01/zero-fold-observation/main.qli"
        ),
        include_str!(
            "fixtures/authoring_sessions/body-effects-v030/attempt-01/dead-static-observation/main.qli"
        ),
        include_str!(
            "fixtures/authoring_sessions/body-effects-v030/attempt-01/recursive-observation/main.qli"
        ),
    ] {
        let sized = ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap();
        assert_eq!(
            sized.function_effect("main::f").unwrap().inferred(),
            Effect::Observe
        );
        let asserted = source.replace("pub fn f", "pub unitary fn f");
        let error = ParsedProgram::parse(BTreeMap::from([("main".into(), asserted)])).unwrap_err();
        assert_eq!(error.code(), "effect");
        explanation(error.message(), "Observe", "Unitary");
    }
}

#[test]
fn typed_finite_lifts_preserve_width_and_scalar_phase_classification() {
    for (source, effect) in [
        (
            include_str!(
                "fixtures/authoring_sessions/body-effects-v030/attempt-01/finite-lift-permutation/main.qli"
            ),
            Effect::Unitary,
        ),
        (
            include_str!(
                "fixtures/authoring_sessions/body-effects-v030/attempt-01/finite-lift-expansion/main.qli"
            ),
            Effect::Iso,
        ),
        (
            include_str!(
                "fixtures/authoring_sessions/body-effects-v030/attempt-01/scalar-unit/main.qli"
            ),
            Effect::Unitary,
        ),
    ] {
        let root = SourceRoot::new(source);
        let finite = project_effects_with_kernel(
            &root.0,
            SourcePolicy::Legacy,
            &Kernel::selected().unwrap(),
        )
        .unwrap();
        assert_eq!(
            finite.function_effect("main::f").unwrap().inferred(),
            effect
        );
        assert_eq!(finite.function_effect("main::f").unwrap().asserted(), None);
    }
}

#[test]
fn names_and_module_paths_do_not_grant_body_effects_or_access() {
    let source = include_str!(
        "fixtures/authoring_sessions/body-effects-v030/attempt-01/primitive-like-local-name/main.qli"
    );
    for module in ["main", "library::ordinary", "user::nested"] {
        let sized = ParsedProgram::parse(BTreeMap::from([(module.into(), source.into())])).unwrap();
        assert_eq!(
            sized
                .function_effect(&format!("{module}::f"))
                .unwrap()
                .inferred(),
            Effect::Unitary
        );
    }
    // The reserved std namespace cannot be injected as a sized source module.
    let error = ParsedProgram::parse(BTreeMap::from([("std::ordinary".into(), source.into())]))
        .unwrap_err();
    assert_eq!(error.code(), "module");
    for (source, code) in [
        (
            include_str!(
                "fixtures/authoring_sessions/body-effects-v030/attempt-01/generic-missing-access/main.qli"
            ),
            "access",
        ),
        (
            include_str!(
                "fixtures/authoring_sessions/body-effects-v030/attempt-01/duplicate-owner/main.qli"
            ),
            "ownership",
        ),
        (
            include_str!(
                "fixtures/authoring_sessions/body-effects-v030/attempt-01/mutual-cycle/main.qli"
            ),
            "cycle",
        ),
    ] {
        let error =
            ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap_err();
        assert_eq!(error.code(), code, "{error}");
    }
}

#[test]
fn every_derived_stdlib_body_exports_its_effect_without_runtime_annotation() {
    let root = SourceRoot::new("fn main()->Unit{()}");
    let report =
        project_effects_with_kernel(&root.0, SourcePolicy::Legacy, &Kernel::selected().unwrap())
            .unwrap();
    for (module, functions, effect) in [
        (
            "transform",
            &["hadamard2", "qft2", "qft3"][..],
            Effect::Unitary,
        ),
        ("reflection", &["reflect_uniform2"][..], Effect::Unitary),
        (
            "measurement",
            &["measure_x", "measure_z2", "parity_zz"][..],
            Effect::Observe,
        ),
    ] {
        for function in functions {
            let fact = report
                .function_effect(&format!("std::{module}::{function}"))
                .unwrap();
            assert_eq!(fact.inferred(), effect, "{module}::{function}");
            assert_eq!(fact.asserted(), None, "{module}::{function}");
        }
        let documentation = report
            .documentation(&format!("std::{module}"))
            .unwrap()
            .unwrap();
        assert!(documentation.contains("Inferred quantum effect:"));
        assert!(!documentation.contains("Checked upper-bound assertion:"));
    }
    // Basis functions have their distinct ordinary total-function checking.
    assert!(
        report
            .function_effect("std::reflection::nonzero2")
            .is_none()
    );

    root.write(
        "arithmetic.qli",
        include_str!("../examples/order_finding/arithmetic.qli"),
    );
    let report =
        project_effects_with_kernel(&root.0, SourcePolicy::Legacy, &Kernel::selected().unwrap())
            .unwrap();
    for name in ["increment2", "add2", "mul2_mod15"] {
        let fact = report
            .function_effect(&format!("arithmetic::{name}"))
            .unwrap();
        assert_eq!(fact.inferred(), Effect::Unitary, "arithmetic::{name}");
        assert_eq!(fact.asserted(), None, "arithmetic::{name}");
        assert!(
            report
                .function_effect(&format!("std::arithmetic::{name}"))
                .is_none()
        );
    }
    let documentation = report.documentation("arithmetic").unwrap().unwrap();
    assert!(documentation.contains("Inferred quantum effect:"));
    assert!(!documentation.contains("Checked upper-bound assertion:"));
}

#[test]
fn operation_providers_use_principal_effects_and_cannot_hide_measurement() {
    let apply = "fn apply[static U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Apply(U){U(q)} pub fn f(q:Q<Bit>)->Q<Bit>{apply[g](q)}";
    for (provider, accepted) in [
        (
            "use std::quantum::x; observe fn g(q:Q<Bit>)->Q<Bit>{x(q)}",
            true,
        ),
        (
            "use std::quantum::init0; use std::observe::measure_z; fn g(q:Q<Bit>)->Q<Bit>{let a=init0();let b=measure_z(a);q}",
            false,
        ),
    ] {
        let source = format!("{provider}{apply}");
        let finite = check_project(&SourceRoot::new(&source).0);
        let sized = ParsedProgram::parse(BTreeMap::from([("main".into(), source)]));
        if accepted {
            finite.unwrap();
            assert_eq!(
                sized
                    .unwrap()
                    .function_effect("main::f")
                    .unwrap()
                    .inferred(),
                Effect::Unitary
            );
        } else {
            assert!(finite.is_err());
            assert_eq!(sized.unwrap_err().code(), "effect");
        }
    }
}

#[test]
fn host_selected_providers_distinguish_unsupported_effects_from_shape_errors() {
    for (source, expected) in [
        (
            include_str!(
                "fixtures/authoring_sessions/body-effects-host-review-v030/attempt-02/host-hidden-observer/main.qli"
            ),
            Some("effect"),
        ),
        (
            include_str!(
                "fixtures/authoring_sessions/body-effects-host-review-v030/attempt-02/host-wide-pure/main.qli"
            ),
            None,
        ),
        (
            include_str!(
                "fixtures/authoring_sessions/body-effects-host-review-v030/attempt-02/host-wrong-shape/main.qli"
            ),
            Some("type"),
        ),
    ] {
        let program =
            ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap();
        let result = program.instantiate(
            "main::entry",
            BTreeMap::new(),
            BTreeMap::from([(
                "U".into(),
                OperationBinding::new("main::provider", BTreeMap::new()),
            )]),
        );
        if let Some(code) = expected {
            let error = result.unwrap_err();
            assert_eq!(error.code(), code, "{error}");
            if code == "effect" {
                assert!(error.message().contains("inferred body effect `Observe`"));
                assert!(error.message().contains(UNSUPPORTED));
                assert!(!error.message().contains("github.com"));
            } else {
                assert!(!error.message().contains(UNSUPPORTED));
            }
        } else {
            result.unwrap();
            let fact = program.function_effect("main::provider").unwrap();
            assert_eq!(fact.inferred(), Effect::Unitary);
            assert_eq!(fact.asserted(), Some(Effect::Observe));
        }
    }
}

#[test]
fn host_selected_cli_uses_the_same_semantic_explanation_in_text_and_json() {
    let source = include_str!(
        "fixtures/authoring_sessions/body-effects-host-review-v030/attempt-02/host-hidden-observer/main.qli"
    );
    let root = SourceRoot::new(source);
    for json in [false, true] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_qleisli"));
        command
            .args([
                "check",
                "--entry=main::entry",
                "--operation=U=main::provider",
            ])
            .arg(format!(
                "--module=main={}",
                root.0.join("main.qli").display()
            ));
        if json {
            command.arg("--format=json");
        }
        let output = command.output().unwrap();
        assert!(!output.status.success());
        let message = if json {
            assert!(output.stderr.is_empty());
            let text = String::from_utf8(output.stdout).unwrap();
            assert!(text.contains("\"code\":\"effect\""), "{text}");
            text.replace("\\\"", "\"")
        } else {
            String::from_utf8(output.stderr).unwrap()
        };
        assert!(
            message.contains("inferred body effect `Observe`"),
            "{message}"
        );
        assert!(message.contains(UNSUPPORTED), "{message}");
        assert!(!message.contains("github.com"), "{message}");
        assert!(!message.contains("#283"), "{message}");
    }
}

#[test]
fn principal_classes_do_not_depend_on_declaration_order_or_call_expansion() {
    let declarations = [
        "fn a(q:Q<Bit>)->Q<Bit>{q}",
        "fn b()->Q<Bit>{init0()}",
        "fn c()->Bit{measure_z(a(b()))}",
    ];
    for order in [
        [0, 1, 2],
        [0, 2, 1],
        [1, 0, 2],
        [1, 2, 0],
        [2, 0, 1],
        [2, 1, 0],
    ] {
        let source = format!(
            "{IMPORTS}{}",
            order.map(|index| declarations[index]).join(" ")
        );
        let root = SourceRoot::new(&source);
        let finite = project_effects_with_kernel(
            &root.0,
            SourcePolicy::Legacy,
            &Kernel::selected().unwrap(),
        )
        .unwrap();
        let sized = ParsedProgram::parse(BTreeMap::from([("main".into(), source)])).unwrap();
        for (name, effect) in [
            ("a", Effect::Unitary),
            ("b", Effect::Iso),
            ("c", Effect::Observe),
        ] {
            let path = format!("main::{name}");
            assert_eq!(finite.function_effect(&path).unwrap().inferred(), effect);
            assert_eq!(finite.function_effect(&path), sized.function_effect(&path));
        }
    }
}

#[test]
fn fn_suggestions_do_not_require_a_redundant_effect_annotation() {
    let parse = qleisli::frontend::parser::parse_module("pub nonsense").unwrap_err();
    assert!(parse.message.contains("expected `fn`"), "{parse}");
    let root = SourceRoot::new(include_str!(
        "fixtures/authoring_sessions/body-effects-host-review-v030/attempt-02/finite-sealed-provider/main.qli"
    ));
    let error = check_project(&root.0).unwrap_err();
    assert_eq!(error.code, ErrorCode::TypeMismatch);
    assert!(error.message.contains("inferred Unitary body effect"));
    assert!(error.message.contains("`fn wrapped_gate"));
    assert!(!error.message.contains("declared unitary"));
}
