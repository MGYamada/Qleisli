//! Diagnostic coverage for issue #368, including ordinary static execution.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
mod common;

use common::SourceRoot;
use qleisli::frontend::ast::Span;
use qleisli::frontend::compile::{ParsedProgram, check_project_with_kernel, compile_project};
use qleisli::frontend::parser::parse_module;
use qleisli::frontend::project::SourcePolicy;
use qleisli::interchange::native::Kernel;
use std::collections::BTreeMap;
use std::process::Command;

static ADJOINT: std::sync::LazyLock<String> = std::sync::LazyLock::new(|| {
    common::current_source_text(
        "tests/fixtures/authoring_sessions/common-diagnostics-v030/attempt-01/adjoint-observe/main.qli",
    )
});
static MISSING_ELSE: std::sync::LazyLock<String> = std::sync::LazyLock::new(|| {
    common::current_source_text(
        "tests/fixtures/authoring_sessions/common-diagnostics-v030/attempt-01/missing-else/main.qli",
    )
});
const QUALIFIED: &str = include_str!(
    "fixtures/authoring_sessions/common-diagnostics-v030/attempt-01/qualified-call/main.qli"
);
static REBIND: std::sync::LazyLock<String> = std::sync::LazyLock::new(|| {
    common::current_source_text(
        "tests/fixtures/authoring_sessions/common-diagnostics-v030/attempt-01/live-rebinding/main.qli",
    )
});

fn refusal(source: &str, code: &str, span: Span, message: &str) {
    let selected =
        ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap_err();
    assert_eq!(selected.span(), span, "{selected}");
    assert!(selected.message().contains(message), "{selected}");
    let root = SourceRoot::new(source);
    let failure = check_project_with_kernel(
        &root.0,
        SourcePolicy::default(),
        &Kernel::new(root.0.join("must-not-invoke-native")),
    )
    .unwrap_err();
    assert_eq!(failure.code, code, "{failure:?}");
    assert_eq!(failure.primary.unwrap().span, span);
    assert_eq!(failure.message, selected.message());
}

#[test]
fn non_endomorphic_adjoint_names_the_effect_obligation_without_guessing_body_effects() {
    for source in [
        ADJOINT.as_str().to_owned(),
        ADJOINT.as_str().replace("observe fn m", "fn m"),
    ] {
        let start = source.find("adjoint(m)").unwrap() + "adjoint(".len();
        refusal(
            &source,
            "type_mismatch",
            Span::new(start, start + 1),
            "inferred body effect Unitary; measurement cannot satisfy this obligation",
        );
    }
}

#[test]
fn endomorphic_observing_provider_still_reports_its_inferred_effect() {
    let source = "use std::state::init0;\x20
        fn m(q:Q<Bit>)->Q<Bit>{let b=measure_z(q); init0()}
        fn client(q:Q<Bit>)->Q<Bit>{adjoint(m)(q)}";
    let start = source.find("adjoint(m)").unwrap() + "adjoint(".len();
    refusal(
        source,
        "effect",
        Span::new(start, start + 1),
        "checked effect in the caller's module must be Unitary",
    );
}

#[test]
fn missing_else_points_at_its_if_including_static_nested_and_eof_cases() {
    for (source, marker) in [
        (MISSING_ELSE.as_str(), "if m"),
        ("fn f()->Bit{if static 1 == 1 {1}}", "if static"),
        ("fn f()->Unit{if 1 {()} else {if 0 {()}}}", "if 0"),
        ("// 日本語\r\nfn f()->Unit{if 1 {()}", "if 1"),
    ] {
        let start = source.find(marker).unwrap();
        refusal(
            source,
            "parse",
            Span::new(start, start + 2),
            "`if` without `else` is unsupported",
        );
        assert!(
            parse_module(source)
                .unwrap_err()
                .message
                .contains("else { () }")
        );
    }
}

#[test]
fn qualified_expression_paths_suggest_the_actual_import_at_the_original_path() {
    for path in [
        "std::observe::measure_z",
        "helper::nested::f",
        "std::classical::parity",
    ] {
        let source = QUALIFIED.replace("std::observe::measure_z", path);
        let start = source.find(path).unwrap();
        refusal(
            &source,
            "parse",
            Span::new(start, start + path.len()),
            &format!("import the function with `use {path};`"),
        );
    }
}

#[test]
fn incomplete_qualified_paths_do_not_suggest_importing_a_module_as_a_function() {
    for path in ["std::", "std::observe::", "helper::nested::"] {
        let source = format!("fn f()->Bit{{{path}}}");
        let error = parse_module(&source).unwrap_err();
        assert!(
            error
                .message
                .contains("use a complete `use module::function;` import")
        );
        assert_eq!(&source[error.span.start..error.span.end], path);
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn explicit_static_else_executes_only_the_selected_ordinary_arm() {
    for (predicate, expected) in [("1 == 1", true), ("1 == 0", false)] {
        let source = format!("observe fn main()->Bit{{if static {predicate} {{1}} else {{0}}}}");
        ParsedProgram::parse(BTreeMap::from([("main".into(), source.clone())])).unwrap();
        let program = compile_project(&SourceRoot::new(&source).0).unwrap();
        let outcomes =
            qleisli::sim::run_closed(&program, qleisli::sim::SimulationLimits::default()).unwrap();
        assert_eq!(
            outcomes,
            BTreeMap::from([(vec![expected], 1.0)]),
            "{source}"
        );
    }
}

#[test]
fn live_quantum_rebinding_quotes_the_owner_and_keeps_the_ownership_refusal() {
    let start = REBIND.as_str().rfind("let a").unwrap() + 4;
    refusal(
        REBIND.as_str(),
        "ownership",
        Span::new(start, start + 1),
        "binding `a` would drop a live quantum owner",
    );
}

#[test]
fn source_refusals_use_one_category_in_cli_text_and_json() {
    for (source, code) in [
        (MISSING_ELSE.as_str(), "parse"),
        (QUALIFIED, "parse"),
        (REBIND.as_str(), "ownership"),
    ] {
        let root = SourceRoot::new(source);
        for json in [false, true] {
            let mut command = Command::new(env!("CARGO_BIN_EXE_qleisli"));
            command.arg("check").arg(&root.0);
            if json {
                command.arg("--format=json");
            }
            let output = command.output().unwrap();
            assert_eq!(output.status.code(), Some(1));
            let text = String::from_utf8(if json { output.stdout } else { output.stderr }).unwrap();
            let marker = if json {
                format!("\"code\":\"{code}\"")
            } else {
                format!(": {code}: ")
            };
            assert_eq!(text.matches(&marker).count(), 1, "{text}");
            assert!(!text.contains("parse error:"), "{text}");
        }
    }
}

#[cfg(unix)]
#[test]
fn selected_native_rejections_keep_one_category_and_fail_closed_in_text_and_json() {
    use std::os::unix::fs::PermissionsExt;
    let root = SourceRoot::new("observe fn main()->Bit{1}");
    let checker = root.0.join("rejecting-checker");
    for code in ["invalid_ir", "limit"] {
        std::fs::write(&checker, format!(
            "#!/bin/sh\ncat >/dev/null\nprintf 'qleisli.qirf-native 2\\nerror\\n{code}\\n'\nexit 1\n"
        )).unwrap();
        std::fs::set_permissions(&checker, std::fs::Permissions::from_mode(0o700)).unwrap();
        for json in [false, true] {
            let mut command = Command::new(env!("CARGO_BIN_EXE_qleisli"));
            command
                .arg("check")
                .arg(&root.0)
                .arg(format!("--lean-kernel={}", checker.display()));
            if json {
                command.arg("--format=json");
            }
            let output = command.output().unwrap();
            assert_eq!(output.status.code(), Some(1));
            let text = String::from_utf8(if json { output.stdout } else { output.stderr }).unwrap();
            let marker = if json {
                format!("\"code\":\"{code}\"")
            } else {
                format!(": {code}: ")
            };
            assert_eq!(text.matches(&marker).count(), 1, "{text}");
            assert!(text.contains("Lean native checker rejected the artifact/request; no fallback while checking main::main"), "{text}");
            if json {
                assert!(!text.contains(&format!("{code}: Lean")), "{text}");
            }
        }
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn explicit_else_imports_and_inferred_unitary_adjoint_still_execute() {
    let imports = "use std::state::init0; use std::gate::x; ";
    for source in [
        MISSING_ELSE
            .as_str()
            .replace("if m { x(excl r); }", "if m { x(excl r); () } else { () };"),
        QUALIFIED
            .replace("std::observe::measure_z(init0())", "measure_z(init0())")
            .replace("use std::quantum::init0;", "use std::state::init0;"),
        format!(
            "{imports} observe fn m(q:Q<Bit>)->Q<Bit>{{x(q)}} observe fn main()->Bit{{measure_z(adjoint(m)(init0()))}}"
        ),
    ] {
        let root = SourceRoot::new(&source);
        let program = compile_project(&root.0).unwrap();
        let outcomes =
            qleisli::sim::run_closed(&program, qleisli::sim::SimulationLimits::default()).unwrap();
        let expected = if source.contains("adjoint(m)") {
            vec![true]
        } else if source.contains("if m") {
            vec![false, false]
        } else {
            vec![false]
        };
        // Ordinary H Z H is numerical here; retain every ordered outcome and
        // check any mathematical-zero tail with the existing engineering bound.
        assert_eq!(expected.len(), program.raw().classical_outputs.len());
        let probability = outcomes.get(&expected).expect("expected ordered output");
        assert!((probability - 1.0).abs() < 1e-12, "{source}");
        for (bits, probability) in &outcomes {
            let requested = if bits == &expected { 1.0 } else { 0.0 };
            assert_eq!(bits.len(), expected.len());
            assert!(probability.is_finite() && *probability >= 0.0);
            assert!((probability - requested).abs() < 1e-12, "{source}");
        }
        assert!((outcomes.values().sum::<f64>() - 1.0).abs() < 1e-12);
    }
}
