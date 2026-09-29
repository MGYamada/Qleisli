//! Diagnostic text and locations assist repair; schemas and rejection stay intact.
mod common;
use common::SourceRoot;
use qleisli_core::frontend::compile::{check_project, check_project_diagnostic, compile_project};
use qleisli_core::sim::{SimulationLimits, run_closed};
use std::{fs, path::Path, process::Command};

fn fixture(name: &str) -> String {
    fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/repair_diagnostics")
            .join(format!("{name}.qli")),
    )
    .unwrap()
}

#[test]
fn effect_errors_locate_the_strongest_cause_and_name_both_effects() {
    for (source, cause, derived, declared) in [
        (
            "use std::observe::measure_z;\nunitary fn bad(q:Q<Bit>)->CBit{measure_z(q)}",
            "measure_z(q)",
            "Observe",
            "Unitary",
        ),
        (
            "use std::quantum::init0; use std::observe::measure_z;\nunitary fn bad()->CBit{measure_z(init0())}",
            "measure_z(init0())",
            "Observe",
            "Unitary",
        ),
        (
            "use std::quantum::init0;\nunitary fn bad()->Q<Bit>{init0()}",
            "init0()",
            "Iso",
            "Unitary",
        ),
        (
            "unitary fn bad(q:Q<Bit>)->Q<(Bit,Bit)>{do x <- q; pure (x,x)}",
            "do x <- q; pure (x,x)",
            "Iso",
            "Unitary",
        ),
        (
            "observe fn strong()->Unit{()} unitary fn weak()->Unit{()}
             iso fn bad()->Unit{strong(); weak()}",
            "strong()",
            "Observe",
            "Iso",
        ),
        (
            "observe fn strong()->Unit{()} iso fn bad()->Unit{if false {strong()} else {()}}",
            "strong()",
            "Observe",
            "Iso",
        ),
        (
            "observe fn strong()->Unit{()} iso fn bad()->Unit{if true {()} else {strong()}}",
            "strong()",
            "Observe",
            "Iso",
        ),
        (
            "observe fn strong()->CBit{true} iso fn bad()->Unit{if strong() {()} else {()}}",
            "strong()",
            "Observe",
            "Iso",
        ),
    ] {
        let root = SourceRoot::new(source);
        let error = check_project_diagnostic(&root.0).unwrap_err();
        assert_eq!(error.code, "effect", "{error:?}");
        assert!(
            error.message.contains(&format!("body effect `{derived}`")),
            "{error:?}"
        );
        assert!(
            error.message.contains(&format!("declared `{declared}`")),
            "{error:?}"
        );
        let location = error.primary.unwrap();
        let start = source.rfind(cause).unwrap();
        assert_eq!(
            (location.span.start, location.span.end),
            (start, start + cause.len()),
            "{source}"
        );
    }
}

#[test]
fn imported_effects_point_to_the_callers_call_in_text_and_json() {
    let source = "// 日本語\r\nuse helper::strong;\r\niso fn bad()->Unit{strong()}";
    let root = SourceRoot::new(source);
    root.write("helper.qli", "pub observe fn strong()->Unit{()}");
    let error = check_project_diagnostic(&root.0).unwrap_err();
    let location = error.primary.unwrap();
    assert_eq!(
        location.path,
        root.0.join("main.qli").canonicalize().unwrap()
    );
    assert_eq!(location.span.start, source.rfind("strong()").unwrap());
    assert_eq!((location.line, location.column), (3, 20));
    for json in [false, true] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_qleisli"));
        command.arg("check").arg(&root.0);
        if json {
            command.arg("--format=json");
        }
        let output = command.output().unwrap();
        assert_eq!(output.status.code(), Some(1));
        let text = String::from_utf8(if json { output.stdout } else { output.stderr }).unwrap();
        assert!(
            text.contains("body effect `Observe` exceeds declared `Iso`"),
            "{text}"
        );
        if json {
            assert!(text.contains("\"path\":\"main.qli\""), "{text}");
            assert!(text.contains("\"line\":3,\"column\":20"), "{text}");
        }
    }
    root.write("main.qli", &source.replace("iso fn", "observe fn"));
    check_project(&root.0).unwrap();
}

#[test]
fn grouped_import_and_gate_provider_hints_have_checked_rewrites() {
    let root = SourceRoot::new("use std::quantum::{init0, h};");
    let error = check_project_diagnostic(&root.0).unwrap_err();
    assert_eq!(error.code, "parse");
    assert!(error.message.contains("grouped imports are unsupported"));
    let imports = "use std::quantum::init0; use std::quantum::h;";
    assert!(error.message.contains(imports));
    let location = error.primary.unwrap();
    assert_eq!((location.span.start, location.span.end), (18, 19));
    root.write("main.qli", imports);
    check_project(&root.0).unwrap();

    for gate in ["h", "x", "z", "t"] {
        let source = format!(
            "use std::quantum::{gate};
            unitary fn apply[static U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Apply(U){{U(q)}}
            unitary fn client(q:Q<Bit>)->Q<Bit>{{apply[{gate}](q)}}"
        );
        root.write("main.qli", &source);
        let error = check_project_diagnostic(&root.0).unwrap_err();
        assert_eq!(error.code, "type_mismatch");
        let wrapper = format!("unitary fn wrapped_gate(q: Q<Bit>) -> Q<Bit> {{ {gate}(q) }}");
        assert!(error.message.contains(&wrapper), "{error:?}");
        let location = error.primary.unwrap();
        assert_eq!(&source[location.span.start..location.span.end], gate);
        root.write(
            "main.qli",
            &format!(
                "{}\n{wrapper}",
                source.replace(&format!("[{gate}]"), "[wrapped_gate]")
            ),
        );
        check_project(&root.0).unwrap();
    }
}

#[test]
fn snapshot_limit_errors_explain_the_retained_sources() {
    for body in ["apply[p](q)", "apply_contract(p,p,q)"] {
        let root = SourceRoot::new(&format!(
            "unitary fn p(q:Q<Bit>)->Q<Bit>{{q}}
             unitary fn apply[static U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Apply(U){{U(q)}}
             unitary fn client(q:Q<Bit>)->Q<Bit>{{{body}}}"
        ));
        check_project(&root.0).unwrap();
        // This file alone exceeds the existing shared work budget when copied.
        // A020-10 removes repeated copies, not the bounded initial snapshot.
        root.write("unrelated.qli", &format!("// {}", "a".repeat(1_000_000)));
        let error = check_project_diagnostic(&root.0).unwrap_err();
        assert_eq!(error.code, "limit", "{error:?}");
        assert!(
            error.message.contains("shared project snapshot"),
            "{error:?}"
        );
        assert!(error.message.contains("charged once"), "{error:?}");
        assert!(
            error
                .message
                .contains("all loaded modules, comments and bundled std"),
            "{error:?}"
        );
    }
}

#[test]
fn concrete_mismatches_show_expected_and_actual_exact_types() {
    for (name, expected, actual) in [
        ("ordinary_return", "(Q<Bit>,Unit)", "Q<Bit>"),
        ("basis_return", "(Bit,(Bit,Bit))", "(Bit,Bit,Bit)"),
        ("basis_argument", "(Unit,Bit)", "Bit"),
        ("static_argument", "Op<Bit>", "Op<(Bit,Bit)>"),
        ("static_composition", "Op<Bit>", "Op<(Bit,Bit)>"),
        ("static_input", "Q<Bit>", "Q<(Bit,Bit)>"),
        ("branch_result", "CBit", "Unit"),
        ("primitive", "Q<Bit>", "CBit"),
        ("zero_width", "Q<Bit>", "Q<Unit>"),
        ("condition", "CBit", "Q<Bit>"),
        ("boolean", "CBit", "Q<Unit>"),
        ("predicate", "Bit -> Bit", "Unit -> Bit"),
        ("certified_predicate", "Bit -> Bit", "Unit -> Bit"),
    ] {
        let root = SourceRoot::new(&fixture(name));
        let error = check_project_diagnostic(&root.0).unwrap_err();
        assert_eq!(error.code, "type_mismatch", "{name}: {error:?}");
        assert!(
            error.message.contains(&format!("expected `{expected}`")),
            "{name}: {error:?}"
        );
        assert!(
            error.message.contains(&format!("found `{actual}`")),
            "{name}: {error:?}"
        );
        assert!(error.primary.is_some(), "{name}: {error:?}");
    }
}

#[test]
fn argument_types_reach_text_and_json_without_moving_the_callers_span() {
    let source = "// 日本語\r\nuse std::transforms::qft3;\r\nunitary fn bad(q:Q<(Bit,(Bit,Bit))>) -> Q<(Bit,(Bit,Bit))> { qft3(q) }";
    let root = SourceRoot::new(source);
    let error = check_project_diagnostic(&root.0).unwrap_err();
    let location = error.primary.unwrap();
    let argument = source.rfind("(q)").unwrap() + 1;
    assert_eq!(
        (location.span.start, location.span.end),
        (argument, argument + 1)
    );
    assert_eq!(location.line, 3);
    assert_eq!(
        location.column,
        source[..argument]
            .rsplit('\n')
            .next()
            .unwrap()
            .chars()
            .count()
            + 1
    );
    for json in [false, true] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_qleisli"));
        command.arg("check").arg(&root.0);
        if json {
            command.arg("--format=json");
        }
        let output = command.output().unwrap();
        assert_eq!(output.status.code(), Some(1));
        let text = String::from_utf8(if json { output.stdout } else { output.stderr }).unwrap();
        assert!(
            text.contains("expected `Q<((Bit,Bit),Bit)>`, found `Q<(Bit,(Bit,Bit))>`"),
            "{text}"
        );
        if json {
            assert!(text.contains("\"code\":\"type_mismatch\""), "{text}");
            assert!(text.contains("\"related\":[]"), "{text}");
        }
    }
}

#[test]
fn cleanup_hint_has_a_working_repair_but_cannot_authorize_a_false_contract() {
    let original = include_str!("fixtures/qli_authoring/rejected/auxiliary_hh.qli");
    let root = SourceRoot::new(original);
    let error = check_project_diagnostic(&root.0).unwrap_err();
    assert_eq!(error.code, "unsupported");
    assert!(
        error
            .message
            .contains("with_computed(source, predicate, logical) { |data, ancilla| ... }")
    );
    assert!(error.message.contains("return both owners"));
    assert!(error.message.contains("does not bypass cleanup checking"));
    let location = error.primary.unwrap();
    assert!(original[location.span.start..location.span.end].contains("h(h(flag))"));
    for json in [false, true] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_qleisli"));
        command.arg("check").arg(&root.0);
        if json {
            command.arg("--format=json");
        }
        let output = command.output().unwrap();
        assert_eq!(output.status.code(), Some(1));
        let text = String::from_utf8(if json { output.stdout } else { output.stderr }).unwrap();
        assert!(text.contains("return both owners"), "{text}");
    }
    root.write(
        "main.qli",
        include_str!("fixtures/qli_authoring/accepted/auxiliary_hh.qli"),
    );
    let program = compile_project(&root.0).unwrap();
    let result = run_closed(&program, SimulationLimits::default()).unwrap();
    assert!((result.get(&vec![false]).unwrap() - 1.0).abs() < 1e-12);
    root.write("main.qli", &fixture("false_cleanup"));
    let error = check_project_diagnostic(&root.0).unwrap_err();
    assert_eq!(error.code, "invalid_ir");
    assert!(error.message.contains("U E_in = E_out u"), "{error:?}");
}
