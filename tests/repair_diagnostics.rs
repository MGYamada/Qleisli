//! Diagnostic text and locations assist repair; schemas and rejection stay intact.
mod common;
use common::{SourceRoot, current_namespace_fixture};
use qleisli::frontend::compile::{check_project, check_project_diagnostic, compile_project};
use qleisli::sim::{SimulationLimits, run_closed};
use std::{fs, path::Path, process::Command};

fn fixture(name: &str) -> String {
    fs::read_to_string(current_namespace_fixture(
        &Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/frontend_v030/ordinary-type-cutover/current/repair_diagnostics")
            .join(format!("{name}.qli")),
    ))
    .unwrap()
}

#[test]
fn effect_errors_locate_the_strongest_cause_and_name_both_effects() {
    for (source, cause, derived, asserted) in [
        (
            "\nunitary fn bad(q:Q<Bit>)->Bit{measure_z(q)}",
            "measure_z(q)",
            "Observe",
            "Unitary",
        ),
        (
            "use std::state::init0; \nunitary fn bad()->Bit{measure_z(init0())}",
            "measure_z(init0())",
            "Observe",
            "Unitary",
        ),
        (
            "use std::state::init0;\nunitary fn bad()->Q<Bit>{init0()}",
            "init0()",
            "Isometry",
            "Unitary",
        ),
        (
            "unitary fn bad(q:Q<Bit>)->Q<(Bit,Bit)>{basis q as x { (x,x) }}",
            "basis q as x { (x,x) }",
            "Isometry",
            "Unitary",
        ),
        (
            "use std::state::init0;\x20
             fn strong()->Unit{let b=measure_z(init0());()} fn weak()->Unit{()}
             isometry fn bad()->Unit{strong(); weak()}",
            "strong()",
            "Observe",
            "Isometry",
        ),
        (
            "use std::state::init0;\x20
             fn strong()->Unit{let b=measure_z(init0());()} isometry fn bad()->Unit{if 0 {strong()} else {()}}",
            "strong()",
            "Observe",
            "Isometry",
        ),
        (
            "use std::state::init0;\x20
             fn strong()->Unit{let b=measure_z(init0());()} isometry fn bad()->Unit{if 1 {()} else {strong()}}",
            "strong()",
            "Observe",
            "Isometry",
        ),
        (
            "use std::state::init0;\x20
             fn strong()->Bit{measure_z(init0())} isometry fn bad()->Unit{if strong() {()} else {()}}",
            "strong()",
            "Observe",
            "Isometry",
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
            error.message.contains(&format!("asserted `{asserted}`")),
            "{error:?}"
        );
        assert!(error.message.contains("\"externally unitary\" is not supported"));
        assert!(!error.message.contains("github.com"));
        let location = error.primary.unwrap();
        let start = source.rfind(cause).unwrap();
        assert_eq!(
            (location.span.start, location.span.end),
            (start, start + cause.len()),
            "{source}"
        );
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn imported_effects_point_to_the_callers_call_in_text_and_json() {
    let source = "// 日本語\r\nuse helper::strong;\r\nisometry fn bad()->Unit{strong()}";
    let root = SourceRoot::new(source);
    root.write(
        "helper.qli",
        "use std::state::init0;\x20
         pub observe fn strong()->Unit{let b=measure_z(init0());()}",
    );
    let error = check_project_diagnostic(&root.0).unwrap_err();
    let location = error.primary.unwrap();
    assert_eq!(
        location.path,
        root.0.join("main.qli").canonicalize().unwrap()
    );
    assert_eq!(location.span.start, source.rfind("strong()").unwrap());
    assert_eq!((location.line, location.column), (3, 25));
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
            text.contains("body effect `Observe` exceeds asserted `Isometry`"),
            "{text}"
        );
        if json {
            assert!(text.contains("\"path\":\"main.qli\""), "{text}");
            assert!(text.contains("\"line\":3,\"column\":25"), "{text}");
        }
    }
    root.write("main.qli", &source.replace("isometry fn", "observe fn"));
    check_project(&root.0).unwrap();
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn ordinary_gate_providers_and_language_primitive_hints_have_checked_rewrites() {
    let root = SourceRoot::new("use std::state::init0;");
    check_project(&root.0).unwrap();
    for gate in ["x", "z", "t"] {
        let source = format!(
            "use std::gate::{gate};
             unitary fn apply[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){{U(q)}}
             unitary fn client(q:Q<Bit>)->Q<Bit>{{apply[{gate}](q)}}"
        );
        root.write("main.qli", &source);
        check_project(&root.0).unwrap();
    }
    let source = "unitary fn apply[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}
        unitary fn client(q:Q<Bit>)->Q<Bit>{apply[h](q)}";
    root.write("main.qli", source);
    let error = check_project_diagnostic(&root.0).unwrap_err();
    assert_eq!(error.code, "type_mismatch");
    let wrapper = "fn wrapped_gate(q: Q<Bit>) -> Q<Bit> { h(q) }";
    assert!(error.message.contains(wrapper), "{error:?}");
    let location = error.primary.unwrap();
    assert_eq!(&source[location.span.start..location.span.end], "h");
    root.write(
        "main.qli",
        &format!("{}\n{wrapper}", source.replace("[h]", "[wrapped_gate]")),
    );
    check_project(&root.0).unwrap();
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn snapshot_limit_errors_explain_the_retained_sources() {
    for body in ["apply[p](q)", "apply_contract(p,p,q)"] {
        let source = format!(
            "unitary fn p(q:Q<Bit>)->Q<Bit>{{q}}
             unitary fn apply[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){{U(q)}}
             unitary fn client(q:Q<Bit>)->Q<Bit>{{{body}}}"
        );
        let root = SourceRoot::new(&source);
        check_project(&root.0).unwrap();
        let comments = format!("// {}", "a".repeat(1_000_000));
        root.write("unrelated.qli", &comments);
        check_project(&root.0).unwrap();
        // The same original bytes matter when they belong to the actual provider.
        // Relevant bytes are never stripped or allowed to bypass the work bound.
        root.write("main.qli", &format!("{source}\n{comments}"));
        let error = check_project_diagnostic(&root.0).unwrap_err();
        assert_eq!(error.code, "limit", "{error:?}");
        assert!(
            error.message.contains("relevant source closure"),
            "{error:?}"
        );
        assert!(error.message.contains("charged once"), "{error:?}");
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
        ("branch_result", "Bit", "Unit"),
        ("primitive", "Q<Bit>", "Bit"),
        ("zero_width", "Q<Bit>", "Q<Unit>"),
        ("condition", "Bit", "Q<Bit>"),
        ("boolean", "Bit", "Q<Unit>"),
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

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn argument_types_reach_text_and_json_without_moving_the_callers_span() {
    let source = "// 日本語\r\nuse std::transform::qft3;\r\nunitary fn bad(q:Q<(Bit,(Bit,Bit))>) -> Q<(Bit,(Bit,Bit))> { qft3(q) }";
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

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn cleanup_hint_has_a_working_repair_but_cannot_authorize_a_false_contract() {
    let original = fs::read_to_string(current_namespace_fixture(
        &Path::new(env!("CARGO_MANIFEST_DIR")).join(
            "tests/fixtures/frontend_v030/ordinary-type-cutover/current/qli_authoring/rejected/auxiliary_hh.qli",
        ),
    ))
    .unwrap();
    // The unchanged historical H H body now has an exact native identity
    // equation. Use a separately authored non-diagonal body for the hint.
    check_project_diagnostic(&SourceRoot::new(&original).0).unwrap();
    assert!(original.contains("h(h(flag))"));
    let unsupported = original.replace("h(h(flag))", "h(flag)");
    let root = SourceRoot::new(&unsupported);
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
    assert!(unsupported[location.span.start..location.span.end].contains("h(flag)"));
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
        &fs::read_to_string(current_namespace_fixture(
            &Path::new(env!("CARGO_MANIFEST_DIR")).join(
                "tests/fixtures/frontend_v030/ordinary-type-cutover/current/qli_authoring/accepted/auxiliary_hh.qli",
            ),
        ))
        .unwrap(),
    );
    let program = compile_project(&root.0).unwrap();
    let result = run_closed(&program, SimulationLimits::default()).unwrap();
    assert!((result.get(&vec![false]).unwrap() - 1.0).abs() < 1e-12);
    root.write("main.qli", &fixture("false_cleanup"));
    let error = check_project_diagnostic(&root.0).unwrap_err();
    assert_eq!(error.code, "invalid_ir");
    assert!(error.message.contains("U E_in = E_out u"), "{error:?}");
}

#[test]
fn ordinary_comparison_refusals_explain_quantum_relations_at_the_operator() {
    use qleisli::frontend::parser::parse_module;

    for ty in [
        "Q<Bit>",
        "Q<Unit>",
        "Q<Bits<0>>",
        "(Bit,(Q<Unit>,Unit))",
        "Bit",
    ] {
        for operator in ["==", "!=", "<", "<=", ">", ">="] {
            let source =
                format!("// 日本語\r\npub fn compare(a:{ty},b:{ty})->Bit{{a {operator} b}}");
            let parsed = parse_module(&source).unwrap_err();
            let start = source.rfind(&format!(" {operator} ")).unwrap() + 1;
            assert_eq!(
                (parsed.span.start, parsed.span.end),
                (start, start + operator.len())
            );
            assert!(
                parsed
                    .message
                    .starts_with(&format!("ordinary runtime comparison `{operator}`"))
            );
            for distinction in [
                "ordinary Bits",
                "Static Nat",
                "If an operand contains live Q<T>",
                "nested and zero-width",
                "Owner/provenance identity",
                "wire identity",
                "explicit reversible operation",
                "tomography",
            ] {
                assert!(parsed.message.contains(distinction), "{parsed:?}");
            }
            let finite = check_project_diagnostic(&SourceRoot::new(&source).0).unwrap_err();
            assert!(finite.message.contains(&parsed.message), "{finite:?}");
            assert_eq!(finite.primary.unwrap().span, parsed.span);
        }
    }
}

#[test]
fn unresolved_hash_teaching_does_not_inspect_arguments_or_mask_resolution() {
    use qleisli::frontend::compile::ParsedProgram;
    use std::collections::BTreeMap;

    for ty in [
        "Bit",
        "Q<Bit>",
        "Q<Unit>",
        "Q<Bits<0>>",
        "(Bit,(Q<Unit>,Unit))",
    ] {
        // Even an invalid argument expression must not replace the original
        // unresolved-callee failure with a guessed type/ownership judgment.
        for argument in ["q", "not q"] {
            let source = format!("pub fn client(q:{ty})->Bit{{hash({argument})}}");
            let common = ParsedProgram::parse(
                qleisli::edition::Edition::E2026,
                BTreeMap::from([("main".into(), source.clone())]),
            )
            .unwrap_err();
            assert_eq!(common.code(), "name");
            assert!(common.message().starts_with("unresolved function hash;"));
            assert!(common.message().contains("If a value contains live Q<T>"));
            assert!(common.message().contains("tomography"));
            let finite = check_project_diagnostic(&SourceRoot::new(&source).0).unwrap_err();
            assert_eq!(finite.code, "unknown_name");
            assert_eq!(finite.message, common.message());
            let span = finite.primary.unwrap().span;
            assert_eq!(&source[span.start..span.end], "hash");
        }
    }
    for (source, expected) in [
        (
            "pub fn client(q:Bit)->Bit{missing(q)}",
            "unresolved function missing",
        ),
        (
            "fn hash(q:Bit)->Bit{q} pub fn client()->Bit{let hash=0;hash()}",
            "a local value is not callable",
        ),
    ] {
        let error = check_project_diagnostic(&SourceRoot::new(source).0).unwrap_err();
        assert_eq!(error.message, expected);
        assert!(!error.message.contains("built-in ordinary hash"));
    }
}

#[test]
fn comparison_teaching_preserves_static_predicates_and_exact_type_delimiters() {
    use qleisli::frontend::compile::ParsedProgram;
    use std::collections::BTreeMap;

    for operator in ["==", "!=", "<", "<=", ">", ">="] {
        let source = format!(
            "pub unitary fn guarded[const N:Nat](q:Q<(Bit,(Unit,Bit))>)->Q<(Bit,(Unit,Bit))> \
             requires N {operator} 1 {{if static N {operator} 1 {{q}} else {{q}}}}"
        );
        ParsedProgram::parse(
            qleisli::edition::Edition::E2026,
            BTreeMap::from([("main".into(), source)]),
        )
        .unwrap();
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn explicit_comparisons_and_resolved_hash_functions_keep_their_checked_actions() {
    for source in [
        "classical fn equal(a:Bit,b:Bit)->Bit{not(a xor b)} \
         pub fn main()->Bit{if static 1<2 {equal(0,0)} else {equal(0,1)}}",
        "use std::state::init0; unitary fn hash(q:Q<Bit>)->Q<Bit>{q} \
         pub observe fn main()->Bit{measure_z(hash(init0()))}",
        "classical fn hash(b:Bit)->Bit{b} pub fn main()->Bit{hash(1)}",
    ] {
        check_project(&SourceRoot::new(source).0).unwrap();
    }
    let imported = SourceRoot::new(
        "use std::state::init0; use helper::hash; \
         pub observe fn main()->Bit{measure_z(helper::hash(hash(init0())))}",
    );
    imported.write("helper.qli", "pub unitary fn hash(q:Q<Bit>)->Q<Bit>{q}");
    check_project(&imported.0).unwrap();

    // This reversible operation computes equality of basis labels into its
    // second output. It neither compares unknown states nor exposes owner IDs.
    let root = SourceRoot::new(
        "use std::state::init0; \
         unitary fn coherent_equal(q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>{ \
             basis q as (a,b){(a,not(a xor b))} } \
         pub observe fn main()->(Bit,Bit){ \
             let(a,b)=split(coherent_equal(join(init0(),init0()))); \
             (measure_z(a),measure_z(b))}",
    );
    let program = compile_project(&root.0).unwrap();
    let output = run_closed(&program, SimulationLimits::default()).unwrap();
    assert_eq!(output.len(), 1);
    assert!((output[&vec![false, true]] - 1.0).abs() < 1e-12);
}
