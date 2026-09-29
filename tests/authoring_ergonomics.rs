//! Author-written source exercises; no additional IR rule or evidence authority.
mod common;

use common::SourceRoot;
use qleisli::frontend::ast::{FnBody, PatternKind, TypeKind};
use qleisli::frontend::compile::{check_project_diagnostic, compile_project};
use qleisli::frontend::documentation::render_markdown;
use qleisli::frontend::parser::parse_module;
use qleisli::sim::{SimulationLimits, run_closed};
use std::fs;
use std::path::Path;

fn source(name: &str) -> String {
    fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/ergonomics")
            .join(format!("{name}.qli")),
    )
    .unwrap()
}

#[test]
fn patterned_basis_contracts_and_nary_clients_execute() {
    for (name, bits) in [
        ("permutation", vec![false, true]),
        ("multi_parameter", vec![true, false]),
        ("tuple_evaluation", vec![true, false, true]),
        ("nary_lift", vec![false, true, false]),
    ] {
        let root = SourceRoot::new(&source(name));
        let program = compile_project(&root.0).unwrap_or_else(|e| panic!("{name}: {e}"));
        let result = run_closed(&program, SimulationLimits::default()).unwrap();
        assert!((result.values().sum::<f64>() - 1.0).abs() < 1e-12);
        assert!(
            (result.get(&bits).copied().unwrap_or_default() - 1.0).abs() < 1e-12,
            "{name}: {result:?}"
        );
    }
}

#[test]
fn pattern_arity_totality_ownership_and_exact_tree_guards_remain() {
    for (name, code) in [
        ("duplicate_pattern", "ownership"),
        ("duplicate_across_parameters", "ownership"),
        ("pattern_shape", "type_mismatch"),
        ("unit_pattern_shape", "type_mismatch"),
        ("unused_pattern_shape", "type_mismatch"),
        ("basis_capture", "unknown_name"),
        ("basis_call_arity", "arity"),
        ("basis_value_not_callable", "type_mismatch"),
        ("ordinary_parameter_pattern", "parse"),
        ("wildcard_not_injective", "ownership"),
        ("nary_duplicate_owner", "ownership"),
        ("nary_duplicate_binding", "ownership"),
        ("unit_owner_wildcard", "ownership"),
        ("flat_is_not_balanced", "type_mismatch"),
        ("phase_mismatch", "contract"),
    ] {
        let root = SourceRoot::new(&source(name));
        let error = check_project_diagnostic(&root.0).unwrap_err();
        assert_eq!(error.code, code, "{name}: {error:?}");
    }
}

#[test]
fn missing_owners_point_to_the_actual_binding_including_shadowing_and_auxiliaries() {
    for (name, needle, binding) in [
        ("dropped_parameter", "unused: Q<Bit>", "unused"),
        ("dropped_nested", "b,c)", "b"),
        ("dropped_shadow", "b = init0()", "b"),
        ("dropped_unit", "token = q", "token"),
        ("dropped_auxiliary", "scratch|", "scratch"),
    ] {
        // Verify both byte spans and scalar coordinates through UTF-8/CRLF.
        for prefix in ["", "// 日本語 🦀\r\n"] {
            let source = format!("{prefix}{}", source(name));
            let root = SourceRoot::new("");
            // Other project modules must report their own binding path.
            root.write("implementation.qli", &source);
            let error = check_project_diagnostic(&root.0).unwrap_err();
            assert_eq!(error.code, "ownership", "{name}: {error:?}");
            let location = error.primary.as_ref().unwrap();
            let start = source.find(needle).unwrap();
            assert_eq!(
                location.path,
                root.0.join("implementation.qli").canonicalize().unwrap()
            );
            assert_eq!(
                (location.span.start, location.span.end),
                (start, start + binding.len()),
                "{name}: {error:?}"
            );
            assert_eq!(
                location.line,
                source[..start].bytes().filter(|&b| b == b'\n').count() + 1
            );
            assert_eq!(
                location.column,
                source[..start].rsplit('\n').next().unwrap().chars().count() + 1
            );
        }
    }
}

#[test]
fn corpus_dropped_owner_now_points_to_b_not_the_body() {
    let source = include_str!("fixtures/qli_authoring/rejected/dropped_owner.qli");
    let root = SourceRoot::new(source);
    let error = check_project_diagnostic(&root.0).unwrap_err();
    let location = error.primary.as_ref().unwrap();
    assert_eq!(error.code, "ownership");
    assert_eq!((location.line, location.column), (4, 9));
    assert_eq!(&source[location.span.start..location.span.end], "b");
}

#[test]
fn nary_patterns_types_and_basis_values_preserve_immediate_arity() {
    let source = "basis fn rotate((a,b,c): (Bit,Bit,Bit)) -> (Bit,Bit,Bit) { (c,a,b) }";
    let ast = parse_module(source).unwrap();
    let param = &ast.decls[0].params[0];
    assert_eq!(
        &source[param.pattern.span.start..param.pattern.span.end],
        "(a,b,c)"
    );
    let PatternKind::Tuple(fields) = &param.pattern.kind else {
        panic!("tuple pattern")
    };
    assert_eq!(fields.len(), 3);
    assert!(matches!(&fields[0].kind, PatternKind::Name(name) if name.text == "a"));
    assert!(matches!(&fields[2].kind, PatternKind::Name(name) if name.text == "c"));
    let TypeKind::Tuple(fields) = &param.ty.kind else {
        panic!("tuple type")
    };
    assert_eq!(fields.len(), 3);
    assert!(
        fields
            .iter()
            .all(|field| matches!(field.kind, TypeKind::Bit))
    );
    let FnBody::Basis(body) = &ast.decls[0].body else {
        panic!("basis body")
    };
    assert_eq!(&source[body.span.start..body.span.end], "(c,a,b)");
    let document = render_markdown(&format!("/// Rotate a three-bit label.\n{source}")).unwrap();
    assert!(document.contains("(a,b,c): (Bit,Bit,Bit)"), "{document}");
    for bad in [
        "basis fn bad((a,b,): (Bit,Bit)) -> Bit { a }",
        "basis fn bad(a: (Bit,Bit,)) -> Bit { 0 }",
        "basis fn bad(a:Bit) -> (Bit,Bit,Bit) { (a,a,a,) }",
        "observe fn main() -> (CBit,CBit,CBit) { (false,false,true,) }",
    ] {
        assert!(parse_module(bad).is_err(), "{bad}");
    }
}

#[test]
fn flat_and_mixed_tuple_syntax_cannot_bypass_ast_depth_limits() {
    std::thread::Builder::new()
        .stack_size(2 * 1024 * 1024)
        .spawn(|| {
            for source in [
                format!(
                    "observe fn main() -> ({}) {{ () }}",
                    vec!["Unit"; 10_000].join(",")
                ),
                format!(
                    "observe fn main() -> Unit {{ ({}) }}",
                    vec!["()"; 10_000].join(",")
                ),
                format!(
                    "basis fn f() -> Unit {{ ({}) }}",
                    vec!["()"; 10_000].join(",")
                ),
                format!(
                    "basis fn f(({}):Unit) -> Unit {{ () }}",
                    vec!["_"; 10_000].join(",")
                ),
                format!(
                    "basis fn f(a:Bit) -> Unit {{ ((),(),{}) }}",
                    vec!["a"; 64].join(" xor ")
                ),
                format!(
                    "observe fn f(a:CBit) -> Unit {{ ((),(),{}) }}",
                    vec!["a"; 64].join(" xor ")
                ),
            ] {
                let error = parse_module(&source).unwrap_err();
                assert!(error.message.contains("limit"), "{error}");
            }
        })
        .unwrap()
        .join()
        .unwrap();
}
