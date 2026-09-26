use qleisli_core::frontend::ast::{BasisExprKind, ExprKind, FnBody, FnKind, StmtKind, TypeKind};
use qleisli_core::frontend::parser::parse_module;

#[test]
fn parses_bell_modules_and_keeps_owned_resource_syntax_distinct() {
    let bell = r#"
pub iso fn entangle(q: Q<Bit>) -> Q<(Bit, Bit)> {
    do x <- q;
    pure (x, x)
}
"#;
    let module = parse_module(bell).unwrap();
    assert_eq!(module.decls.len(), 1);
    let decl = &module.decls[0];
    assert!(decl.public);
    assert_eq!(decl.kind, FnKind::Iso);
    assert_eq!(decl.name.text, "entangle");
    assert!(matches!(decl.return_type.kind, TypeKind::Q(_)));
    let FnBody::Quantum(body) = &decl.body else {
        panic!("expected quantum body")
    };
    let ExprKind::CoherentLift {
        binder,
        input,
        basis,
    } = &body.result.kind
    else {
        panic!("expected coherent lift")
    };
    assert_eq!(binder.text, "x");
    assert!(matches!(input.kind, ExprKind::Name(_)));
    assert!(matches!(basis.kind, BasisExprKind::Tuple(_, _)));

    let main = r#"
use bell::entangle;
use std::quantum::h;
use std::quantum::init0;
use std::quantum::split;
use std::observe::measure_z;

observe fn main() -> (CBit, CBit) {
    let pair = entangle(h(init0()));
    let (left, right) = split(pair);
    let a = measure_z(left);
    let b = measure_z(right);
    (a, b)
}
"#;
    let module = parse_module(main).unwrap();
    assert_eq!(module.uses.len(), 5);
    assert_eq!(
        module.uses[0]
            .path
            .iter()
            .map(|part| part.text.as_str())
            .collect::<Vec<_>>(),
        ["bell", "entangle"]
    );
    assert_eq!(module.decls[0].kind, FnKind::Observe);
    let FnBody::Quantum(body) = &module.decls[0].body else {
        panic!("expected quantum body")
    };
    assert_eq!(body.statements.len(), 4);
    assert!(matches!(body.statements[1].kind, StmtKind::Let { .. }));
    assert!(matches!(body.result.kind, ExprKind::Tuple(_, _)));
}

#[test]
fn parses_phase_oracle_and_measurement_feedback() {
    let source = r#"
use std::quantum::z;
basis fn predicate(x: Bit) -> Bit { not x }
pub unitary fn phase_oracle(q: Q<Bit>) -> Q<Bit> {
    with_computed(q, predicate) { |a| z(a) }
}
observe fn feedback(q: Q<Bit>, r: Q<Bit>) -> (CBit, Q<Bit>) {
    let b = measure_z(q);
    let r1 = if b { x(r) } else { r };
    (b, r1)
}
"#;
    let module = parse_module(source).unwrap();
    assert_eq!(module.decls.len(), 3);
    assert_eq!(module.decls[0].kind, FnKind::Basis);
    assert!(matches!(module.decls[0].body, FnBody::Basis(_)));
    assert_eq!(module.decls[1].kind, FnKind::Unitary);
    let FnBody::Quantum(body) = &module.decls[1].body else {
        panic!("expected quantum body")
    };
    let ExprKind::WithComputed {
        source,
        function,
        binder,
        body,
    } = &body.result.kind
    else {
        panic!("expected structured computation")
    };
    assert!(matches!(source.kind, ExprKind::Name(_)));
    assert_eq!(function.text, "predicate");
    assert_eq!(binder.text, "a");
    assert!(matches!(body.result.kind, ExprKind::Call { .. }));

    let FnBody::Quantum(feedback) = &module.decls[2].body else {
        panic!("expected quantum body")
    };
    let StmtKind::Let { value, .. } = &feedback.statements[1].kind else {
        panic!("expected let")
    };
    assert!(matches!(value.kind, ExprKind::If { .. }));
}

#[test]
fn basis_operators_have_documented_precedence_and_left_associativity() {
    let module =
        parse_module("basis fn f(x: Bit, y: Bit, z: Bit) -> Bit { not x and y xor z xor 1 }")
            .unwrap();
    let FnBody::Basis(expr) = &module.decls[0].body else {
        panic!("expected basis body")
    };
    let BasisExprKind::Xor(first, last) = &expr.kind else {
        panic!("expected outer xor")
    };
    assert!(matches!(last.kind, BasisExprKind::Bit(true)));
    let BasisExprKind::Xor(left, right) = &first.kind else {
        panic!("expected left-associative xor")
    };
    assert!(matches!(right.kind, BasisExprKind::Name(_)));
    let BasisExprKind::And(first, _) = &left.kind else {
        panic!("expected and to bind tighter")
    };
    assert!(matches!(first.kind, BasisExprKind::Not(_)));
}

#[test]
fn accepts_comments_and_reports_utf8_byte_offsets() {
    let source = "// λ\niso fn f(q: Q<Bit>) -> Q<Bit> { q }";
    let module = parse_module(source).unwrap();
    let offset = source.find("iso").unwrap();
    assert_eq!(offset, 6);
    assert_eq!(module.decls[0].span.start, offset);
    assert_eq!(
        &source[module.decls[0].name.span.start..module.decls[0].name.span.end],
        "f"
    );
    let bad = "// λ\niso fn f(q: Q<Bit>) -> Q<Bit> { @ }";
    let error = parse_module(bad).unwrap_err();
    assert_eq!(error.span.start, bad.find('@').unwrap());
    assert_eq!(error.span.end, error.span.start + 1);
    assert!(error.message.contains("unexpected character"));
}

#[test]
fn malformed_syntax_has_precise_error_spans() {
    let cases = [
        ("use oracle::*;", "*", "unexpected character"),
        (
            "iso fn f(q: Q<Bit>) -> Q<Bit> { do x <- q; let y = x; pure y }",
            "let",
            "expected",
        ),
        ("basis fn f(x: CBit) -> Bit { x }", "CBit", "expected"),
        ("iso fn f(q: Q<Bit>) -> Q<Bit> {}", "}", "final expression"),
    ];
    for (source, at, message) in cases {
        let error = parse_module(source).unwrap_err();
        assert_eq!(error.span.start, source.find(at).unwrap(), "{source}");
        assert!(error.message.contains(message), "{error}");
    }
}

#[test]
fn deep_syntax_is_rejected_without_exhausting_the_stack() {
    let parentheses = format!(
        "iso fn f(q: Q<Bit>) -> Q<Bit> {{ {}q{} }}",
        "(".repeat(10_000),
        ")".repeat(10_000)
    );
    let negations = format!("basis fn f(x: Bit) -> Bit {{ {}x }}", "not ".repeat(10_000));
    let types = format!(
        "basis fn f(x: {}Bit{}) -> Bit {{ 0 }}",
        "(".repeat(10_000),
        ", Bit)".repeat(10_000)
    );
    let conditionals = format!(
        "observe fn f(b: CBit, q: Q<Bit>) -> Q<Bit> {{ {}q{} }}",
        "if b { ".repeat(10_000),
        " } else { q }".repeat(10_000)
    );
    for source in [&parentheses, &negations, &types, &conditionals] {
        let error = parse_module(source).unwrap_err();
        assert!(error.message.contains("limit"), "{error}");
        assert!(error.span.start < source.len());
    }

    let below_limit = format!(
        "iso fn f(q: Q<Bit>) -> Q<Bit> {{ {}q{} }}",
        "(".repeat(62),
        ")".repeat(62)
    );
    parse_module(&below_limit).unwrap();
}

#[test]
fn nested_operator_chains_share_the_ast_depth_limit() {
    let mut expr = "x".to_owned();
    for _ in 0..20 {
        expr = format!("({expr}){}", " xor x".repeat(20));
    }
    let source = format!("basis fn f(x: Bit) -> Bit {{ {expr} }}");
    assert!(parse_module(&source).unwrap_err().message.contains("limit"));
}

#[test]
fn invisible_separators_and_bad_bit_literals_have_precise_errors() {
    let cases = [
        (
            "// note\u{2028}iso fn hidden() -> Unit { () }",
            "unsupported line separator",
            "\u{2028}",
        ),
        ("// note\u{202e}hidden", "bidirectional control", "\u{202e}"),
        (
            "// note\u{0085}hidden",
            "unsupported line separator",
            "\u{0085}",
        ),
        (
            "// note\u{000b}hidden",
            "unsupported line separator",
            "\u{000b}",
        ),
        ("// note\u{0000}hidden", "control character", "\u{0000}"),
        (
            "basis fn f() -> Bit { 10 }",
            "Bit literal must be 0 or 1",
            "10",
        ),
        (
            "basis fn f() -> Bit { 2 }",
            "Bit literal must be 0 or 1",
            "2",
        ),
        (
            "basis fn f() -> Bit {\u{3000}0 }",
            "unsupported whitespace",
            "\u{3000}",
        ),
    ];
    for (source, message, offending) in cases {
        let error = parse_module(source).unwrap_err();
        assert!(error.message.contains(message), "{error}");
        assert_eq!(error.span.start, source.find(offending).unwrap());
        assert_eq!(error.span.end, error.span.start + offending.len());
    }
}
