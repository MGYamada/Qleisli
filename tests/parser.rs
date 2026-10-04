use qleisli::frontend::ast::{
    BasisExprKind, ExprKind, FnBody, FnKind, PatternKind, StmtKind, TypeKind,
};
use qleisli::frontend::parser::parse_module;
use qleisli::frontend::{ast::Span, lexer::lex};

fn check_token_prefixes(source: &str, label: &str) {
    parse_module(source).unwrap_or_else(|error| panic!("{label}: {error}"));
    let mut boundaries = vec![0, source.len()];
    for token in lex(source).unwrap() {
        boundaries.extend([token.span.start, token.span.end]);
    }
    boundaries.sort_unstable();
    boundaries.dedup();
    for end in boundaries {
        let result = std::panic::catch_unwind(|| parse_module(&source[..end]));
        assert!(result.is_ok(), "{label}: parser panicked at byte {end}");
    }
}

#[test]
fn static_operation_errors_point_to_the_unconsumed_token_or_eof() {
    let prefix = "unitary fn f(q: Q<Bit>) -> Q<Bit> { g[";
    for suffix in ["", "]", "0", "(", "true", "let"] {
        let source = format!("{prefix}{suffix}");
        let error = parse_module(&source).unwrap_err();
        assert_eq!(error.message, "expected a static operation description");
        assert_eq!(error.span, Span::new(prefix.len(), source.len()));
    }
    let source = format!("{prefix}repeat_op(0,");
    let error = parse_module(&source).unwrap_err();
    assert_eq!(error.message, "expected a static operation description");
    assert_eq!(error.span, Span::new(source.len(), source.len()));
}

#[test]
fn all_static_constructor_token_prefixes_parse_without_panicking() {
    for operation in [
        "bind_op(u,m)",
        "repeat_op(0,u)",
        "inverse_op(u)",
        "controlled_op(u)",
        "then_op(u,v)",
        "tensor_op(u,v)",
        "conjugate_op(u,v)",
        "then_op(bind_op(u,m),controlled_op(inverse_op(repeat_op(2,v))))",
    ] {
        let source = format!("unitary fn f(q: Q<Bit>) -> Q<Bit> {{ g[{operation}](q) }}");
        check_token_prefixes(&source, operation);
    }
}

#[test]
fn example_and_stdlib_token_prefixes_parse_without_panicking() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut directories = vec![root.join("examples"), root.join("stdlib/src")];
    let mut files = 0;
    while let Some(directory) = directories.pop() {
        for entry in std::fs::read_dir(directory).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                directories.push(path);
            } else if path.extension().is_some_and(|ext| ext == "qli") {
                let source = std::fs::read_to_string(&path).unwrap();
                check_token_prefixes(&source, &path.display().to_string());
                files += 1;
            }
        }
    }
    assert!(files > 0, "the source corpus must not be empty");
}

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
    assert!(matches!(&binder.kind, PatternKind::Name(name) if name.text == "x"));
    assert!(matches!(input.kind, ExprKind::Name(_)));
    assert!(matches!(basis.kind, BasisExprKind::Tuple(_)));

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
    assert!(matches!(body.result.kind, ExprKind::Tuple(_)));
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

#[test]
fn reserved_std_module_keywords_allow_further_identifier_components() {
    for (source, expected) in [
        ("use std::basis::a::b;", vec!["std", "basis", "a", "b"]),
        (
            "use std::observe::a::b::c;",
            vec!["std", "observe", "a", "b", "c"],
        ),
    ] {
        let module = parse_module(source).unwrap();
        assert_eq!(module.uses.len(), 1);
        assert!(module.decls.is_empty());
        let path = &module.uses[0].path;
        assert_eq!(
            path.iter()
                .map(|part| part.text.as_str())
                .collect::<Vec<_>>(),
            expected,
            "{source}"
        );
        for part in path {
            assert_eq!(&source[part.span.start..part.span.end], part.text);
        }
    }
    // The keyword exception applies only immediately after `std::`.
    // Resolving the parsed module/name is a separate project check.
    for source in [
        "use other::basis::a;",
        "use std::basis::observe;",
        "use std::observe::a::basis;",
    ] {
        assert!(parse_module(source).is_err(), "{source}");
    }
}

#[test]
fn unicode_format_characters_are_comment_text_but_not_source_tokens() {
    let declaration = "basis fn visible() -> Bit { 0 }";
    for format_character in ['\u{200b}', '\u{feff}'] {
        for line_ending in ["\n", "\r\n"] {
            let source = format!(
                "// note{format_character}basis fn hidden() -> Bit {{ 1 }}{line_ending}{declaration}"
            );
            let module = parse_module(&source).unwrap();
            assert_eq!(module.decls.len(), 1);
            assert_eq!(module.decls[0].name.text, "visible");
            assert_eq!(
                module.decls[0].span.start,
                source.find(declaration).unwrap()
            );
        }
        let trailing_comment = format!("{declaration} // note{format_character}");
        assert_eq!(parse_module(&trailing_comment).unwrap().decls.len(), 1);
        // Bare CR can hide displayed code, so the 0.2.0 source profile rejects it.
        let bare_cr = format!("// note{format_character}\r{declaration}");
        assert!(
            parse_module(&bare_cr)
                .unwrap_err()
                .message
                .contains("bare carriage return")
        );

        // In particular, a leading U+FEFF is not stripped as a BOM.
        let source = format!("{format_character}{declaration}");
        let error = parse_module(&source).unwrap_err();
        assert!(error.message.contains("unexpected character"), "{error}");
        assert_eq!(error.span.start, 0);
        assert_eq!(error.span.end, format_character.len_utf8());
    }
}

#[test]
fn coherent_lifts_parse_nested_basis_patterns_and_keep_their_spans() {
    let source = "unitary fn f(q: Q<((Bit,Unit),Bit)>) -> Q<(Bit,Bit)> {
        do ((a,_),b) <- q; pure (a,b)
    }";
    let module = parse_module(source).unwrap();
    let FnBody::Quantum(body) = &module.decls[0].body else {
        panic!("expected ordinary body")
    };
    let ExprKind::CoherentLift { binder, basis, .. } = &body.result.kind else {
        panic!("expected coherent lift")
    };
    assert_eq!(&source[binder.span.start..binder.span.end], "((a,_),b)");
    let PatternKind::Tuple(outer) = &binder.kind else {
        panic!("expected outer tuple pattern")
    };
    let [left, right] = outer.as_slice() else {
        panic!("two fields")
    };
    let PatternKind::Tuple(inner) = &left.kind else {
        panic!("expected nested tuple pattern")
    };
    let [a, ignored] = inner.as_slice() else {
        panic!("two nested fields")
    };
    assert!(matches!(&a.kind, PatternKind::Name(name) if name.text == "a"));
    assert!(matches!(ignored.kind, PatternKind::Wildcard));
    assert!(matches!(&right.kind, PatternKind::Name(name) if name.text == "b"));
    assert!(matches!(basis.kind, BasisExprKind::Tuple(_)));

    parse_module("iso fn f(q: Q<Unit>) -> Q<Bit> { do _ <- q; pure 0 }").unwrap();
    // Duplicate names are syntactically valid; the basis pattern checker must
    // reject them. Unit/singleton patterns and trailing commas remain invalid.
    parse_module("unitary fn f(q: Q<(Bit,Bit)>) -> Q<Bit> { do (a,a) <- q; pure a }").unwrap();
    for pattern in ["()", "(a)", "(a,)", "(a,b,c,)"] {
        let source = format!("unitary fn f(q: Q<Bit>) -> Q<Bit> {{ do {pattern} <- q; pure 0 }}");
        assert!(parse_module(&source).is_err(), "{source}");
    }
}

#[test]
fn classical_boolean_operators_have_precedence_and_left_associativity() {
    let source = "unitary fn f(a: CBit, b: CBit, c: CBit) -> CBit {
        not a and b xor c xor false
    }";
    let module = parse_module(source).unwrap();
    let FnBody::Quantum(body) = &module.decls[0].body else {
        panic!("expected ordinary body")
    };
    let ExprKind::Xor(first, last) = &body.result.kind else {
        panic!("expected outer xor")
    };
    assert!(matches!(last.kind, ExprKind::CBit(false)));
    let ExprKind::Xor(left, right) = &first.kind else {
        panic!("expected left-associated xor")
    };
    assert!(matches!(&right.kind, ExprKind::Name(name) if name.text == "c"));
    let ExprKind::And(negated, _) = &left.kind else {
        panic!("expected and to bind more tightly")
    };
    assert!(matches!(negated.kind, ExprKind::Not(_)));
    assert_eq!(
        &source[body.result.span.start..body.result.span.end],
        "not a and b xor c xor false"
    );

    let module = parse_module("unitary fn f() -> CBit { true and false and true }").unwrap();
    let FnBody::Quantum(body) = &module.decls[0].body else {
        panic!("expected ordinary body")
    };
    let ExprKind::And(left, right) = &body.result.kind else {
        panic!("expected outer and")
    };
    assert!(matches!(left.kind, ExprKind::And(_, _)));
    assert!(matches!(right.kind, ExprKind::CBit(true)));

    parse_module("unitary fn f(a: CBit) -> CBit { not (a xor true) }").unwrap();
    parse_module("unitary fn f(a: CBit) -> CBit { if not a { true } else { false } }").unwrap();
}

#[test]
fn classical_literals_are_reserved_and_distinct_from_basis_bits() {
    for source in [
        "unitary fn f() -> (CBit,CBit) { (true,false) }",
        "basis fn f() -> (Bit,Bit) { (0,1) }",
    ] {
        parse_module(source).unwrap();
    }
    for keyword in ["true", "false"] {
        for source in [
            format!("unitary fn {keyword}() -> Unit {{ () }}"),
            format!("unitary fn f({keyword}: CBit) -> Unit {{ () }}"),
            format!("unitary fn f() -> Unit {{ let {keyword} = (); () }}"),
            format!("use m::{keyword};"),
            format!("use {keyword}::f;"),
            format!("basis fn f() -> Bit {{ {keyword} }}"),
            format!("unitary fn f(q: Q<Bit>) -> Q<Bit> {{ do {keyword} <- q; pure 0 }}"),
        ] {
            assert!(parse_module(&source).is_err(), "{source}");
        }
    }
    for expression in ["0", "1", "true and", "not", "true xor xor false"] {
        let source = format!("unitary fn f() -> CBit {{ {expression} }}");
        assert!(parse_module(&source).is_err(), "{source}");
    }
}

#[test]
fn classical_operator_chains_and_basis_patterns_obey_depth_limits() {
    let mut nested_chain = "true".to_owned();
    for _ in 0..20 {
        nested_chain = format!("({nested_chain}){}", " xor true".repeat(20));
    }
    for expression in [
        format!("{}true", "not ".repeat(10_000)),
        format!("true{}", " xor false".repeat(10_000)),
        format!("true{}", " and false".repeat(10_000)),
        nested_chain,
    ] {
        let source = format!("unitary fn f() -> CBit {{ {expression} }}");
        let error = parse_module(&source).unwrap_err();
        assert!(error.message.contains("limit"), "{error}");
        assert!(error.span.start < source.len());
    }
    let deep_pattern = format!("{}a{}", "(".repeat(10_000), ",_)".repeat(10_000));
    let source = format!("unitary fn f(q: Q<Bit>) -> Q<Bit> {{ do {deep_pattern} <- q; pure a }}");
    assert!(parse_module(&source).unwrap_err().message.contains("limit"));

    for expression in [
        format!("{}true", "not ".repeat(32)),
        format!("true{}", " xor false".repeat(32)),
    ] {
        parse_module(&format!("unitary fn f() -> CBit {{ {expression} }}")).unwrap();
    }
}

#[test]
fn shared_scanner_preserves_the_finite_public_token_projection() {
    use qleisli::frontend::lexer::{TokenKind, lex};
    let source = "// λ\r\n==> <-> <= >= :: :/*x*/: 00 01 Bits fn";
    let tokens = lex(source).unwrap();
    assert_eq!(
        tokens.iter().map(|t| t.kind.clone()).collect::<Vec<_>>(),
        vec![
            TokenKind::Equals,
            TokenKind::FatArrow,
            TokenKind::LeftArrow,
            TokenKind::RAngle,
            TokenKind::LAngle,
            TokenKind::Equals,
            TokenKind::RAngle,
            TokenKind::Equals,
            TokenKind::DoubleColon,
            TokenKind::Colon,
            TokenKind::Colon,
            TokenKind::Natural("00".into()),
            TokenKind::Natural("01".into()),
            TokenKind::Ident("Bits".into()),
            TokenKind::Fn,
            TokenKind::Eof,
        ]
    );
    assert_eq!(tokens[0].span.start, "// λ\r\n".len());
    assert_eq!(&source[tokens[1].span.start..tokens[1].span.end], "=>");
    assert_eq!(tokens.last().unwrap().span.start, source.len());
    for source in ["+", "-", "*", "^", "..", "!=", "-/*x*/>"] {
        let e = lex(source).unwrap_err();
        assert_eq!((e.span.start, e.span.end), (0, 1), "{source}");
        assert!(e.message.starts_with("unexpected character"));
    }
}
