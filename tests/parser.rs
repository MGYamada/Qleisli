use qleisli::frontend::ast::{
    BasisExprKind, ExprKind, FnBody, FnKind, PatternKind, StmtKind, TypeKind,
};
use qleisli::frontend::parser::parse_module;
use qleisli::frontend::{ast::Span, lexer::lex};

#[test]
fn ordinary_match_retains_qualified_label_bytes_and_separate_arm_blocks() {
    let source = "// λ\r\nfn f(t:Tri)->Bit{match t { alias /* λ */ :: Tri :: A => { let x=0; x }, Tri::B => 1, }}";
    let module = parse_module(source).unwrap();
    let FnBody::Quantum(body) = &module.decls[0].body else {
        panic!()
    };
    let ExprKind::Match(selection) = &body.result.kind else {
        panic!()
    };
    assert_eq!(
        &source[body.result.span.start..body.result.span.end],
        "match t { alias /* λ */ :: Tri :: A => { let x=0; x }, Tri::B => 1, }"
    );
    assert!(matches!(selection.scrutinee.kind, ExprKind::Name(_)));
    let first = &selection.arms[0];
    assert_eq!(first.label.type_name.text, "alias::Tri");
    assert_eq!(
        &source[first.label.type_name.span.start..first.label.type_name.span.end],
        "alias /* λ */ :: Tri"
    );
    assert_eq!(
        &source[first.label.variant.span.start..first.label.variant.span.end],
        "A"
    );
    assert_eq!(
        &source[first.span.start..first.span.end],
        "alias /* λ */ :: Tri :: A => { let x=0; x }"
    );
    assert_eq!(first.body.statements.len(), 1);
    let second = &selection.arms[1];
    assert!(second.body.statements.is_empty());
    assert!(!second.body.implicit_result);
    assert_eq!(second.body.span, second.body.result.span);
    assert_eq!(&source[second.body.span.start..second.body.span.end], "1");
    check_token_prefixes(source, "ordinary match");
}

#[test]
fn classical_match_retains_every_label_and_expression() {
    let source =
        "// λ\r\nclassical fn f(t:Tri)->Bit{match t { Tri :: A => 0, other::Tri::B => not g(t), }}";
    let module = parse_module(source).unwrap();
    let FnBody::Basis(body) = &module.decls[0].body else {
        panic!()
    };
    let BasisExprKind::Match(selection) = &body.kind else {
        panic!()
    };
    assert_eq!(selection.arms.len(), 2);
    assert!(matches!(selection.scrutinee.kind, BasisExprKind::Name(_)));
    assert_eq!(selection.arms[1].label.type_name.text, "other::Tri");
    assert!(matches!(selection.arms[1].body.kind, BasisExprKind::Not(_)));
    for arm in &selection.arms {
        assert_eq!(
            &source[arm.label.variant.span.start..arm.label.variant.span.end],
            arm.label.variant.text
        );
        assert!(arm.span.start <= arm.body.span.start && arm.body.span.end <= arm.span.end);
    }
    check_token_prefixes(source, "classical match");
}

#[test]
fn match_scrutinees_do_not_consume_arm_braces_or_disable_nested_records() {
    for prefix in ["fn", "classical fn"] {
        for expression in [
            "match t { E::A => P{tag:t}.tag, E::B => t }",
            "match (P{tag:t}.tag) { E::A => t, E::B => t }",
            "match g(P{tag:t}) { E::A => t, E::B => t }",
            "match match t { E::A => t, E::B => t } { E::A => t, E::B => t }",
            "match t { E::A => match t { E::A => t, E::B => t }, E::B => t }",
        ] {
            parse_module(&format!("{prefix} f(t:E)->E{{{expression}}}")).unwrap();
        }
    }
}

#[test]
fn match_labels_are_exact_and_general_patterns_remain_unavailable() {
    for prefix in ["fn", "classical fn"] {
        for label in ["_", "A", "E::A(x)", "E::A{x}", "E::A | E::B", "E::A if 1"] {
            let source = format!("{prefix} f(t:E)->Bit{{match t{{{label}=>0}}}}");
            assert!(parse_module(&source).is_err(), "{source}");
        }
        for body in ["E::A=>0 E::B=>1", "E::A=>0;", "E::A,", "=>0"] {
            let source = format!("{prefix} f(t:E)->Bit{{match t{{{body}}}}}");
            assert!(parse_module(&source).is_err(), "{source}");
        }
        // Duplicate, empty and foreign labels remain visible for common checking.
        parse_module(&format!(
            "{prefix} f(t:E)->Bit{{match t{{E::A=>0,E::A=>1,F::B=>0}}}}"
        ))
        .unwrap();
        parse_module(&format!("{prefix} f(t:E)->Bit{{match t{{}}}}")).unwrap();
    }
    assert!(parse_module("classical fn f(t:E)->Bit{match t{E::A=>{let x=0;x}}}").is_err());
}

#[test]
fn match_arm_and_ast_depth_limits_are_checked_without_selecting_a_branch() {
    let arms = (0..64)
        .map(|n| format!("E::V{n}=>0"))
        .collect::<Vec<_>>()
        .join(",");
    for prefix in ["fn", "classical fn"] {
        parse_module(&format!("{prefix} f(t:E)->Bit{{match t{{{arms}}}}}")).unwrap();
        let source = format!("{prefix} f(t:E)->Bit{{match t{{{arms},E::Extra=>0}}}}");
        let error = parse_module(&source).unwrap_err();
        assert_eq!(error.message, "ordinary match exceeds 64 arms");
        assert_eq!(&source[error.span.start..error.span.end], "E");
        let nested = format!("{}0{}", "match t{E::A=>".repeat(65), "}".repeat(65));
        assert!(
            parse_module(&format!("{prefix} f(t:E)->Bit{{{nested}}}"))
                .unwrap_err()
                .message
                .contains("64-level")
        );
        // The deep second branch must count even if the first label is repeated.
        let nested = format!("match t{{E::A=>0,E::A=>{}0{}}}", "not ".repeat(64), "");
        assert!(
            parse_module(&format!("{prefix} f(t:E)->Bit{{{nested}}}"))
                .unwrap_err()
                .message
                .contains("64-level")
        );
    }
}

#[test]
fn ordinary_match_word_is_reserved_in_runtime_and_module_names() {
    use qleisli::frontend::lexer::TokenKind;
    assert_eq!(lex("match").unwrap()[0].kind, TokenKind::Match);
    for source in [
        "fn match()->Unit{()}",
        "fn f(match:Bit)->Bit{match}",
        "use match::f;",
        "enum match { A }",
    ] {
        let error = parse_module(source).unwrap_err();
        assert_eq!(&source[error.span.start..error.span.end], "match");
        assert!(error.message.starts_with("expected"), "{error:?}");
    }
}

#[test]
fn finite_type_declarations_keep_names_members_shapes_and_original_spans() {
    use qleisli::frontend::ast::TypeDeclKind;
    let source = "pub enum Tri { A, B, C, } fn f(q:Q<labels::Tri>)->Q<labels::Tri>{q} struct Empty {} pub struct Tagged { pub tag: labels::Tri, flag: Bit, zero: Bits<0>, }";
    let module = parse_module(source).unwrap();
    assert_eq!(module.decls.len(), 1);
    assert_eq!(module.type_decls.len(), 3);
    let tri = &module.type_decls[0];
    assert!(tri.public);
    assert_eq!(tri.name.text, "Tri");
    assert_eq!(
        &source[tri.span.start..tri.span.end],
        "pub enum Tri { A, B, C, }"
    );
    let TypeDeclKind::Enum { variants } = &tri.kind else {
        panic!("enum")
    };
    assert_eq!(
        variants.iter().map(|v| v.text.as_str()).collect::<Vec<_>>(),
        ["A", "B", "C"]
    );
    assert!(
        variants
            .iter()
            .all(|v| source[v.span.start..v.span.end] == v.text)
    );
    let empty = &module.type_decls[1];
    assert!(!empty.public);
    assert!(matches!(&empty.kind, TypeDeclKind::Record { fields } if fields.is_empty()));
    let TypeDeclKind::Record { fields } = &module.type_decls[2].kind else {
        panic!("record")
    };
    assert_eq!(
        fields
            .iter()
            .map(|f| f.name.text.as_str())
            .collect::<Vec<_>>(),
        ["tag", "flag", "zero"]
    );
    assert!(fields[0].public);
    assert!(!fields[1].public);
    assert_eq!(
        &source[fields[0].span.start..fields[0].span.end],
        "pub tag: labels::Tri"
    );
    assert!(matches!(&fields[0].ty.kind, TypeKind::Named(name) if name.text == "labels::Tri"));
    let TypeKind::Q(inner) = &module.decls[0].params[0].ty.kind else {
        panic!("owner")
    };
    assert!(
        matches!(&inner.kind, TypeKind::Named(name) if name.text == "labels::Tri" && &source[name.span.start..name.span.end] == "labels::Tri")
    );
}

#[test]
fn finite_declaration_profile_is_bounded_and_rejects_unimplemented_payload_forms() {
    for source in [
        "enum E { A(Bit) }",
        "enum E { A { value: Bit } }",
        "enum E { A = 1 }",
        "struct R(Bit);",
        "struct R[const N:Nat] { value: Bits<N> }",
        "enum E { A B }",
        "struct R { a: Bit b: Bit }",
        "fn enum()->Unit{()}",
        "fn struct()->Unit{()}",
    ] {
        assert!(parse_module(source).is_err(), "{source}");
    }
    for keyword in ["enum", "struct"] {
        let members = (0..64)
            .map(|i| {
                if keyword == "enum" {
                    format!("V{i}")
                } else {
                    format!("f{i}: Bit")
                }
            })
            .collect::<Vec<_>>()
            .join(",");
        let source = format!("{keyword} Many {{ {members} }}");
        check_token_prefixes(&source, keyword);
        let extra = if keyword == "enum" {
            "Extra"
        } else {
            "extra: Bit"
        };
        let over = format!("{keyword} Many {{ {members}, {extra} }}");
        let error = parse_module(&over).unwrap_err();
        assert_eq!(error.message, "finite type declaration exceeds 64 members");
        assert_eq!(
            &over[error.span.start..error.span.end],
            extra.split(':').next().unwrap()
        );
    }
}

#[test]
fn qualified_type_paths_preserve_the_complete_reference_in_every_type_position() {
    let source = "pub fn f[const U:Op<model::Input -> model::Output>](q:Q<model::Input>)->Q<model::Output>{U(q)}";
    let module = parse_module(source).unwrap();
    let declaration = &module.decls[0];
    let qleisli::frontend::ast::StaticParamKind::Operation {
        basis, codomain, ..
    } = &declaration.static_params[0].kind
    else {
        panic!("operation")
    };
    for (ty, expected) in [
        (basis, "model::Input"),
        (codomain.as_deref().unwrap(), "model::Output"),
    ] {
        assert!(matches!(&ty.kind, TypeKind::Named(name) if name.text == expected));
        assert_eq!(&source[ty.span.start..ty.span.end], expected);
    }
    let incomplete = "fn f(q:Q<model::>)->Unit{()}";
    let error = parse_module(incomplete).unwrap_err();
    assert_eq!(&incomplete[error.span.start..error.span.end], "model::");
}

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
    for suffix in ["", "true", "let"] {
        let source = format!("{prefix}{suffix}");
        let error = parse_module(&source).unwrap_err();
        assert_eq!(error.message, "expected a static operation description");
        assert_eq!(error.span, Span::new(prefix.len(), source.len()));
    }
    let source = format!("{prefix}power(");
    let error = parse_module(&source).unwrap_err();
    assert_eq!(error.message, "expected a static operation description");
    assert_eq!(error.span, Span::new(source.len(), source.len()));
}

#[test]
fn all_static_constructor_token_prefixes_parse_without_panicking() {
    for operation in [
        "checked_op(u,m)",
        "power(u,0)",
        "adjoint(u)",
        "controlled(u)",
        "then_op(u,v)",
        "tensor_op(u,v)",
        "conjugate_op(u,v)",
        "then_op(checked_op(u,m),controlled(adjoint(power(v,2))))",
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
pub isometry fn entangle(q: Q<Bit>) -> Q<(Bit, Bit)> {
    basis q as x {
        (x, x)
    }
}
"#;
    let module = parse_module(bell).unwrap();
    assert_eq!(module.decls.len(), 1);
    let decl = &module.decls[0];
    assert!(decl.public);
    assert_eq!(decl.kind, FnKind::Isometry);
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

observe fn main() -> (Bit, Bit) {
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
classical fn predicate(x: Bit) -> Bit { not x }
pub unitary fn phase_oracle(q: Q<Bit>) -> Q<Bit> {
    with_computed(q, predicate) { |a| z(a) }
}
observe fn feedback(q: Q<Bit>, r: Q<Bit>) -> (Bit, Q<Bit>) {
    let b = measure_z(q);
    let r1 = if b { x(r) } else { r };
    (b, r1)
}
"#;
    let module = parse_module(source).unwrap();
    assert_eq!(module.decls.len(), 3);
    assert_eq!(module.decls[0].kind, FnKind::Classical);
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
        parse_module("classical fn f(x: Bit, y: Bit, z: Bit) -> Bit { not x and y xor z xor 1 }")
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
    let source = "// λ\nisometry fn f(q: Q<Bit>) -> Q<Bit> { q }";
    let module = parse_module(source).unwrap();
    let offset = source.find("isometry").unwrap();
    assert_eq!(offset, 6);
    assert_eq!(module.decls[0].span.start, offset);
    assert_eq!(
        &source[module.decls[0].name.span.start..module.decls[0].name.span.end],
        "f"
    );
    let bad = "// λ\nisometry fn f(q: Q<Bit>) -> Q<Bit> { @ }";
    let error = parse_module(bad).unwrap_err();
    assert_eq!(error.span.start, bad.find('@').unwrap());
    assert_eq!(error.span.end, error.span.start + 1);
    assert!(error.message.contains("unexpected character"));
}

#[test]
fn malformed_syntax_has_precise_error_spans() {
    let cases = [
        ("use oracle::*;", "*", "expected an identifier"),
        (
            "isometry fn f(q: Q<Bit>) -> Q<Bit> { basis q as x { let y = x; y } }",
            "let",
            "expected",
        ),
        ("classical fn f(x: CBit) -> Bit { x }", "CBit", "removed"),
    ];
    for (source, at, message) in cases {
        let error = parse_module(source).unwrap_err();
        assert_eq!(error.span.start, source.find(at).unwrap(), "{source}");
        assert!(error.message.contains(message), "{error}");
    }
}

#[test]
fn deep_syntax_is_rejected_without_exhausting_the_stack() {
    // macOS otherwise gives test threads more stack than the Linux CI lane.
    std::thread::Builder::new()
        .stack_size(2 * 1024 * 1024)
        .spawn(check_deep_syntax_on_bounded_stack)
        .unwrap()
        .join()
        .unwrap();
}

fn check_deep_syntax_on_bounded_stack() {
    let parentheses = format!(
        "isometry fn f(q: Q<Bit>) -> Q<Bit> {{ {}q{} }}",
        "(".repeat(10_000),
        ")".repeat(10_000)
    );
    let negations = format!(
        "classical fn f(x: Bit) -> Bit {{ {}x }}",
        "not ".repeat(10_000)
    );
    let types = format!(
        "classical fn f(x: {}Bit{}) -> Bit {{ 0 }}",
        "(".repeat(10_000),
        ", Bit)".repeat(10_000)
    );
    let conditionals = format!(
        "observe fn f(b: Bit, q: Q<Bit>) -> Q<Bit> {{ {}q{} }}",
        "if b { ".repeat(10_000),
        " } else { q }".repeat(10_000)
    );
    for source in [&parentheses, &negations, &types, &conditionals] {
        let error = parse_module(source).unwrap_err();
        assert!(error.message.contains("limit"), "{error}");
        assert!(error.span.start < source.len());
    }

    let below_limit = format!(
        "isometry fn f(q: Q<Bit>) -> Q<Bit> {{ {}q{} }}",
        "(".repeat(62),
        ")".repeat(62)
    );
    parse_module(&below_limit).unwrap();

    // Exercise the contextual branch as well as the ordinary parentheses
    // that exposed the dispatch-frame regression. The operation argument
    // itself must still share the original nesting limit.
    let input = format!("{}q{}", "(".repeat(60), ")".repeat(60));
    for expression in [
        format!("power(u, 2)({input})"),
        format!("adjoint(u)({input})"),
        format!("controlled(u)(c, {input})"),
    ] {
        parse_module(&format!(
            "unitary fn f(c: Q<Bit>, q: Q<Bit>) -> Q<Bit> {{ {expression} }}"
        ))
        .unwrap();
    }
    let expression = format!("{}q{}", "power(u, 1)(".repeat(60), ")".repeat(60));
    parse_module(&format!(
        "unitary fn f(q: Q<Bit>) -> Q<Bit> {{ {expression} }}"
    ))
    .unwrap();
    let expression = format!("{}q{}", "power(u, 1)(".repeat(10_000), ")".repeat(10_000));
    let error = parse_module(&format!(
        "unitary fn f(q: Q<Bit>) -> Q<Bit> {{ {expression} }}"
    ))
    .unwrap_err();
    assert!(error.message.contains("limit"), "{error}");
    let operation = format!("{}u{}", "power(".repeat(10_000), ", 1)".repeat(10_000));
    let error = parse_module(&format!(
        "unitary fn f(q: Q<Bit>) -> Q<Bit> {{ power({operation}, 1)(q) }}"
    ))
    .unwrap_err();
    assert!(error.message.contains("limit"), "{error}");
}

#[test]
fn nested_operator_chains_share_the_ast_depth_limit() {
    let mut expr = "x".to_owned();
    for _ in 0..20 {
        expr = format!("({expr}){}", " xor x".repeat(20));
    }
    let source = format!("classical fn f(x: Bit) -> Bit {{ {expr} }}");
    assert!(parse_module(&source).unwrap_err().message.contains("limit"));
}

#[test]
fn invisible_separators_and_bad_bit_literals_have_precise_errors() {
    let cases = [
        (
            "// note\u{2028}isometry fn hidden() -> Unit { () }",
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
            "classical fn f() -> Bit { 10 }",
            "Bit literal must be 0 or 1",
            "10",
        ),
        (
            "classical fn f() -> Bit { 2 }",
            "Bit literal must be 0 or 1",
            "2",
        ),
        (
            "classical fn f() -> Bit {\u{3000}0 }",
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
    let declaration = "classical fn visible() -> Bit { 0 }";
    for format_character in ['\u{200b}', '\u{feff}'] {
        for line_ending in ["\n", "\r\n"] {
            let source = format!(
                "// note{format_character}classical fn hidden() -> Bit {{ 1 }}{line_ending}{declaration}"
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
        basis q as ((a,_),b) { (a,b) }
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

    assert_eq!(
        &source[body.result.span.start..body.result.span.end],
        "basis q as ((a,_),b) { (a,b) }"
    );
    assert_eq!(&source[basis.span.start..basis.span.end], "(a,b)");

    parse_module("isometry fn f(q: Q<Unit>) -> Q<Bit> { basis q as _ { 0 } }").unwrap();
    // Duplicate names are syntactically valid; the basis pattern checker must
    // reject them. Empty tuple patterns are shared syntax for the sized profile;
    // singleton patterns and trailing commas remain invalid.
    parse_module("unitary fn f(q: Q<(Bit,Bit)>) -> Q<Bit> { basis q as (a,a) { a } }").unwrap();
    for pattern in ["(a)", "(a,)", "(a,b,c,)"] {
        let source =
            format!("unitary fn f(q: Q<Bit>) -> Q<Bit> {{ basis q as {pattern} {{ 0 }} }}");
        assert!(parse_module(&source).is_err(), "{source}");
    }
}

#[test]
fn coherent_basis_as_is_contextual_and_preserves_identifier_positions() {
    use qleisli::frontend::lexer::TokenKind;

    let tokens = lex("as").unwrap();
    assert_eq!(tokens[0].kind, TokenKind::Ident("as".into()));
    let source = r#"
use as::{f,as};
unitary fn as(q: Q<Bit>) -> Q<Bit> { q }
unitary fn call(q: Q<Bit>) -> Q<Bit> { basis as(q) as as { as } }
unitary fn direct(as: Q<Bit>) -> Q<Bit> { basis as as as { as } }
unitary fn sized[const as: Nat](q: Q<Bits<as>>) -> Q<Bits<as>> { q }
"#;
    let module = parse_module(source).unwrap();
    assert_eq!(module.uses.len(), 2);
    assert_eq!(module.uses[0].path[0].text, "as");
    assert_eq!(module.uses[1].path[1].text, "as");
    assert_eq!(module.decls[0].name.text, "as");
    assert_eq!(module.decls[3].static_params[0].name.text, "as");
    for (index, called) in [(1, true), (2, false)] {
        let FnBody::Quantum(body) = &module.decls[index].body else {
            panic!("expected ordinary body")
        };
        let ExprKind::CoherentLift {
            binder,
            input,
            basis,
        } = &body.result.kind
        else {
            panic!("expected coherent lift")
        };
        assert!(matches!(&binder.kind, PatternKind::Name(name) if name.text == "as"));
        assert!(matches!(&basis.kind, BasisExprKind::Name(name) if name.text == "as"));
        match &input.kind {
            ExprKind::Call { callee, .. } if called => assert_eq!(callee.text, "as"),
            ExprKind::Name(name) if !called => assert_eq!(name.text, "as"),
            _ => panic!("input must retain its original expression category"),
        }
    }
}

#[test]
fn coherent_basis_input_retains_existing_expression_grammar() {
    for (input, category) in [
        ("f(q)", "call"),
        ("(q,r)", "tuple"),
        ("if b { q } else { r }", "conditional"),
        ("basis q as inner { inner }", "lift"),
    ] {
        let source = format!(
            "unitary fn f(q: Q<Bit>, r: Q<Bit>, b: Bit) -> Q<Bit> {{ basis {input} as label {{ label }} }}"
        );
        let module = parse_module(&source).unwrap();
        let FnBody::Quantum(body) = &module.decls[0].body else {
            panic!("expected ordinary body")
        };
        let ExprKind::CoherentLift { input: parsed, .. } = &body.result.kind else {
            panic!("expected coherent lift")
        };
        assert_eq!(&source[parsed.span.start..parsed.span.end], input);
        assert!(
            matches!(
                (&parsed.kind, category),
                (ExprKind::Call { .. }, "call")
                    | (ExprKind::Tuple(_), "tuple")
                    | (ExprKind::If { .. }, "conditional")
                    | (ExprKind::CoherentLift { .. }, "lift")
            ),
            "{source}"
        );
    }
    // Parsing preserves the ordinary expression; the source checker, rather
    // than a second parser grammar, enforces that it produces one Q<A> owner.
    let module = parse_module(
        "unitary fn f(a: Bit, b: Bit, c: Bit) -> Q<Bit> { basis not a and b xor c as label { label } }",
    )
    .unwrap();
    let FnBody::Quantum(body) = &module.decls[0].body else {
        panic!("expected ordinary body")
    };
    let ExprKind::CoherentLift { input, .. } = &body.result.kind else {
        panic!("expected coherent lift")
    };
    let ExprKind::Xor(left, _) = &input.kind else {
        panic!("expected lower-precedence xor in the input")
    };
    assert!(matches!(left.kind, ExprKind::And(_, _)));
}

#[test]
fn coherent_basis_body_keeps_basis_precedence_and_unit_patterns() {
    let source =
        "unitary fn f(q: Q<(Bit,Bit,Bit)>) -> Q<Bit> { basis q as (a,b,c) { not a and b xor c } }";
    let module = parse_module(source).unwrap();
    let FnBody::Quantum(body) = &module.decls[0].body else {
        panic!("expected ordinary body")
    };
    let ExprKind::CoherentLift { basis, .. } = &body.result.kind else {
        panic!("expected coherent lift")
    };
    let BasisExprKind::Xor(left, _) = &basis.kind else {
        panic!("expected lower-precedence xor in the basis body")
    };
    let BasisExprKind::And(first, _) = &left.kind else {
        panic!("expected higher-precedence and")
    };
    assert!(matches!(first.kind, BasisExprKind::Not(_)));
    let module =
        parse_module("unitary fn f(q: Q<Unit>) -> Q<Unit> { basis q as () { () } }").unwrap();
    let FnBody::Quantum(body) = &module.decls[0].body else {
        panic!("expected ordinary body")
    };
    let ExprKind::CoherentLift { binder, basis, .. } = &body.result.kind else {
        panic!("expected coherent lift")
    };
    assert!(matches!(&binder.kind, PatternKind::Tuple(fields) if fields.is_empty()));
    assert!(matches!(basis.kind, BasisExprKind::Unit));
}

#[test]
fn coherent_basis_body_is_one_expression_without_statements_or_a_semicolon() {
    for basis in [
        "",
        "x;",
        "let y = x; y",
        "{ x }",
        "basis q as y { y }",
        "if x { x } else { x }",
        "x, x",
    ] {
        let prefix = "unitary fn f(q: Q<Bit>) -> Q<Bit> { basis q as x { ";
        let source = format!("{prefix}{basis} }} }}");
        let error = parse_module(&source).unwrap_err();
        assert!(error.span.start >= prefix.len(), "{source}\n{error}");
        assert!(error.span.start < source.len(), "{source}\n{error}");
    }
}

#[test]
fn coherent_basis_delimiter_errors_point_to_the_missing_as_or_body() {
    for (suffix, at, expected) in [
        ("basis q label { label }", "label", "expected `as`"),
        ("basis q AS label { label }", "AS", "expected `as`"),
        ("basis q as label label", "label }", "expected `{`"),
    ] {
        let prefix = "unitary fn f(q: Q<Bit>) -> Q<Bit> { ";
        let source = format!("{prefix}{suffix} }}");
        let error = parse_module(&source).unwrap_err();
        assert!(error.message.contains(expected), "{source}\n{error}");
        assert_eq!(error.span.start, source.find(at).unwrap(), "{source}");
    }
    let source = "unitary fn f(q: Q<Bit>) -> Q<Bit> { basis q";
    let error = parse_module(source).unwrap_err();
    assert_eq!(error.message, "expected `as`");
    assert_eq!(error.span, Span::new(source.len(), source.len()));
}

#[test]
fn retired_coherent_do_and_pure_have_located_migration_diagnostics() {
    for (source, keyword) in [
        (
            "unitary fn f(q: Q<Bit>) -> Q<Bit> { do x <- q; pure x }",
            "do",
        ),
        ("unitary fn f(q: Q<Bit>) -> Q<Bit> { pure q }", "pure"),
        (
            "unitary fn f(q: Q<Bit>) -> Q<Bit> { basis q as x { pure x } }",
            "pure",
        ),
        ("classical fn f(x: Bit) -> Bit { not pure x }", "pure"),
        (
            "unitary fn f(q: Q<Bit>) -> Q<Bit> { basis q as x { do y <- q; pure y } }",
            "do",
        ),
        (
            "unitary fn f(q: Q<Bit>) -> Q<Bit> { basis q as x { x xor pure x } }",
            "pure",
        ),
    ] {
        let error = parse_module(source).unwrap_err();
        let start = source.find(keyword).unwrap();
        assert_eq!(error.span, Span::new(start, start + keyword.len()));
        for message in [
            "removed in Qleisli 0.3.0",
            "basis q as p { e }",
            "not monadic bind or measurement",
            "`pure` does not prepare a state",
        ] {
            assert!(error.message.contains(message), "{source}\n{error}");
        }
    }
}

#[test]
fn coherent_basis_token_prefixes_parse_without_panicking() {
    for expression in [
        "basis q as label { (label,label) }",
        "basis f(q) as (a,_) { not a }",
        "basis basis q as a { a } as b { b }",
        "basis as(q) as as { as }",
    ] {
        let source = format!("isometry fn f(q: Q<Bit>) -> Q<Bit> {{ {expression} }}");
        check_token_prefixes(&source, expression);
    }
}

#[test]
fn classical_boolean_operators_have_precedence_and_left_associativity() {
    let source = "unitary fn f(a: Bit, b: Bit, c: Bit) -> Bit {
        not a and b xor c xor 0
    }";
    let module = parse_module(source).unwrap();
    let FnBody::Quantum(body) = &module.decls[0].body else {
        panic!("expected ordinary body")
    };
    let ExprKind::Xor(first, last) = &body.result.kind else {
        panic!("expected outer xor")
    };
    assert!(matches!(last.kind, ExprKind::Bit(false)));
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
        "not a and b xor c xor 0"
    );

    let module = parse_module("unitary fn f() -> Bit { 1 and 0 and 1 }").unwrap();
    let FnBody::Quantum(body) = &module.decls[0].body else {
        panic!("expected ordinary body")
    };
    let ExprKind::And(left, right) = &body.result.kind else {
        panic!("expected outer and")
    };
    assert!(matches!(left.kind, ExprKind::And(_, _)));
    assert!(matches!(right.kind, ExprKind::Bit(true)));

    parse_module("unitary fn f(a: Bit) -> Bit { not (a xor 1) }").unwrap();
    parse_module("unitary fn f(a: Bit) -> Bit { if not a { 1 } else { 0 } }").unwrap();
}

#[test]
fn canonical_bit_literals_share_spelling_with_basis_bits() {
    for source in [
        "unitary fn f() -> (Bit,Bit) { (1,0) }",
        "classical fn f() -> (Bit,Bit) { (0,1) }",
    ] {
        parse_module(source).unwrap();
    }
    for keyword in ["true", "false"] {
        for source in [
            format!("unitary fn {keyword}() -> Unit {{ () }}"),
            format!("unitary fn f({keyword}: Bit) -> Unit {{ () }}"),
            format!("unitary fn f() -> Unit {{ let {keyword} = (); () }}"),
            format!("use m::{keyword};"),
            format!("use {keyword}::f;"),
            format!("classical fn f() -> Bit {{ {keyword} }}"),
            format!("unitary fn f(q: Q<Bit>) -> Q<Bit> {{ basis q as {keyword} {{ 0 }} }}"),
        ] {
            assert!(parse_module(&source).is_err(), "{source}");
        }
    }
    for expression in ["2", "01", "1 and", "not", "1 xor xor 0"] {
        let source = format!("unitary fn f() -> Bit {{ {expression} }}");
        assert!(parse_module(&source).is_err(), "{source}");
    }
}

#[test]
fn classical_operator_chains_and_basis_patterns_obey_depth_limits() {
    let mut nested_chain = "1".to_owned();
    for _ in 0..20 {
        nested_chain = format!("({nested_chain}){}", " xor 1".repeat(20));
    }
    for expression in [
        format!("{}1", "not ".repeat(10_000)),
        format!("1{}", " xor 0".repeat(10_000)),
        format!("1{}", " and 0".repeat(10_000)),
        nested_chain,
    ] {
        let source = format!("unitary fn f() -> Bit {{ {expression} }}");
        let error = parse_module(&source).unwrap_err();
        assert!(error.message.contains("limit"), "{error}");
        assert!(error.span.start < source.len());
    }
    let deep_pattern = format!("{}a{}", "(".repeat(10_000), ",_)".repeat(10_000));
    let source =
        format!("unitary fn f(q: Q<Bit>) -> Q<Bit> {{ basis q as {deep_pattern} {{ a }} }}");
    assert!(parse_module(&source).unwrap_err().message.contains("limit"));

    for expression in [
        format!("{}1", "not ".repeat(32)),
        format!("1{}", " xor 0".repeat(32)),
    ] {
        parse_module(&format!("unitary fn f() -> Bit {{ {expression} }}")).unwrap();
    }
}

#[test]
fn common_token_stream_includes_sized_punctuation_without_trivia_joining() {
    use qleisli::frontend::lexer::{TokenKind, lex};
    let source = "// λ\r\n==> <-> <= >= :: :/*x*/: 00 01 Bits fn";
    let tokens = lex(source).unwrap();
    assert_eq!(
        tokens.iter().map(|t| t.kind.clone()).collect::<Vec<_>>(),
        vec![
            TokenKind::EqualEqual,
            TokenKind::RAngle,
            TokenKind::LeftArrow,
            TokenKind::RAngle,
            TokenKind::LessEqual,
            TokenKind::GreaterEqual,
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
    assert_eq!(&source[tokens[0].span.start..tokens[0].span.end], "==");
    assert_eq!(tokens.last().unwrap().span.start, source.len());
    let dot = lex(".").unwrap();
    assert_eq!(dot.len(), 2);
    assert_eq!(dot[0].kind, TokenKind::Dot);
    assert_eq!((dot[0].span.start, dot[0].span.end), (0, 1));
    assert_eq!(dot[1].kind, TokenKind::Eof);
    assert_eq!((dot[1].span.start, dot[1].span.end), (1, 1));
    for source in ["!", "/", "!/*x*/="] {
        let e = lex(source).unwrap_err();
        assert_eq!((e.span.start, e.span.end), (0, 1), "{source}");
        assert!(e.message.starts_with("unexpected character"));
    }
}

#[test]
fn common_natural_and_count_syntax_keeps_precedence_and_source_spans() {
    use qleisli::frontend::ast::{Count, NatKind, StaticOpKind, StaticParamKind};
    let source = "pub unitary fn f[const n:Nat,const U:Op<Bits<n+1*2>>](q:Q<Bits<n>>)->Q<Bits<n>> requires n+1*2 >= 0 { adjoint(power(U,2^(n+1)))(q) }";
    let ast = parse_module(source).unwrap();
    assert!(matches!(
        ast.decls[0].static_params[0].kind,
        StaticParamKind::Natural
    ));
    let StaticParamKind::Operation { basis, .. } = &ast.decls[0].static_params[1].kind else {
        panic!("operation")
    };
    let TypeKind::Bits(size) = &basis.kind else {
        panic!("register basis")
    };
    assert_eq!(&source[size.span.start..size.span.end], "n+1*2");
    let NatKind::Add(left, right) = &size.kind else {
        panic!("addition")
    };
    assert!(matches!(&left.kind,NatKind::Name(n) if n=="n"));
    assert!(matches!(&right.kind, NatKind::Mul(..)));
    let FnBody::Quantum(body) = &ast.decls[0].body else {
        panic!("body")
    };
    let ExprKind::Adjoint { operation, .. } = &body.result.kind else {
        panic!("adjoint")
    };
    let StaticOpKind::Repeat(Count::Power(exponent), _) = &operation.kind else {
        panic!("counted power")
    };
    assert_eq!(&source[exponent.span.start..exponent.span.end], "(n+1)");
    assert!(matches!(exponent.kind, NatKind::Add(..)));
}

#[test]
fn basis_requires_rejects_before_documentation_attachment() {
    for clause in ["0 == 0", "Applicable(U)"] {
        let source = format!("/// title\nclassical fn f(x:Bit)->Bit requires {clause} {{x}}");
        let error = parse_module(&source).unwrap_err();
        assert_eq!(&source[error.span.start..error.span.end], "requires");
        assert_eq!(
            error.message,
            "classical functions cannot have requires clauses"
        );
    }
}

#[test]
fn retired_static_parameter_headers_report_the_marker_and_const_migration() {
    for source in [
        "pub fn f[static n:Nat](q:Q<Bit>)->Q<Bit>{q}",
        "pub fn f[const n:Nat,static U:Op<Bit>](q:Q<Bit>)->Q<Bit>{q}",
        "pub fn f[static n:Nat,const U:Op<Bit>](q:Q<Bit>)->Q<Bit>{q}",
    ] {
        let error = parse_module(source).unwrap_err();
        assert_eq!(
            error.message,
            "compile-time parameter headers use `const`; replace `static` with `const`"
        );
        let start = source.find("static").unwrap();
        assert_eq!(error.span, Span::new(start, start + "static".len()));
        check_token_prefixes(&source.replace("static", "const"), "migrated header");
    }
}

#[test]
fn retired_operation_spellings_report_the_original_token_and_migration() {
    for (body, token, message) in [
        (
            "adjoint(U,q)",
            "adjoint",
            "`adjoint(U, q)` is retired; use `adjoint(U)(q)`",
        ),
        (
            "g[repeat_op(2,U)](q)",
            "repeat_op",
            "`repeat_op(k, U)` is retired; use `power(U, k)`",
        ),
        (
            "repeat_static(2,U,q)",
            "repeat_static",
            "`repeat_static(k, U, q)` is retired; use `power(U, k)(q)`",
        ),
        (
            "adjoint(U)(adjoint(V,q))",
            "adjoint",
            "`adjoint(U, q)` is retired; use `adjoint(U)(q)`",
        ),
        (
            "g[adjoint(repeat_op(2,U))](q)",
            "repeat_op",
            "`repeat_op(k, U)` is retired; use `power(U, k)`",
        ),
        (
            "if 0 {q} else {repeat_static(0,U,q)}",
            "repeat_static",
            "`repeat_static(k, U, q)` is retired; use `power(U, k)(q)`",
        ),
    ] {
        // A later declaration, multibyte comment and CRLF must not shift spans.
        for prefix in ["", "// 位相\r\nunitary fn earlier(q:Q<Bit>)->Q<Bit>{q}\r\n"] {
            let source = format!("{prefix}unitary fn f(q:Q<Bit>)->Q<Bit>{{{body}}}");
            let error = parse_module(&source).unwrap_err();
            let start = if body == "adjoint(U)(adjoint(V,q))" {
                source.rfind(token).unwrap()
            } else {
                source.find(token).unwrap()
            };
            assert_eq!(
                error.span,
                Span::new(start, start + token.len()),
                "{source}"
            );
            assert_eq!(error.message, message);
        }
    }
    // Refuse the old keyword even when its argument list is incomplete.
    for body in ["adjoint(", "repeat_static(", "g[repeat_op("] {
        let source = format!("unitary fn f(q:Q<Bit>)->Q<Bit>{{{body}");
        assert!(
            parse_module(&source)
                .unwrap_err()
                .message
                .contains("is retired")
        );
    }
}

#[test]
fn capability_names_and_static_adjoint_control_share_the_existing_ast() {
    use qleisli::frontend::ast::{Access, Requirement, StaticOpKind};
    let source = "// 位相\r\nunitary fn f[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U), Adjointable(U), Controllable(U) { helper[controlled(adjoint(power(U,2)))](q) }";
    let module = parse_module(source).unwrap();
    for (constraint, (expected, spelling)) in module.decls[0].requires.iter().zip([
        (Access::Apply, "Applicable"),
        (Access::Adjoint, "Adjointable"),
        (Access::Controlled, "Controllable"),
    ]) {
        let Requirement::Access(constraint) = constraint else {
            panic!("access")
        };
        assert_eq!(constraint.access, expected);
        assert_eq!(
            &source[constraint.span.start..constraint.span.end],
            spelling
        );
    }
    let FnBody::Quantum(body) = &module.decls[0].body else {
        panic!("body")
    };
    let ExprKind::Call { static_args, .. } = &body.result.kind else {
        panic!("call")
    };
    let operation = &static_args[0];
    let StaticOpKind::Controlled(inner) = &operation.kind else {
        panic!("controlled")
    };
    assert!(matches!(inner.kind, StaticOpKind::Inverse(_)));
    assert_eq!(
        &source[operation.span.start..operation.span.end],
        "controlled(adjoint(power(U,2)))"
    );
}

#[test]
fn retired_capability_names_and_descriptions_report_precise_replacements() {
    for (old, new) in [
        ("Apply", "Applicable"),
        ("Adjoint", "Adjointable"),
        ("Controlled", "Controllable"),
    ] {
        let source = format!(
            "// 位相\r\nunitary fn f[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires {old}(U){{q}}"
        );
        let error = parse_module(&source).unwrap_err();
        assert_eq!(&source[error.span.start..error.span.end], old);
        assert_eq!(
            error.message,
            format!("`{old}(U)` is retired; use `{new}(U)`")
        );
    }
    for (body, token, replacement) in [
        ("inverse(U)(q)", "inverse", "adjoint(U)(q)"),
        ("helper[inverse_op(U)](q)", "inverse_op", "adjoint(U)"),
        (
            "helper[controlled_op(U)](q)",
            "controlled_op",
            "controlled(U)",
        ),
    ] {
        let source = format!("unitary fn f(q:Q<Bit>)->Q<Bit>{{{body}}}");
        let error = parse_module(&source).unwrap_err();
        assert_eq!(&source[error.span.start..error.span.end], token);
        assert!(error.message.contains(replacement));
    }
}

#[test]
fn new_capability_words_remain_contextual_identifiers() {
    for word in ["Applicable", "Adjointable", "Controllable"] {
        let source = format!(
            "pub unitary fn {word}[const {word}:Nat](q:Q<Bit>)->Q<Bit> requires {word} >= 0 {{q}}"
        );
        let module = parse_module(&source).unwrap();
        assert_eq!(module.decls[0].name.text, word);
        assert!(matches!(
            module.decls[0].requires[0],
            qleisli::frontend::ast::Requirement::Predicate(_)
        ));
    }
}
