mod common;

use common::SourceRoot;
use qleisli::frontend::compile::{check_project, compile_project};
use qleisli::frontend::documentation::{DocStyle, render_markdown};
use qleisli::frontend::lexer::lex;
use qleisli::frontend::parser::{parse_documented_module, parse_module};

#[test]
fn rust_style_docs_attach_to_modules_imports_and_functions_in_source_order() {
    let source = "//! Module.\n/*! More module. */\n\
        /// Import.\nuse std::quantum::h;\n\
        /// Outer.\n/** More outer. */\npub unitary fn f(q: Q<Bit>) -> Q<Bit> {\n\
        //! Inner.\n/*! More inner. */\nh(q)\n}\n\
        classical fn identity(x: Bit) -> Bit { //! Basis inner.\n x }";
    let parsed = parse_documented_module(source).unwrap();
    assert_eq!(parsed.syntax, parse_module(source).unwrap());
    assert_eq!(parsed.module_docs.len(), 2);
    assert_eq!(parsed.module_docs[0].text, " Module.");
    assert_eq!(parsed.module_docs[1].text, " More module. ");
    assert_eq!(parsed.import_docs.len(), 1);
    assert_eq!(parsed.import_docs[0][0].text, " Import.");
    let docs = &parsed.declaration_docs[0];
    assert_eq!(
        docs.iter().map(|d| d.style).collect::<Vec<_>>(),
        vec![
            DocStyle::Outer,
            DocStyle::Outer,
            DocStyle::Inner,
            DocStyle::Inner
        ]
    );
    assert_eq!(
        docs.iter().map(|d| d.text.as_str()).collect::<Vec<_>>(),
        vec![" Outer.", " More outer. ", " Inner.", " More inner. "]
    );
    assert_eq!(parsed.declaration_docs[1][0].text, " Basis inner.");
    assert_eq!(&source[docs[0].span.start..docs[0].span.end], "/// Outer.");
}

#[test]
fn ordinary_and_nested_comment_delimiters_follow_rust_distinctions() {
    for prefix in [
        "//// not docs\n",
        "/**/",
        "/***/",
        "/**** ordinary */",
        "/* outer /*! inner */ /** nested */ */",
    ] {
        let parsed =
            parse_documented_module(&format!("{prefix}classical fn f() -> Bit {{ 0 }}")).unwrap();
        assert!(parsed.module_docs.is_empty(), "{prefix}");
        assert!(parsed.declaration_docs[0].is_empty(), "{prefix}");
    }
    let parsed = parse_documented_module(
        "/*!*/ /** outer /* nested */ tail */ classical fn f() -> Bit { 0 }",
    )
    .unwrap();
    assert_eq!(parsed.module_docs[0].text, "");
    assert_eq!(
        parsed.declaration_docs[0][0].text,
        " outer /* nested */ tail "
    );
    let parsed =
        parse_documented_module("//!! bang\n///! outer bang\nclassical fn f() -> Bit { 0 }")
            .unwrap();
    assert_eq!(parsed.module_docs[0].text, "! bang");
    assert_eq!(parsed.declaration_docs[0][0].text, "! outer bang");
    assert!(
        parse_documented_module("//! empty module")
            .unwrap()
            .syntax
            .decls
            .is_empty()
    );
}

#[test]
fn misplaced_documentation_is_rejected_in_both_parse_entry_points() {
    for source in [
        "/// orphan",
        "/** orphan */",
        "/// outer\n//! inner after outer\nclassical fn f() -> Bit { 0 }",
        "use std::quantum::h; //! late module",
        "pub /// inside header\nclassical fn f() -> Bit { 0 }",
        "classical fn f(/// parameter\nx: Bit) -> Bit { x }",
        "classical fn f() -> Bit { /// expression\n0 }",
        "classical fn f() -> Bit { 0 //! after body value\n }",
        "unitary fn f() -> Bit { let b = 1; //! after statement\n b }",
        "unitary fn f() -> Bit { if 1 { //! expression block\n 1 } else { 0 } }",
    ] {
        let error = parse_documented_module(source).unwrap_err();
        assert!(error.message.contains("documentation"), "{source}: {error}");
        assert_eq!(parse_module(source).unwrap_err(), error);
        assert!(source[error.span.start..error.span.end].starts_with('/'));
    }
}

#[test]
fn doc_text_normalizes_crlf_but_preserves_utf8_source_spans() {
    let source = "//! 日本語\r\n/** α\r\n β */\r\nclassical fn f() -> Bit { 0 }";
    let parsed = parse_documented_module(source).unwrap();
    assert_eq!(parsed.module_docs[0].text, " 日本語");
    assert_eq!(parsed.module_docs[0].span.end, "//! 日本語".len());
    let doc = &parsed.declaration_docs[0][0];
    assert_eq!(doc.text, " α\n β ");
    assert_eq!(&source[doc.span.start..doc.span.end], "/** α\r\n β */");
    assert_eq!(
        parsed.syntax.decls[0].span.start,
        source.find("classical").unwrap()
    );
    for source in [
        "//! bare\r",
        "/// bare\r\nclassical fn f() -> Bit { 0 }",
        "/*! bare\r */",
    ] {
        if source.contains("\r\n") {
            parse_module(source).unwrap();
        } else {
            let error = parse_module(source).unwrap_err();
            assert!(error.message.contains("bare carriage return"));
            assert_eq!(&source[error.span.start..error.span.end], "\r");
        }
    }
    assert!(
        parse_module("// ordinary\rclassical fn hidden() -> Bit { 0 }")
            .unwrap_err()
            .message
            .contains("bare carriage return")
    );
    assert!(parse_module("/* ordinary\r */classical fn visible() -> Bit { 0 }").is_err());
}

#[test]
fn all_comment_forms_keep_unicode_rejection_and_unclosed_block_diagnostics() {
    for (prefix, suffix) in [
        ("//", "\n"),
        ("//!", "\n"),
        ("///", "\n"),
        ("/*", "*/"),
        ("/*!", "*/"),
        ("/** ", "*/"),
    ] {
        for character in ['\u{202e}', '\u{2028}', '\u{0085}', '\u{00a0}', '\0'] {
            let source = format!("{prefix} text{character}{suffix}classical fn f() -> Bit {{ 0 }}");
            let error = lex(&source).unwrap_err();
            assert_eq!(
                &source[error.span.start..error.span.end],
                character.to_string()
            );
        }
    }
    for source in ["/*", "/** unfinished", "/*! /* nested */", "/* /* */"] {
        let error = lex(source).unwrap_err();
        assert_eq!(error.message, "unterminated block comment");
        assert_eq!((error.span.start, error.span.end), (0, source.len()));
    }
}

#[test]
fn deeply_nested_comments_are_iterative_and_do_not_hide_following_syntax() {
    let source = format!(
        "{} text {}classical fn f() -> Bit {{ 1 }}",
        "/*".repeat(20_000),
        "*/".repeat(20_000)
    );
    assert_eq!(parse_module(&source).unwrap().decls.len(), 1);
    let error = parse_module(&(source + " @")).unwrap_err();
    assert!(error.message.contains("unexpected character"));
}

#[test]
fn documentation_neither_changes_ir_nor_authorizes_invalid_ownership() {
    let plain = SourceRoot::new(
        "use std::quantum::init0; use std::quantum::h; use std::observe::measure_z; observe fn main() -> Bit { measure_z(h(init0())) }",
    );
    let documented = SourceRoot::new(
        "//! A program.\nuse std::quantum::init0; use std::quantum::h; use std::observe::measure_z; /// Coin.\nobserve fn main() -> Bit { /*! Body. */ measure_z(h(init0())) }",
    );
    assert_eq!(
        compile_project(&plain.0).unwrap().raw(),
        compile_project(&documented.0).unwrap().raw()
    );
    let invalid = SourceRoot::new(
        "use std::quantum::join; /// Verified: copying this owner is safe.\npub unitary fn copy(q: Q<Bit>) -> Q<(Bit,Bit)> { join(q,q) }",
    );
    parse_documented_module(&std::fs::read_to_string(invalid.0.join("main.qli")).unwrap()).unwrap();
    assert!(check_project(&invalid.0).is_err());
}

#[test]
fn markdown_includes_private_docs_and_uses_safe_signature_fences() {
    let source = "//! Module text.\n/// Function text.\npub /* ``` */ classical fn f(x: Bit) -> Bit { x }\n/// Private text.\nclassical fn hidden() -> Bit { 0 }";
    let rendered = render_markdown(source).unwrap();
    assert!(rendered.contains("Module text."));
    assert!(rendered.contains("f (public)"));
    assert!(rendered.contains("hidden (private)"));
    assert!(rendered.contains("Private text."));
    assert!(rendered.contains("````qli\npub /* ``` */ classical fn f(x: Bit) -> Bit\n````"));
    assert!(!rendered.contains("{ x }"));
}

#[test]
fn unfinished_comment_blocks_cannot_swallow_later_declarations() {
    for comment in ["```", "~~~~rust", "<!--", "<script>", "``````\n/// <!--"] {
        let source = format!(
            "/// {comment}\nclassical fn hidden()->Bit{{0}}\n/// visible\npub classical fn visible()->Bit{{1}}"
        );
        let rendered = render_markdown(&source).unwrap();
        // Independently scan fenced blocks: the later heading must occur at
        // block level, with the complete signature in its own qli block.
        let mut fence = None;
        let mut heading = false;
        for line in rendered.lines() {
            let ticks = line.bytes().take_while(|b| *b == b'`').count();
            match fence {
                Some(n) if ticks >= n && line[ticks..].trim().is_empty() => fence = None,
                None if ticks >= 3 => fence = Some(ticks),
                None if line == "## visible (public)" => heading = true,
                _ => {}
            }
        }
        assert!(heading && fence.is_none(), "{rendered}");
        assert!(rendered.contains("```qli\npub classical fn visible()->Bit\n```"));
    }
}

#[test]
fn every_bundled_module_and_public_or_private_definition_has_documentation() {
    let sources = [
        include_str!("../stdlib/src/basis.qli"),
        include_str!("../stdlib/src/transform.qli"),
        include_str!("../stdlib/src/reflection.qli"),
        include_str!("../stdlib/src/measurement.qli"),
    ];
    let mut public = 0;
    let mut private = 0;
    for source in sources {
        let parsed = parse_documented_module(source).unwrap();
        assert!(
            parsed
                .module_docs
                .iter()
                .any(|doc| !doc.text.trim().is_empty())
        );
        assert_eq!(parsed.declaration_docs.len(), parsed.syntax.decls.len());
        for (decl, docs) in parsed.syntax.decls.iter().zip(parsed.declaration_docs) {
            assert!(
                docs.iter().any(|doc| !doc.text.trim().is_empty()),
                "{}",
                decl.name.text
            );
            if decl.public {
                public += 1;
            } else {
                private += 1;
            }
        }
    }
    assert_eq!((public, private), (9, 1));
}

#[test]
fn common_parser_shares_documentation_attachment_with_sized_source() {
    use qleisli::frontend::compile::ParsedProgram;
    use std::collections::BTreeMap;
    let source = "//! 日本語\r\n/** outer /* nested */ */ pub unitary fn f(q: Q<Bit>) -> Q<Bit> { /*! α\r\nβ */ q }";
    let documented = parse_documented_module(source).unwrap();
    assert_eq!(documented.module_docs[0].text, " 日本語");
    assert_eq!(documented.declaration_docs[0][1].text, " α\nβ ");
    let sized = ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap();
    assert_eq!(sized.source("main"), Some(source));
    assert_eq!(sized.syntax("main"), Some(&documented.syntax));
    // Sized source now uses the same declaration attachment boundary.
    let misplaced = "pub unitary fn f(q: Q<Bit>) -> Q<Bit> { /// misplaced\n q }";
    assert!(
        parse_module(misplaced)
            .unwrap_err()
            .message
            .contains("documentation")
    );
    let error =
        ParsedProgram::parse(BTreeMap::from([("main".into(), misplaced.into())])).unwrap_err();
    let common = parse_module(misplaced).unwrap_err();
    assert_eq!(
        (error.span(), error.message()),
        (common.span, common.message.as_str())
    );
}
