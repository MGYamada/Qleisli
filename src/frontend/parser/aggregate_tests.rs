//! Constructor/member syntax, original byte spans and existing parse budgets.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;

#[test]
fn qualified_constructor_spans_and_written_fields_are_original() {
    let text = "// λ\nfn f()->Unit{ alias /* root */ :: Color :: Green }";
    let module = parse_module(text).unwrap();
    let FnBody::Quantum(body) = &module.decls[0].body else {
        panic!()
    };
    let ExprKind::Variant(value) = &body.result.kind else {
        panic!()
    };
    assert_eq!(value.type_name.text, "alias::Color");
    assert_eq!(
        &text[value.type_name.span.start..value.type_name.span.end],
        "alias /* root */ :: Color"
    );
    assert_eq!(
        &text[value.variant.span.start..value.variant.span.end],
        "Green"
    );
    let module = parse_module("fn f()->Unit{P{right:1,left:0,}.left}").unwrap();
    let FnBody::Quantum(body) = &module.decls[0].body else {
        panic!()
    };
    let ExprKind::Field { receiver, field } = &body.result.kind else {
        panic!()
    };
    assert_eq!(field.text, "left");
    let ExprKind::Record(record) = &receiver.kind else {
        panic!()
    };
    assert_eq!(
        record
            .fields
            .iter()
            .map(|f| f.name.text.as_str())
            .collect::<Vec<_>>(),
        ["right", "left"]
    );
}

#[test]
fn records_do_not_steal_if_or_fold_body_braces() {
    for source in [
        "fn f(b:Bit)->Bit{if b {1}else{0}}",
        "fn f(b:Bit)->Bit{if not b {1}else{0}}",
        "fn f(b:Bit)->Bit{if (P{bit:b}.bit) {1}else{0}}",
        "fn f(b:Bit)->Bit{for static i in 0..1 carry x=b {yield x}}",
        "fn f(b:Bit)->Bit{for static i in 0..1 carry x=(P{bit:b}.bit) {yield x}}",
    ] {
        parse_module(source).unwrap();
    }
}

#[test]
fn methods_payloads_shorthand_updates_and_static_variant_arguments_stay_unavailable() {
    for source in [
        "fn f()->Unit{P{a}}",
        "fn f()->Unit{P{..old}}",
        "fn f()->Unit{Color::Red[]}",
    ] {
        assert!(parse_module(source).is_err(), "{source}");
    }
    let error = parse_module("fn f(p:Unit)->Unit{p.method()}").unwrap_err();
    assert!(error.message.contains("method receiver syntax"));
    assert!(error.message.contains("explicit `excl ...` or `ctrl ...`"));
    // A qualified call retains its function category, including a type-like name.
    let m = parse_module("fn f()->Unit{Color::Red()}").unwrap();
    let FnBody::Quantum(b) = &m.decls[0].body else {
        panic!()
    };
    assert!(matches!(b.result.kind, ExprKind::Call { .. }));
}

#[test]
fn postfix_and_record_trees_share_existing_depth_and_field_limits() {
    for prefix in ["fn", "classical fn"] {
        let chain = format!("{prefix} f(p:Unit)->Unit{{p{}}}", ".a".repeat(64));
        assert!(
            parse_module(&chain)
                .unwrap_err()
                .message
                .contains("64-level")
        );
        let nested = format!(
            "{prefix} f()->Unit{{{}0{}}}",
            "P{a:".repeat(65),
            "}".repeat(65)
        );
        assert!(
            parse_module(&nested)
                .unwrap_err()
                .message
                .contains("64-level")
        );
        let fields = (0..65)
            .map(|n| format!("f{n}:0"))
            .collect::<Vec<_>>()
            .join(",");
        assert!(parse_module(&format!("{prefix} f()->Unit{{P{{{fields}}}}}")).is_err());
    }
}
