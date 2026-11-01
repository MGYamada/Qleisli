//! Exact-label syntax and original order only, not coherent execution evidence.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;

#[test]
fn grouped_quantum_match_retains_the_keyword_token_separately() {
    let source =
        "fn f(s:Q<E>,q:Q<Bit>)->(Q<E>,Q<Bit>){((/* λ */ qmatch(s,q){E::A=>keep,E::B=>keep}))}";
    let syntax = parse_module(source).unwrap();
    assert_eq!(parse_bounded_module(source).unwrap(), syntax);
    let FnBody::Quantum(body) = &syntax.decls[0].body else {
        panic!()
    };
    let ExprKind::QuantumMatch(selection) = &body.result.kind else {
        panic!()
    };
    assert_eq!(selection.keyword.start, source.find("qmatch").unwrap());
    assert_eq!(
        &source[selection.keyword.start..selection.keyword.end],
        "qmatch"
    );
    assert!(body.result.span.start < selection.keyword.start);
    assert_eq!(
        &source[body.result.span.start..body.result.span.start + 2],
        "(("
    );
}

#[test]
fn quantum_match_preserves_written_labels_operations_and_original_spans() {
    let source = "// λ\nfn f(s:Q<E>,q:Q<Bit>)->(Q<E>,Q<Bit>){qmatch(s,q){alias /* original */ :: E :: C=>keep,E::A=>h,E::B=>global_phase_eighth,}}";
    let syntax = parse_module(source).unwrap();
    assert_eq!(parse_bounded_module(source).unwrap(), syntax);
    let FnBody::Quantum(body) = &syntax.decls[0].body else {
        panic!()
    };
    let ExprKind::QuantumMatch(selection) = &body.result.kind else {
        panic!()
    };
    let labels = selection
        .arms
        .iter()
        .map(|arm| {
            let QuantumLabel::Variant(label) = &arm.label else {
                panic!()
            };
            label.variant.text.as_str()
        })
        .collect::<Vec<_>>();
    assert_eq!(labels, ["C", "A", "B"]);
    let QuantumLabel::Variant(first) = &selection.arms[0].label else {
        panic!()
    };
    assert_eq!(first.type_name.text, "alias::E");
    assert_eq!(
        &source[first.type_name.span.start..first.type_name.span.end],
        "alias /* original */ :: E"
    );
    assert_eq!(
        &source[first.variant.span.start..first.variant.span.end],
        "C"
    );
    for (arm, name) in selection
        .arms
        .iter()
        .zip(["keep", "h", "global_phase_eighth"])
    {
        assert_eq!(
            &source[arm.operation.span.start..arm.operation.span.end],
            name
        );
    }
    let syntax = parse_module(
        "fn f(s:Q<Bits<2>>,q:Q<Bit>)->(Q<Bits<2>>,Q<Bit>){qmatch(s,q){3=>h,0=>h,2=>h,1=>h}}",
    )
    .unwrap();
    let FnBody::Quantum(body) = &syntax.decls[0].body else {
        panic!()
    };
    let ExprKind::QuantumMatch(selection) = &body.result.kind else {
        panic!()
    };
    let ordinals = selection
        .arms
        .iter()
        .map(|arm| {
            let QuantumLabel::Ordinal(label) = &arm.label else {
                panic!()
            };
            *label
        })
        .collect::<Vec<_>>();
    assert_eq!(ordinals, [3, 0, 2, 1]);
}

#[test]
fn convenience_patterns_and_dynamic_arm_bodies_are_not_silently_desugared() {
    for arms in [
        "_=>h",
        "0..2=>h",
        "E::A(x)=>h",
        "E::A if 1=>h",
        "00=>h",
        "4294967296=>h",
        "0=>h(q)",
        "0=>{q}",
        "0=>controlled(h)",
    ] {
        let source = format!("fn f(s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){{qmatch(s,q){{{arms}}}}}");
        assert!(parse_module(&source).is_err(), "{source}");
    }
    // Existing qif syntax and its fixed 0/1 written order are unchanged.
    parse_module("fn f(s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){qif(s,q){0=>h,1=>h}}").unwrap();
    assert!(parse_module("fn f(s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){qif(s,q){1=>h,0=>h}}").is_err());
}
