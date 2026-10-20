//! Public profile and accessor regressions for the internal shared type migration.
use qleisli::frontend::compile::{ParsedProgram, SourceType};
use qleisli::frontend::parser::parse_module;
use std::collections::BTreeMap;

fn parsed(text: &str) -> ParsedProgram {
    ParsedProgram::parse(
        qleisli::edition::Edition::E2026,
        BTreeMap::from([("main".into(), text.into())]),
    )
    .unwrap()
}
fn signature(ty: &SourceType) -> String {
    if ty.kind() == "tuple" {
        format!(
            "({})",
            ty.fields()
                .iter()
                .map(signature)
                .collect::<Vec<_>>()
                .join(",")
        )
    } else {
        assert!(ty.fields().is_empty());
        format!("{}:{}:{}", ty.kind(), ty.width().unwrap(), ty.is_quantum())
    }
}

#[test]
fn concrete_accessor_views_preserve_data_owners_nesting_and_unit() {
    let program = parsed(
        "pub unitary fn f(q: Q<Bit>, r: Q<Bits<1>>, z: Q<Bits<0>>, c: Bit, d: Bits<1>, e: Bits<0>) -> ((Q<Bit>,Q<Bits<1>>),(Q<Bits<0>>,Bit),Bits<1>,Bits<0>,Unit) { ((q,r),(z,c),d,e,()) }",
    );
    let graph = program
        .instantiate("main::f", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap();
    let body = &graph.definitions()[graph.root()];
    assert_eq!(
        body.inputs()
            .iter()
            .map(|v| signature(v.ty()))
            .collect::<Vec<_>>(),
        [
            "bit:1:true",
            "bits:1:true",
            "bits:0:true",
            "bit:1:false",
            "bits:1:false",
            "bits:0:false"
        ]
    );
    assert_eq!(
        signature(body.output().ty()),
        "((bit:1:true,bits:1:true),(bits:0:true,bit:1:false),bits:1:false,bits:0:false,unit:0:false)"
    );
    assert!(!body.output().ty().is_quantum());
    assert_eq!(body.output().ty().width(), None);
    assert_eq!(
        body.inputs()[2].identity(),
        body.output().fields()[1].fields()[0].identity()
    );
    assert!(body.inputs()[2].identity().is_some());
    assert_ne!(body.inputs()[0].ty(), body.inputs()[1].ty());
    assert_ne!(body.inputs()[2].ty(), body.inputs()[5].ty());
    assert_ne!(body.inputs()[5].ty(), body.output().fields()[4].ty());
}

#[test]
fn ordinary_types_share_the_sized_signature_classifier_without_general_basis_support() {
    for source in [
        "pub unitary fn f(x: Unit) -> Unit { x }",
        "pub unitary fn f(x: Bit) -> Bit { x }",
        "pub unitary fn f(x: Bits<1>) -> Bits<1> { x }",
        "pub unitary fn f(q: Q<Unit>) -> Q<Unit> { q }",
        "pub unitary fn f(q: Q<(Unit,Unit)>) -> Q<(Unit,Unit)> { q }",
    ] {
        parsed(source);
    }
    // Coherent lifting preserves the complete zero-width input/output trees;
    // this is an explicit basis map, never an implicit same-width coercion.
    let source = "pub unitary fn f(q: Q<(Unit,Unit)>) -> Q<Unit> { basis q as ((),u) { u } }";
    let program = parsed(source);
    assert_eq!(program.source("main"), Some(source));
    assert_eq!(program.syntax("main"), Some(&parse_module(source).unwrap()));
    let graph = program
        .instantiate("main::f", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap();
    let body = &graph.definitions()[graph.root()];
    assert!(body.inputs()[0].ty().is_quantum());
    assert_eq!(
        signature(body.inputs()[0].ty().quantum_basis().unwrap()),
        "(unit:0:false,unit:0:false)"
    );
    assert_eq!(signature(body.output().ty()), "unit:0:true");
    let lift = body
        .steps()
        .iter()
        .find(|step| step.kind() == "lift_basis")
        .unwrap();
    assert_eq!(lift.basis_table(), Some(&[0][..]));
    assert_eq!(
        &source[lift.span().start..lift.span().end],
        "basis q as ((),u) { u }"
    );
    graph.lower_raw().unwrap();
}

#[test]
fn symbolic_sizes_keep_exact_owner_shape_and_canonical_mismatch_diagnostics() {
    parsed("pub unitary fn f[const n: Nat](q: Q<Bits<n+1>>) -> Q<Bits<1+n>> { q }");
    for (source, message) in [
        (
            "pub unitary fn f(q: Q<Bits<1>>) -> Q<Bit> { q }",
            "type or tuple/size shape mismatch: expected `Q<Bit>`, found `Q<Bits<1>>`",
        ),
        (
            "pub unitary fn f(c: Bits<0>) -> Unit { c }",
            "type or tuple/size shape mismatch: expected `Unit`, found `Bits<0>`",
        ),
        (
            "pub unitary fn f(c: Bit) -> Q<Bit> { c }",
            "type or tuple/size shape mismatch: expected `Q<Bit>`, found `Bit`",
        ),
        (
            "pub unitary fn f(q: Q<Bit>) -> Bit { q }",
            "type or tuple/size shape mismatch: expected `Bit`, found `Q<Bit>`",
        ),
    ] {
        let e = ParsedProgram::parse(
            qleisli::edition::Edition::E2026,
            BTreeMap::from([("main".into(), source.into())]),
        )
        .unwrap_err();
        assert_eq!(e.code(), "type");
        assert_eq!(e.message(), message);
    }
}

#[test]
fn common_basis_empty_constructor_uses_its_exact_ordinary_signature() {
    for source in [
        " pub unitary fn f(q:Q<Unit>)->Q<Bits<0>>{basis q as () {empty_bits()}}",
        " classical fn label()->Bits<0>{empty_bits()} pub unitary fn f(q:Q<Unit>)->Q<Bits<0>>{basis q as () {label()}}",
        "classical fn empty_bits()->Bit{1} pub isometry fn f(q:Q<Unit>)->Q<Bit>{basis q as () {empty_bits()}}",
    ] {
        let program = parsed(source);
        assert_eq!(program.source("main"), Some(source));
        assert_eq!(program.syntax("main"), Some(&parse_module(source).unwrap()));
    }
    // Matching physical width grants no implicit conversion to the Unit basis.
    let source = " pub unitary fn f(q:Q<Unit>)->Q<Unit>{basis q as () {empty_bits()}}";
    let error = ParsedProgram::parse(
        qleisli::edition::Edition::E2026,
        BTreeMap::from([("main".into(), source.into())]),
    )
    .unwrap_err();
    assert_eq!(error.code(), "type");
    assert!(
        error
            .message()
            .contains("expected `Q<Unit>`, found `Q<Bits<0>>`")
    );
}

#[test]
fn common_basis_empty_constructor_does_not_admit_other_calls_or_local_capture() {
    for (source, code, message) in [
        (
            "pub unitary fn f(q:Q<Unit>)->Q<Bits<0>>{basis q as () {std::classical::empty_bits()}}",
            "name",
            "call the language primitive `empty_bits` without an import",
        ),
        (
            " pub unitary fn f(q:Q<Unit>)->Q<Bits<0>>{basis q as () {empty_bits(())}}",
            "arity",
            "argument arity mismatch",
        ),
        (
            "use std::structure::empty; pub unitary fn f(q:Q<Unit>)->Q<Unit>{basis q as () {empty()}}",
            "type",
            "basis expression requires a classical function",
        ),
        (
            "use std::state::init0; pub unitary fn f(q:Q<Unit>)->Q<Unit>{basis q as () {init0()}}",
            "type",
            "basis expression requires a classical function",
        ),
        (
            " fn ordinary()->Bits<0>{empty_bits()} pub unitary fn f(q:Q<Unit>)->Q<Bits<0>>{basis q as () {ordinary()}}",
            "type",
            "basis expression requires a classical function",
        ),
        (
            "pub unitary fn f(q:Q<Bit>)->Q<Bit>{basis q as empty_bits {empty_bits()}}",
            "type",
            "a basis value is not callable",
        ),
        (
            " pub unitary fn f(q:Q<Unit>,outside:Bits<0>)->Q<Bits<0>>{basis q as () {outside}}",
            "name",
            "unbound basis value",
        ),
    ] {
        let error = ParsedProgram::parse(
            qleisli::edition::Edition::E2026,
            BTreeMap::from([("main".into(), source.into())]),
        )
        .unwrap_err();
        assert_eq!(error.code(), code, "{source}: {error}");
        assert!(error.message().contains(message), "{source}: {error}");
        assert_eq!(error.module(), Some("main"));
        assert!(error.span().start < error.span().end && error.span().end <= source.len());
    }
}
