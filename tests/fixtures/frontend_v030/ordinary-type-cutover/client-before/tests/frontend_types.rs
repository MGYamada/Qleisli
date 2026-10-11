//! Public profile and accessor regressions for the internal shared type migration.
use qleisli::frontend::sized::{ParsedProgram, SourceType};
use std::collections::BTreeMap;

fn parsed(text: &str) -> ParsedProgram {
    ParsedProgram::parse(BTreeMap::from([("main".into(), text.into())])).unwrap()
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
fn concrete_accessor_views_preserve_data_owners_nesting_and_empty_tuples() {
    let program = parsed(
        "pub unitary fn f(q: Q<Bit>, r: Q<Bits<1>>, z: Q<Bits<0>>, c: CBit, d: CBits<1>, e: CBits<0>) -> ((Q<Bit>,Q<Bits<1>>),(Q<Bits<0>>,CBit),CBits<1>,CBits<0>,()) { ((q,r),(z,c),d,e,()) }",
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
            "cbit:1:false",
            "cbits:1:false",
            "cbits:0:false"
        ]
    );
    assert_eq!(
        signature(body.output().ty()),
        "((bit:1:true,bits:1:true),(bits:0:true,cbit:1:false),cbits:1:false,cbits:0:false,())"
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
fn shared_identity_does_not_extend_the_sized_surface_profile() {
    for source in [
        "pub unitary fn f(x: Unit) -> Unit { x }",
        "pub unitary fn f(q: Q<Unit>) -> Q<Unit> { q }",
        "pub unitary fn f(x: Bit) -> Bit { x }",
        "pub unitary fn f(x: Bits<1>) -> Bits<1> { x }",
    ] {
        let e = ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap_err();
        assert_eq!(e.code(), "unsupported", "{e}");
        assert!(e.message().starts_with("sized preparation profile:"));
    }
}

#[test]
fn symbolic_sizes_keep_exact_owner_shape_and_legacy_mismatch_diagnostics() {
    parsed("pub unitary fn f[static n: Nat](q: Q<Bits<n+1>>) -> Q<Bits<1+n>> { q }");
    for (source, message) in [
        (
            "pub unitary fn f(q: Q<Bits<1>>) -> Q<Bit> { q }",
            "type or tuple/size shape mismatch: expected Bit, found Bits(Linear { constant: 1, terms: {} })",
        ),
        (
            "pub unitary fn f(c: CBits<0>) -> () { c }",
            "type or tuple/size shape mismatch: expected Tuple([]), found CBits(Linear { constant: 0, terms: {} })",
        ),
        (
            "pub unitary fn f(c: CBit) -> Q<Bit> { c }",
            "type or tuple/size shape mismatch: expected Bit, found CBit",
        ),
        (
            "pub unitary fn f(q: Q<Bit>) -> CBit { q }",
            "type or tuple/size shape mismatch: expected CBit, found Bit",
        ),
    ] {
        let e = ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap_err();
        assert_eq!(e.code(), "type");
        assert_eq!(e.message(), message);
    }
}
