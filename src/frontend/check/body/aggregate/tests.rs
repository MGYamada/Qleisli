//! Original-source judgments only; successful preparation is not native execution.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;

fn prepare(sources: &[(&str, &str)]) -> Result<CheckedProgram> {
    let syntax = sources
        .iter()
        .map(|(_, source)| crate::frontend::parser::parse_module(source).unwrap())
        .collect::<Vec<_>>();
    program_with_sources(
        sources
            .iter()
            .zip(&syntax)
            .map(|((name, _), syntax)| (*name, syntax))
            .collect(),
        sources.iter().copied().collect(),
        SourceLimits::finite(),
        |_, _, _, _, _, _, _| Ok(()),
    )
    .map(|(checked, ())| checked)
}
fn checked(text: &str) -> CheckedProgram {
    prepare(&[("main", text)]).unwrap()
}
fn failure(text: &str) -> SourceError {
    prepare(&[("main", text)]).unwrap_err()
}

#[test]
fn both_ordinary_grammars_keep_enum_record_and_empty_nominal_values() {
    checked(
        "enum Color{Red,Green,Blue} struct Packet{tag:Color,bit:Bit,zero:Unit} struct Empty{}
        classical fn selected()->Color{Color::Green}
        classical fn packet()->Packet{Packet{bit:1,zero:(),tag:selected()}}
        classical fn field(p:Packet)->Color{p.tag}
        fn empty()->Empty{Empty{}}
        fn main()->(Color,Bit,Empty){let p=packet();(p.tag,p.bit,empty())}",
    );
}

#[test]
fn original_reexport_paths_and_field_privacy_survive_constructor_resolution() {
    let leaf = "pub enum Color{Red,Green,Blue} pub struct Packet{pub tag:Color,hidden:Unit} pub fn make()->Packet{Packet{hidden:(),tag:Color::Red}}";
    let alias = "pub use leaf::Color; pub use leaf::Packet;";
    prepare(&[("leaf",leaf),("alias",alias),("main","fn main()->alias::Color{leaf::make().tag} fn color()->alias::Color{alias::Color::Blue}")]).unwrap();
    for main in [
        "fn main()->Unit{leaf::make().hidden}",
        "fn main()->alias::Packet{alias::Packet{tag:alias::Color::Red,hidden:()}}",
        "classical fn main(p:alias::Packet)->Unit{p.hidden}",
    ] {
        let error = prepare(&[("leaf", leaf), ("alias", alias), ("main", main)]).unwrap_err();
        assert_eq!(error.code, "visibility", "{error:?}");
        assert_eq!(&main[error.span.start..error.span.end], "hidden");
    }
}

#[test]
fn every_field_is_explicit_exact_and_unique_in_both_grammars() {
    for kind in ["fn", "classical fn"] {
        for (value, message) in [
            ("P{a:0}", "missing field b"),
            ("P{a:0,a:1,b:1}", "duplicate field a"),
            ("P{a:0,b:1,c:0}", "unknown field c"),
            ("P{a:(),b:1}", "expected"),
        ] {
            let error = failure(&format!(
                "struct P{{a:Bit,b:Bit}} {kind} main()->P{{{value}}}"
            ));
            assert_eq!(error.code, "type", "{error:?}");
            assert!(error.message.contains(message), "{error:?}");
        }
    }
}

#[test]
fn quantum_initializers_and_projection_cannot_hide_ownership_or_observation() {
    for text in [
        "struct P{bit:Bit} unitary fn f(q:Q<Bit>)->P{P{bit:q}}",
        "struct P{bit:Bit} fn f(q:Q<P>)->Bit{q.bit}",
    ] {
        assert_eq!(failure(text).code, "type");
    }
    for effect in ["unitary", "isometry"] {
        let error = failure(&format!(
            "struct P{{bit:Bit}} pub {effect} fn f(q:Q<Bit>)->P{{P{{bit:measure_z(q)}}}}"
        ));
        assert_eq!(error.code, "effect", "{error:?}");
    }
    checked("struct P{bit:Bit} pub observe fn f(q:Q<Bit>)->P{P{bit:measure_z(q)}}");
}

#[test]
fn field_initializers_consume_owners_in_written_order() {
    let text = "struct Pair{a:Bit,b:Bit} observe fn f(q:Q<Bit>)->Pair{Pair{b:measure_z(q),a:measure_z(q)}}";
    let error = failure(text);
    assert_eq!(error.code, "ownership", "{error:?}");
    assert_eq!(error.span.start, text.rfind("q)").unwrap());
    checked("struct Pair{a:Bit,b:Bit} observe fn f(q:Q<Bit>)->Pair{Pair{b:measure_z(q),a:0}}");
}

#[test]
fn local_and_basis_names_never_fall_back_to_same_spelled_enum() {
    for text in [
        "enum Color{Red,Green} fn f[const Color:Basis]()->Color{Color::Red}",
        "enum Color{Red,Green} fn f(Color:Bit)->main::Color{Color::Red}",
        "struct Packet{bit:Bit} fn f(Packet:Bit)->main::Packet{Packet{bit:0}}",
    ] {
        let error = failure(text);
        assert_eq!(error.code, "type", "{error:?}");
        assert!(
            error
                .message
                .contains("concrete ordinary finite constructor type"),
            "{error:?}"
        );
    }
}

#[test]
fn constructor_categories_members_and_nominal_equality_are_exact() {
    for (text, message) in [
        (
            "enum Color{Red} fn f()->Color{Color{}}",
            "record construction",
        ),
        (
            "struct Packet{} fn f()->Packet{Packet::Red}",
            "variant construction",
        ),
        (
            "enum Color{Red} fn f()->Color{Color::Green}",
            "unknown variant",
        ),
        (
            "enum Color{Red} fn f(x:Color)->Bit{x.bit}",
            "ordinary record",
        ),
        (
            "struct P{bit:Bit} fn f(p:P)->Bit{p.absent}",
            "unknown field",
        ),
    ] {
        let error = failure(text);
        assert_eq!(error.code, "type");
        assert!(error.message.contains(message), "{error:?}");
    }
    for text in [
        "enum A{Only} enum B{Only} fn f()->B{A::Only}",
        "struct Empty{} fn f()->Unit{Empty{}}",
        "enum One{Only} fn f()->Bits<0>{One::Only}",
    ] {
        assert_eq!(failure(text).code, "type");
    }
}

#[test]
fn unused_initializers_retain_function_dependencies_and_effect_bounds() {
    let error = failure(
        "struct P{bit:Bit} observe fn read(q:Q<Bit>)->Bit{measure_z(q)} pub unitary fn unused(q:Q<Bit>)->P{P{bit:read(q)}} fn main()->Unit{()}",
    );
    assert_eq!(error.code, "effect", "{error:?}");
    let error = failure("struct P{bit:Bit} fn a()->P{P{bit:b().bit}} fn b()->P{P{bit:a().bit}}");
    assert_eq!(error.code, "cycle", "{error:?}");
}

#[test]
fn parsed_preparation_keeps_concrete_execution_gate() {
    let p = crate::frontend::compile::ParsedProgram::parse(
        crate::edition::Edition::E2026,
        BTreeMap::from([(
            "main".into(),
            "enum Color{Red,Green,Blue} pub fn main()->Color{Color::Green}".into(),
        )]),
    )
    .unwrap();
    let error = p
        .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
        .unwrap_err();
    assert_eq!(error.code(), "unsupported");
    assert!(error.to_string().contains("typed native transport"));
}
