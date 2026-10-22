//! Common source judgments; these tests do not grant nominal runtime acceptance.
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
        |_, _, _, _, _, _, _, _| Ok(()),
    )
    .map(|(checked, ())| checked)
}

fn failure(text: &str) -> SourceError {
    prepare(&[("main", text)]).unwrap_err()
}

#[test]
fn complete_match_checks_both_grammars_and_nested_nominal_results() {
    prepare(&[("main", "enum E{A,B,C} struct P{tag:E,flag:Bit} enum One{Only}
        classical fn flag(p:E)->Bit{match p{E::C=>0,E::A=>0,E::B=>1,}}
        classical fn once(p:One)->One{match p{One::Only=>p}}
        fn pick(b:Bit)->E{if b{E::B}else{E::C}}
        fn packet(p:E)->P{match p{E::A=>P{flag:0,tag:p},E::B=>{let b=flag(p);P{tag:p,flag:b}},E::C=>P{tag:p,flag:0}}}
        observe fn main(q:Q<Bit>)->Bit{let p=pick(measure_z(q));packet(p).flag}")]).unwrap();
}

#[test]
fn exact_coverage_is_checked_before_any_arm_is_selected() {
    for prefix in ["fn", "classical fn"] {
        for (arms, message) in [
            ("E::A=>0,E::B=>1", "missing variant C"),
            ("E::A=>0,E::B=>1,E::C=>0,E::B=>0", "duplicate match arm B"),
            ("E::A=>0,E::B=>1,E::D=>0", "unknown variant D"),
        ] {
            let source = format!("enum E{{A,B,C}} {prefix} f()->Bit{{match E::A{{{arms}}}}}");
            let error = failure(&source);
            assert_eq!(error.code, "type", "{error:?}");
            assert!(error.message.contains(message), "{error:?}");
            if message.starts_with("duplicate") {
                assert_eq!(&source[error.span.start..error.span.end], "B");
                assert_eq!(error.span.start, source.rfind("B=>0").unwrap());
            }
        }
    }
}

#[test]
fn label_identity_uses_original_declarations_through_aliases() {
    let leaf = "pub enum E{A,B,C}";
    let alias = "pub use leaf::E;";
    prepare(&[
        ("leaf", leaf),
        ("alias", alias),
        (
            "main",
            "classical fn f(p:leaf::E)->Bit{match p{alias::E::A=>0,leaf::E::B=>1,alias::E::C=>0}}",
        ),
    ])
    .unwrap();
    let wrong = prepare(&[
        ("leaf", leaf),
        ("other", leaf),
        (
            "main",
            "classical fn f(p:leaf::E)->Bit{match p{leaf::E::A=>0,other::E::B=>1,leaf::E::C=>0}}",
        ),
    ])
    .unwrap_err();
    assert_eq!(wrong.code, "type", "{wrong:?}");
    let private = prepare(&[
        ("leaf", "enum E{A,B}"),
        (
            "main",
            "fn f(p:Bit)->Bit{match p{leaf::E::A=>0,leaf::E::B=>1}}",
        ),
    ])
    .unwrap_err();
    assert_eq!(private.code, "visibility", "{private:?}");
    assert!(private.message.contains("not public"), "{private:?}");
}

#[test]
fn every_arm_must_return_the_same_full_type_tree() {
    for prefix in ["fn", "classical fn"] {
        for (result, arms) in [
            ("Unit", "E::A=>(),E::B=>1"),
            ("E", "E::A=>E::A,E::B=>F::A"),
            ("(Bit,Unit)", "E::A=>(0,()),E::B=>((),0)"),
        ] {
            let error = failure(&format!(
                "enum E{{A,B}} enum F{{A,B}} {prefix} f(p:E)->{result}{{match p{{{arms}}}}}"
            ));
            assert_eq!(error.code, "type", "{error:?}");
        }
    }
}

#[test]
fn ordinary_match_never_inspects_quantum_or_record_values_in_unused_code() {
    for (decl, ty, label) in [
        ("enum E{A}", "Q<E>", "E::A"),
        ("struct P{} enum E{A}", "P", "E::A"),
        ("enum E{A}", "Bit", "E::A"),
    ] {
        let error = failure(&format!(
            "{decl} fn unused(p:{ty})->Unit{{match p{{{label}=>()}}}} fn main()->Unit{{()}}"
        ));
        assert_eq!(error.code, "type", "{error:?}");
        assert!(
            error.message.contains("ordinary match requires"),
            "{error:?}"
        );
    }
}

#[test]
fn match_joins_complete_owner_frames_including_zero_width_owners() {
    for ty in ["Q<Bit>", "Q<Unit>"] {
        let source = format!(
            "enum E{{A,B}} observe fn f(p:E,q:{ty})->Unit{{match p{{E::A=>{{discard(q);()}},E::B=>()}}}}"
        );
        let error = failure(&source);
        assert_eq!(error.code, "ownership", "{error:?}");
        assert!(
            error.message.contains("match arms must consume"),
            "{error:?}"
        );
        prepare(&[(
            "main",
            &format!("enum E{{A,B}} fn f(p:E,q:{ty})->{ty}{{match p{{E::A=>q,E::B=>q}}}}"),
        )])
        .unwrap();
    }
}

#[test]
fn dormant_arms_retain_effects_and_call_dependencies() {
    for effect in ["unitary", "isometry"] {
        let source = format!(
            "enum E{{A,B}} pub {effect} fn f(q:Q<Bit>)->Q<Bit>{{match E::A{{E::A=>q,E::B=>{{let b=measure_z(q);basis unit(()) as _{{0}}}}}}}}"
        );
        let error = failure(&source);
        assert_eq!(error.code, "effect", "{error:?}");
    }
    for prefix in ["fn", "classical fn"] {
        let error = failure(&format!(
            "enum E{{A,B}} {prefix} f()->Bit{{match E::A{{E::A=>0,E::B=>f()}}}}"
        ));
        assert_eq!(error.code, "cycle", "{error:?}");
    }
}

#[test]
fn valid_source_match_does_not_bypass_the_nominal_execution_gate() {
    let parsed = crate::frontend::compile::ParsedProgram::parse(
        crate::edition::Edition::E2026,
        BTreeMap::from([(
            "main".into(),
            "enum E{A,B} pub fn main()->Bit{match E::A{E::A=>0,E::B=>1}}".into(),
        )]),
    )
    .unwrap();
    let error = parsed
        .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
        .unwrap_err();
    assert_eq!(error.code(), "unsupported");
    assert!(
        error.to_string().contains("typed native transport"),
        "{error}"
    );
}
