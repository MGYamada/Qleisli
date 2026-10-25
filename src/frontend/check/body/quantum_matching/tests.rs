//! Common judgments and explicit execution refusal, not coherent execution.
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

const KEEP: &str = "unitary fn keep(q:Q<Bit>)->Q<Bit>{q}";

fn failed(text: &str) -> SourceError {
    prepare(&[("main", text)]).unwrap_err()
}

#[test]
fn three_and_four_label_tables_reach_common_checking_and_retain_every_arm() {
    for (variants, arms, count) in [
        ("A,B,C", "E::C=>keep,E::A=>keep,E::B=>keep", 3),
        ("A,B,C,D", "E::D=>keep,E::B=>keep,E::A=>keep,E::C=>keep", 4),
    ] {
        let source = format!(
            "enum E{{{variants}}} {KEEP} pub unitary fn f(s:Q<E>,q:Q<Bit>)->(Q<E>,Q<Bit>){{qmatch(s,q){{{arms}}}}}"
        );
        let checked = prepare(&[("main", &source)]).unwrap();
        assert_eq!(checked.static_calls.len(), count);
        assert!(
            checked
                .static_calls
                .values()
                .all(|call| { call.source_effect == Some(Effect::Unitary) && call.access[2] })
        );
        assert_eq!(
            checked
                .obligations
                .iter()
                .filter(|o| matches!(o.kind, ObligationKind::Provider { .. }))
                .count(),
            count
        );
        assert_eq!(
            checked
                .obligations
                .iter()
                .filter(|o| matches!(o.kind, ObligationKind::TransformedMeaning))
                .count(),
            1
        );
    }
    prepare(&[("main", &format!(
        "{KEEP} unitary fn f(s:Q<Bits<2>>,q:Q<Bit>)->(Q<Bits<2>>,Q<Bit>){{qmatch(s,q){{3=>keep,0=>keep,2=>keep,1=>keep}}}}"
    ))]).unwrap();
}

#[test]
fn original_enum_identity_survives_aliases_and_rejects_alias_duplicates() {
    let leaf = "pub enum E{A,B,C}";
    let alias = "pub use leaf::E;";
    let source = format!(
        "{KEEP} unitary fn f(s:Q<leaf::E>,q:Q<Bit>)->(Q<leaf::E>,Q<Bit>){{qmatch(s,q){{alias::E::C=>keep,leaf::E::A=>keep,alias::E::B=>keep}}}}"
    );
    prepare(&[("leaf", leaf), ("alias", alias), ("main", &source)]).unwrap();
    for (arms, message) in [
        (
            "leaf::E::A=>keep,alias::E::A=>keep,leaf::E::B=>keep,leaf::E::C=>keep",
            "duplicate qmatch label A",
        ),
        ("leaf::E::A=>keep,leaf::E::B=>keep", "missing variant C"),
        (
            "leaf::E::A=>keep,leaf::E::B=>keep,leaf::E::D=>keep",
            "unknown variant D",
        ),
    ] {
        let source = format!(
            "{KEEP} fn f(s:Q<leaf::E>,q:Q<Bit>)->(Q<leaf::E>,Q<Bit>){{qmatch(s,q){{{arms}}}}}"
        );
        let error = prepare(&[("leaf", leaf), ("alias", alias), ("main", &source)]).unwrap_err();
        assert_eq!(error.code, "type", "{error:?}");
        assert!(error.message.contains(message), "{error:?}");
    }
    let wrong = source.replace("alias::E::B", "other::E::B");
    let error = prepare(&[
        ("leaf", leaf),
        ("alias", alias),
        ("other", leaf),
        ("main", &wrong),
    ])
    .unwrap_err();
    assert_eq!(error.code, "type", "{error:?}");
    let private = prepare(&[
        ("leaf", "enum E{A,B,C}"),
        ("alias", alias),
        ("main", &source),
    ])
    .unwrap_err();
    assert_eq!(private.code, "visibility", "{private:?}");
}

#[test]
fn ordinal_coverage_does_not_admit_padding_or_an_exponential_domain() {
    for (ty, arms, message) in [
        ("Bit", "0=>keep", "non-exhaustive"),
        (
            "Bit",
            "0=>keep,1=>keep,0=>keep",
            "duplicate qmatch ordinal 0",
        ),
        (
            "Bits<2>",
            "0=>keep,1=>keep,2=>keep,4294967295=>keep",
            "outside the selector",
        ),
        ("Bits<7>", "0=>keep", "fitting 64 arms"),
        ("E", "0=>keep,1=>keep,2=>keep", "exact enum variant labels"),
        ("Bit", "E::A=>keep,E::B=>keep", "exact ordinal labels"),
    ] {
        let error = failed(&format!(
            "enum E{{A,B,C}} {KEEP} fn f(s:Q<{ty}>,q:Q<Bit>)->(Q<{ty}>,Q<Bit>){{qmatch(s,q){{{arms}}}}}"
        ));
        assert_eq!(error.code, "type", "{error:?}");
        assert!(error.message.contains(message), "{error:?}");
    }
}

#[test]
fn exact_selector_and_target_trees_retain_zero_width_owners() {
    for (selector, label) in [("Unit", "0"), ("Bits<0>", "0"), ("One", "One::Only")] {
        for target in ["Unit", "Bits<0>", "One", "Empty", "(Bit,Unit)"] {
            prepare(&[("main", &format!(
                "enum One{{Only}} struct Empty{{}} unitary fn keep(q:Q<{target}>)->Q<{target}>{{q}} unitary fn f(s:Q<{selector}>,q:Q<{target}>)->(Q<{selector}>,Q<{target}>){{qmatch(s,q){{{label}=>keep}}}}"
            ))]).unwrap();
        }
        let error = failed(&format!(
            "enum One{{Only}} unitary fn keep(q:Q<{selector}>)->Q<{selector}>{{q}} fn f(s:Q<{selector}>)->(Q<{selector}>,Q<{selector}>){{qmatch(s,s){{{label}=>keep}}}}"
        ));
        assert_eq!(error.code, "ownership", "{error:?}");
    }
    for (target, provider) in [
        ("Bit", "Bits<1>"),
        ("Unit", "Bits<0>"),
        ("Unit", "One"),
        ("One", "Empty"),
        ("(Bit,Unit)", "(Unit,Bit)"),
        ("One", "Other"),
    ] {
        let error = failed(&format!(
            "enum One{{Only}} enum Other{{Only}} struct Empty{{}} unitary fn keep(q:Q<{provider}>)->Q<{provider}>{{q}} fn f(s:Q<Bit>,q:Q<{target}>)->(Q<Bit>,Q<{target}>){{qmatch(s,q){{0=>keep,1=>keep}}}}"
        ));
        assert_eq!(error.code, "type", "{error:?}");
    }
    for selector in ["Bit", "Unit", "One"] {
        let error = failed(&format!(
            "enum One{{Only}} {KEEP} fn f(s:{selector},q:Q<Bit>)->(Q<Bit>,Q<Bit>){{qmatch(s,q){{0=>keep,1=>keep}}}}"
        ));
        assert!(
            error.message.contains("selector requires one Q<A>"),
            "{error:?}"
        );
    }
    let reused_live = failed(&format!(
        "{KEEP} fn f(s:Q<Bit>)->(Q<Bit>,Q<Bit>){{qmatch(s,s){{0=>keep,1=>keep}}}}"
    ));
    assert_eq!(reused_live.code, "ownership", "{reused_live:?}");
    for (selector, result) in [("Bit", "Bits<1>"), ("Bits<0>", "Unit")] {
        let arms = if selector == "Bit" {
            "0=>keep,1=>keep"
        } else {
            "0=>keep"
        };
        let error = failed(&format!(
            "{KEEP} fn f(s:Q<{selector}>,q:Q<Bit>)->(Q<{result}>,Q<Bit>){{qmatch(s,q){{{arms}}}}}"
        ));
        assert_eq!(error.code, "type", "{error:?}");
    }
    let multiple_targets = failed(&format!(
        "{KEEP} fn f(s:Q<Bit>,a:Q<Bit>,b:Q<Bit>)->(Q<Bit>,Q<Bit>){{qmatch(s,(a,b)){{0=>keep,1=>keep}}}}"
    ));
    assert!(
        multiple_targets
            .message
            .contains("target requires one Q<B>"),
        "{multiple_targets:?}"
    );
}

#[test]
fn bit_table_uses_qif_access_and_transform_requirements_without_granting_control() {
    for construct in ["qif", "qmatch"] {
        let checked = prepare(&[("main", &format!(
            "{KEEP} unitary fn f[const U:Op<Bit>](s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>) requires Controllable(U){{{construct}(s,q){{0=>keep,1=>U}}}}"
        ))]).unwrap();
        assert_eq!(
            checked
                .obligations
                .iter()
                .filter(|o| matches!(o.kind, ObligationKind::TransformedMeaning))
                .count(),
            1
        );
        let error = failed(&format!(
            "{KEEP} unitary fn f[const U:Op<Bit>](s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>) requires Applicable(U){{{construct}(s,q){{0=>keep,1=>U}}}}"
        ));
        assert_eq!(error.code, "access", "{error:?}");
        let caller = format!(
            "{KEEP} unitary fn f(s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){{{construct}(s,q){{0=>keep,1=>leaf::broad}}}}"
        );
        let public_effect = prepare(&[
            ("leaf", "pub observe fn broad(q:Q<Bit>)->Q<Bit>{q}"),
            ("main", &caller),
        ])
        .unwrap_err();
        assert_eq!(public_effect.code, "effect", "{public_effect:?}");
    }
}

#[test]
fn named_phase_arms_retain_original_static_call_order_and_identity() {
    let source = "enum E{A,B,C}
        unitary fn keep(q:Q<Bit>)->Q<Bit>{q}
        unitary fn scalar(q:Q<Bit>)->Q<Bit>{global_phase_eighth(q)}
        unitary fn had(q:Q<Bit>)->Q<Bit>{h(q)}
        unitary fn f(s:Q<E>,q:Q<Bit>)->(Q<E>,Q<Bit>){qmatch(s,q){E::C=>scalar,E::A=>keep,E::B=>had}}";
    let checked = prepare(&[("main", source)]).unwrap();
    let arms = checked
        .static_calls
        .values()
        .map(|call| checked.resolution.declaration(call.target).name.1.as_str())
        .collect::<Vec<_>>();
    assert_eq!(arms, ["scalar", "keep", "had"]);
}

#[test]
fn later_arms_are_checked_after_a_generic_provider_and_public_effect_annotations() {
    for body in [
        "reset(q)",
        "let b=measure_z(q);fresh()",
        "discard(q);fresh()",
    ] {
        // Even a correct earlier unresolved operation formal cannot skip a
        // later concrete provider's complete inferred effect obligation.
        let error = failed(&format!(
            "enum E{{A,B,C}} isometry fn fresh()->Q<Bit>{{basis unit(()) as _{{0}}}} observe fn reset(q:Q<Bit>)->Q<Bit>{{discard(q);fresh()}} observe fn bad(q:Q<Bit>)->Q<Bit>{{{body}}} unitary fn f[const U:Op<Bit>](s:Q<E>,q:Q<Bit>)->(Q<E>,Q<Bit>) requires Controllable(U){{qmatch(s,q){{E::A=>U,E::B=>U,E::C=>bad}}}}"
        ));
        assert_eq!(error.code, "effect", "{error:?}");
    }
    let error = failed(&format!(
        "enum E{{A,B,C}} {KEEP} unitary fn f[const U:Op<Bit>,const V:Op<Bit>](s:Q<E>,q:Q<Bit>)->(Q<E>,Q<Bit>) requires Controllable(U),Applicable(V){{qmatch(s,q){{E::A=>U,E::B=>keep,E::C=>V}}}}"
    ));
    assert_eq!(error.code, "access", "{error:?}");
    let select = "unitary fn select[const U:Op<Bit>](s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>) requires Controllable(U){qmatch(s,q){0=>U,1=>U}}";
    prepare(&[("main", &format!(
        "{KEEP} {select} unitary fn outer[const V:Op<Bit>](s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>) requires Controllable(V){{select[then_op(V,keep)](s,q)}}"
    ))]).unwrap();
    let composite = failed(&format!(
        "{select} unitary fn wrong(q:Q<Bits<1>>)->Q<Bits<1>>{{q}} unitary fn outer[const V:Op<Bit>](s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>) requires Controllable(V){{select[then_op(V,wrong)](s,q)}}"
    ));
    assert_eq!(composite.code, "type", "{composite:?}");
}

#[test]
fn successful_common_checking_cannot_open_selected_native_transport() {
    for (decl, selector, labels) in [
        ("", "Bit", "0=>keep,1=>keep"),
        ("enum E{A,B,C}", "E", "E::A=>keep,E::B=>keep,E::C=>keep"),
    ] {
        let source = format!(
            "{decl} {KEEP} pub unitary fn f(s:Q<{selector}>,q:Q<Bit>)->(Q<{selector}>,Q<Bit>){{qmatch(s,q){{{labels}}}}}"
        );
        prepare(&[("main", &source)]).unwrap();
        let parsed = crate::frontend::compile::ParsedProgram::parse(
            crate::edition::Edition::E2026,
            BTreeMap::from([("main".into(), source)]),
        )
        .unwrap();
        let error = parsed
            .instantiate("main::f", BTreeMap::new(), BTreeMap::new())
            .unwrap_err();
        assert_eq!(error.code(), "unsupported");
        assert!(
            error.to_string().contains("typed native transport"),
            "{error}"
        );
    }
}
