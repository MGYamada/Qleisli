//! Compatibility of contextual static-natural names with shared type syntax.
// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::frontend::sized::ParsedProgram;
use std::collections::BTreeMap;

const TYPE_WORDS: [&str; 7] = ["Q", "Op", "Unit", "Bit", "CBit", "Bits", "CBits"];

fn prepare(source: &str, naturals: BTreeMap<String, u32>) {
    ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())]))
        .and_then(|program| program.instantiate("main::f", naturals, BTreeMap::new()))
        .and_then(|instance| instance.elaborate())
        .unwrap_or_else(|error| panic!("{source}\n{error}"));
}

#[test]
fn contextual_naturals_retain_name_span_type_dimensions_and_constraints() {
    for name in TYPE_WORDS {
        let source = format!(
            "pub unitary fn f[static {name}: Nat](q: Q<Bits<{name}>>) -> Q<Bits<{name}>> requires {name} >= 0 {{ if static {name} < 2 {{ q }} else {{ q }} }}"
        );
        let syntax = parse_module(&source).unwrap();
        let parameter = &syntax.decls[0].static_params[0];
        assert_eq!(parameter.kind, StaticParamKind::Natural);
        assert_eq!(parameter.name.text, name);
        assert_eq!(
            &source[parameter.name.span.start..parameter.name.span.end],
            name
        );
        let TypeKind::Q(basis) = &syntax.decls[0].params[0].ty.kind else {
            panic!("type constructor Q must retain its meaning");
        };
        let TypeKind::Bits(size) = &basis.kind else {
            panic!("Bits must retain its type constructor meaning");
        };
        assert_eq!(size.kind, NatKind::Name(name.into()));
        for value in [0, 1, 3] {
            prepare(&source, BTreeMap::from([(name.into(), value)]));
        }
    }
}

#[test]
fn contextual_naturals_keep_all_comparisons_separate_from_type_angles() {
    for name in TYPE_WORDS {
        for comparison in ["<", ">", "!=", "<=", ">=", "=="] {
            let source = format!(
                "pub unitary fn f[static {name}: Nat](q: Q<Bit>) -> Q<Bit> {{ if static {name} {comparison} 2 {{ q }} else {{ q }} }}"
            );
            prepare(&source, BTreeMap::from([(name.into(), 1)]));
        }
    }
}

#[test]
fn contextual_naturals_are_retained_in_fold_indices_and_bounds() {
    for name in TYPE_WORDS {
        let source = format!(
            "pub unitary fn f(q: Q<Bit>) -> Q<Bit> {{ for static {name} in 0..2 carry a = q {{ yield if static {name} < 1 {{ a }} else {{ a }} }} }}"
        );
        prepare(&source, BTreeMap::new());
        let bounded = format!(
            "pub unitary fn f[static {name}: Nat](q: Q<Bit>) -> Q<Bit> {{ for static i in 0..{name} carry a = q {{ yield a }} }}"
        );
        prepare(&bounded, BTreeMap::from([(name.into(), 2)]));
    }
}

#[test]
fn contextual_naturals_pass_through_specialization_and_operation_counts() {
    for name in TYPE_WORDS {
        let provider = "pub unitary fn identity[static n: Nat](q: Q<Bits<n>>) -> Q<Bits<n>> { q }";
        for argument in [name.to_owned(), format!("({name}+0)")] {
            let client = format!(
                "use dep::identity; pub unitary fn f[static {name}: Nat](q: Q<Bits<{name}>>) -> Q<Bits<{name}>> {{ identity[{argument}](q) }}"
            );
            ParsedProgram::parse(BTreeMap::from([
                ("dep".into(), provider.into()),
                ("main".into(), client.clone()),
            ]))
            .and_then(|p| {
                p.instantiate(
                    "main::f",
                    BTreeMap::from([(name.into(), 1)]),
                    BTreeMap::new(),
                )
            })
            .and_then(|p| p.elaborate())
            .unwrap_or_else(|error| panic!("{client}\n{error}"));
        }
        for count in [name.to_owned(), format!("2^{name}")] {
            let source = format!(
                "pub unitary fn f[static {name}: Nat, static U: Op<Bits<{name}>>](q: Q<Bits<{name}>>) -> Q<Bits<{name}>> requires Apply(U), Adjoint(U) {{ adjoint(repeat_op({count},U),q) }}"
            );
            ParsedProgram::parse(BTreeMap::from([("main".into(), source.clone())]))
                .unwrap_or_else(|error| panic!("{source}\n{error}"));
        }
    }
}

#[test]
fn contextual_natural_syntax_does_not_resolve_an_unbound_name() {
    for name in TYPE_WORDS {
        let source = format!(
            "pub unitary fn f(q: Q<Bit>) -> Q<Bit> {{ if static {name} < 2 {{ q }} else {{ q }} }}"
        );
        parse_module(&source).unwrap();
        let error = match ParsedProgram::parse(BTreeMap::from([("main".into(), source)])) {
            Err(error) => error,
            Ok(_) => panic!("the preparation profile must reject an unbound natural"),
        };
        assert_ne!(error.code(), "parse");
    }
}

#[test]
fn contextual_naturals_do_not_unreserve_runtime_global_or_operation_names() {
    for name in ["Q", "Op", "Unit", "Bit", "CBit"] {
        for source in [
            format!("pub unitary fn {name}(q: Q<Bit>) -> Q<Bit> {{ q }}"),
            format!("pub unitary fn f({name}: Q<Bit>) -> Q<Bit> {{ {name} }}"),
            format!("pub unitary fn f(q: Q<Bit>) -> Q<Bit> {{ let {name} = q; {name} }}"),
            format!("pub unitary fn f[static {name}: Op<Bit>](q: Q<Bit>) -> Q<Bit> {{ q }}"),
        ] {
            assert!(parse_module(&source).is_err(), "{source}");
        }
    }
    for keyword in ["if", "true", "Apply", "static"] {
        let source =
            format!("pub unitary fn f[static {keyword}: Nat](q: Q<Bit>) -> Q<Bit> {{ q }}");
        assert!(parse_module(&source).is_err(), "{source}");
    }
}
