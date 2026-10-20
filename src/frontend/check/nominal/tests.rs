// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;

fn inspect(sources: &[(&str, &str)], check: impl FnOnce(&Program<'_>)) {
    let syntax: Vec<_> = sources
        .iter()
        .map(|(_, text)| super::super::super::parser::parse_module(text).unwrap())
        .collect();
    let modules = sources
        .iter()
        .zip(&syntax)
        .map(|((name, _), syntax)| (*name, syntax))
        .collect();
    let program = prepare_program(
        modules,
        sources.iter().copied().collect(),
        SourceLimits::finite(),
    )
    .unwrap();
    check(&program);
}
fn ty<'a>(p: &'a Program<'_>, name: &str) -> &'a Ty {
    let Target::Type(id) = p.resolution.qualified_target(name).unwrap() else {
        panic!("nominal type")
    };
    &p.nominals[&id]
}
fn error(text: &str) -> SourceError {
    let syntax = super::super::super::parser::parse_module(text).unwrap();
    prepare_program(
        BTreeMap::from([("main", &syntax)]),
        BTreeMap::from([("main", text)]),
        SourceLimits::finite(),
    )
    .err()
    .expect("rejected source")
}

#[test]
fn forward_records_and_quantum_interfaces_keep_original_trees_and_visibility() {
    let text = "pub struct Packet { pub tag: Tri, zero: Unit, bit: Bit }
        pub enum Tri { A, B, C }
        fn classical_id(x:Packet)->Packet{x}
        unitary fn quantum_id(q:Q<Packet>)->Q<Packet>{q}";
    inspect(&[("main", text)], |p| {
        let packet = ty(p, "main::Packet");
        assert!(packet.is_basis());
        let Kind::Nominal(packet) = &packet.kind else {
            panic!("record")
        };
        assert_eq!(packet.origin.source.as_ref(), text);
        let Body::Record(fields) = &packet.body else {
            panic!("record fields")
        };
        assert_eq!(
            fields
                .iter()
                .map(|field| (field.name.as_str(), field.public))
                .collect::<Vec<_>>(),
            [("tag", true), ("zero", false), ("bit", false)]
        );
        assert_eq!(&fields[0].ty, ty(p, "main::Tri"));
        let id = p.resolution.qualified("main::quantum_id").unwrap();
        let interface = &p.interfaces[&id];
        assert_eq!(
            interface.params[0].quantum_basis(),
            Some(ty(p, "main::Packet"))
        );
        assert_eq!(interface.params[0], interface.result);
        assert!(interface.params[0].linear());
    });
}

#[test]
fn imported_alias_keeps_original_identity_and_rejects_private_fields_types() {
    let declarations = "pub enum Tri { A, B, C } enum Private { A }";
    inspect(
        &[
            ("leaf", declarations),
            ("alias", "pub use leaf::Tri;"),
            ("main", "use alias::Tri; struct Packet { tag:Tri }"),
        ],
        |p| {
            let Kind::Nominal(packet) = &ty(p, "main::Packet").kind else {
                panic!("record")
            };
            assert_eq!(packet.fields().next(), Some(ty(p, "leaf::Tri")));
        },
    );
    let leaf = super::super::super::parser::parse_module(declarations).unwrap();
    let text = "struct Leak { tag:leaf::Private }";
    let main = super::super::super::parser::parse_module(text).unwrap();
    let error = prepare_program(
        BTreeMap::from([("leaf", &leaf), ("main", &main)]),
        BTreeMap::from([("leaf", declarations), ("main", text)]),
        SourceLimits::finite(),
    )
    .err()
    .unwrap();
    assert_eq!(error.code, "visibility");
    assert_eq!(&text[error.span.start..error.span.end], "leaf::Private");
}

#[test]
fn nonfinite_unknown_recursive_and_wrong_category_fields_refuse() {
    for (text, code, location) in [
        ("struct Bad { q:Q<Bit> }", "type", "Q<Bit>"),
        ("struct Bad { x:(Bit,Q<Unit>) }", "type", "Q<Unit>"),
        ("struct Bad { x:Missing }", "type", "Missing"),
        ("fn f()->Unit{()} struct Bad { x:f }", "type", "f"),
        ("struct Bad { x:Bad }", "cycle", "Bad"),
        ("struct A { b:B } struct B { a:A }", "cycle", "A"),
        ("struct Bad { x:Bits<n> }", "static", "n"),
        ("struct Bad { x:Bits<4294967296> }", "size", "4294967296"),
    ] {
        let error = error(text);
        assert_eq!(error.code, code, "{text}: {}", error.message);
        assert_eq!(&text[error.span.start..error.span.end], location, "{text}");
    }
}

#[test]
fn field_sizes_use_existing_static_helpers_with_their_premises() {
    let prefix = "static fn previous[const n:Nat]()->Nat requires n>=1 {n-1}";
    inspect(
        &[(
            "main",
            &format!("{prefix} struct Word {{ bits:Bits<previous[3]()> }}"),
        )],
        |p| {
            let closed = close_type_budgeted(
                ty(p, "main::Word"),
                &BTreeMap::new(),
                &BTreeMap::new(),
                Span::default(),
                |_, _| Ok(()),
            )
            .unwrap();
            assert_eq!(closed.basis_width(), Some(2));
        },
    );
    assert_eq!(
        error(&format!(
            "{prefix} struct Word {{ bits:Bits<previous[0]()> }}"
        ))
        .code,
        "size"
    );
}

#[test]
fn same_width_names_order_source_and_zero_width_owners_remain_distinct() {
    let text = "enum Tri { A,B,C } enum Four { A,B,C,D } enum One { A } struct Empty {}";
    inspect(&[("main", text)], |p| {
        let close = |name| {
            close_type_budgeted(
                ty(p, name),
                &BTreeMap::new(),
                &BTreeMap::new(),
                Span::default(),
                |_, _| Ok(()),
            )
            .unwrap()
        };
        let three = close("main::Tri");
        let four = close("main::Four");
        assert_eq!(
            (three.basis_width(), four.basis_width()),
            (Some(2), Some(2))
        );
        assert_ne!(three, four);
        let one = close("main::One");
        let empty = close("main::Empty");
        for value in [one.clone(), empty.clone()] {
            assert_eq!(value.basis_width(), Some(0));
            assert_ne!(value, Type::unit());
            assert_ne!(value, Type::bits(0));
            assert!(Type::quantum(value).linear());
        }
        assert_ne!(one, empty);
    });
    let mut retained = None;
    inspect(&[("main", "enum Tri { A,B,C }")], |p| {
        retained = Some(ty(p, "main::Tri").clone())
    });
    for text in [
        "enum Tri { A,C,B }",
        "enum Tri { A,B,C } // different original bytes",
    ] {
        inspect(&[("main", text)], |p| {
            assert_ne!(retained.as_ref().unwrap(), ty(p, "main::Tri"))
        });
    }
}

#[test]
fn mutated_originals_cannot_supply_nominal_identity() {
    let text = "enum Tri { A,B,C }";
    let mut syntax = super::super::super::parser::parse_module(text).unwrap();
    let ast::TypeDeclKind::Enum { variants } = &mut syntax.type_decls[0].kind else {
        unreachable!()
    };
    variants.swap(0, 1);
    let error = prepare_program(
        BTreeMap::from([("main", &syntax)]),
        BTreeMap::from([("main", text)]),
        SourceLimits::finite(),
    )
    .err()
    .unwrap();
    assert_eq!(error.code, "source");
    let error = prepare_program(
        BTreeMap::from([("main", &syntax)]),
        BTreeMap::new(),
        SourceLimits::finite(),
    )
    .err()
    .unwrap();
    assert_eq!(error.code, "source");
}

#[test]
fn removing_ast_type_declarations_cannot_hide_original_source_declarations() {
    let text = "enum Tri { A,B,C }";
    let mut syntax = super::super::super::parser::parse_module(text).unwrap();
    syntax.type_decls.clear();
    let result = prepare_program(
        BTreeMap::from([("main", &syntax)]),
        BTreeMap::from([("main", text)]),
        SourceLimits::finite(),
    );
    assert!(
        matches!(result, Err(ref e) if e.code == "source"),
        "deleting AST declarations must not bypass original-source validation"
    );
}

#[test]
fn expanded_record_trees_and_ordered_basis_shadowing_keep_existing_limits() {
    let mut source = "struct R0 { value:Bit }".to_owned();
    for n in 1..65 {
        source.push_str(&format!(" struct R{n} {{ value:R{} }}", n - 1));
    }
    assert_eq!(error(&source).code, "limit");
    let mut source = "struct R0 { value:Bit }".to_owned();
    for n in 1..13 {
        source.push_str(&format!(" struct R{n} {{ a:R{}, b:R{} }}", n - 1, n - 1));
    }
    assert_eq!(error(&source).code, "limit");
    // A later lexical Basis binder cannot fall back to the global enum.
    let source = "enum A { X } fn f[const U:Op<A>,const A:Basis](q:Q<A>)->Q<A>{q}";
    let failure = error(source);
    assert_eq!(failure.code, "type");
    assert!(failure.message.contains("ordered kind"));
}

#[test]
fn a_matching_origin_cannot_hide_changed_field_trees_or_visibility() {
    inspect(&[("main", "struct Pair { pub a:Bit, b:Unit }")], |p| {
        let original = ty(p, "main::Pair");
        let Kind::Nominal(nominal) = &original.kind else {
            unreachable!()
        };
        for mutation in 0..3 {
            let mut forged = nominal.as_ref().clone();
            let Body::Record(fields) = &mut forged.body else {
                unreachable!()
            };
            match mutation {
                0 => fields.swap(0, 1),
                1 => fields[0].public = false,
                _ => fields[0].ty = Ty::bits(Linear::constant(1)),
            }
            assert_eq!(forged.origin, nominal.origin);
            assert_ne!(&Ty::nominal(forged), original);
        }
        let mut naturals = Vec::new();
        let mapped = original
            .map_parts(
                &mut |n| {
                    naturals.push(n.constant);
                    Ok::<_, ()>(n.constant as u32)
                },
                &mut |_| panic!("closed record contains no opaque Basis parameter"),
            )
            .unwrap();
        assert!(naturals.is_empty());
        assert_eq!(mapped.basis_width(), Some(1));
        assert_ne!(mapped, Type::bits(1));
    });
}
