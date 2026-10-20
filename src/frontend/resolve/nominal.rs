//! Original nominal name/category validation; not finite-carrier elaboration.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;
use crate::frontend::ast::{Ident, RecordField, TypeDecl, TypeDeclKind};

pub(super) fn check_members<E: From<Failure>>(
    module: &str,
    declaration: &TypeDecl,
    charge: &mut impl FnMut(Span, usize) -> Result<(), E>,
) -> Result<(), E> {
    let (variants, fields): (&[Ident], &[RecordField]) = match &declaration.kind {
        TypeDeclKind::Enum { variants } => {
            if variants.is_empty() {
                charge(
                    declaration.span,
                    module.len() + declaration.name.text.len() + 1,
                )?;
                return Err(E::from(Failure {
                    module: module.into(),
                    span: declaration.name.span,
                    kind: FailureKind::EmptyEnum(declaration.name.text.clone()),
                }));
            }
            (variants, &[])
        }
        TypeDeclKind::Record { fields } => (&[], fields),
    };
    let mut names = BTreeSet::new();
    for name in variants
        .iter()
        .chain(fields.iter().map(|field| &field.name))
    {
        charge(name.span, name.text.len() + 1)?;
        if !names.insert(name.text.as_str()) {
            charge(
                name.span,
                module.len() + declaration.name.text.len() + name.text.len() + 2,
            )?;
            return Err(E::from(Failure {
                module: module.into(),
                span: name.span,
                kind: FailureKind::DuplicateMember {
                    owner: declaration.name.text.clone(),
                    member: name.text.clone(),
                },
            }));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::parser::parse_module;

    #[test]
    fn type_reexports_retain_original_category_visibility_index_and_source_chain() {
        let leaf =
            parse_module("pub enum Tri { A, B, C } struct Hidden {} pub fn f()->Unit{()}").unwrap();
        let alias = parse_module("pub use leaf::Tri;").unwrap();
        let client = parse_module("use alias::Tri; fn f()->Unit{()}").unwrap();
        let modules = [("leaf", &leaf), ("alias", &alias), ("client", &client)];
        let mut table = Resolution::new(modules).unwrap();
        let reverse = Resolution::new(modules.into_iter().rev()).unwrap();
        let target = table.qualified_target("leaf::Tri").unwrap();
        assert!(matches!(target, Target::Type(_)));
        assert_eq!(table.qualified_target("alias::Tri"), Ok(target));
        assert_eq!(reverse.qualified_target("alias::Tri"), Ok(target));
        assert_eq!(
            table.qualified("alias::Tri"),
            Err(FailureKind::NotFunction("alias::Tri".into()))
        );
        assert_ne!(
            target,
            Target::Declaration(table.qualified("leaf::f").unwrap())
        );
        let Target::Type(id) = target else {
            unreachable!()
        };
        assert_eq!(
            table.type_declaration(id).name,
            ("leaf".into(), "Tri".into())
        );
        assert_eq!(table.type_declaration(id).ast_index, 0);
        let caller = table.module("client").unwrap();
        let imports = table.imports(caller, &client).unwrap();
        table.set_scope(caller, imports);
        assert_eq!(table.lookup_visible(caller, "Tri"), Ok(Some(target)));
        let mut sources = Vec::new();
        table
            .visit_name_sources(caller, "Tri", |owner| {
                sources.push(table.module_name(owner));
                Ok::<_, ()>(())
            })
            .unwrap();
        assert_eq!(sources, ["alias", "leaf"]);
        let private = table.qualified_target("leaf::Hidden").unwrap();
        assert!(table.target_visible(private, table.module("leaf")));
        assert!(!table.target_visible(private, Some(caller)));
        let bad = parse_module("pub use leaf::Hidden;").unwrap();
        assert!(matches!(
            Resolution::new([("leaf", &leaf), ("bad", &bad)])
                .unwrap_err()
                .kind,
            FailureKind::Private(_)
        ));
    }

    #[test]
    fn empty_or_duplicate_members_and_cross_category_collisions_reject_at_original_names() {
        for (source, name, expected) in [
            (
                "enum Empty {}",
                "Empty",
                FailureKind::EmptyEnum("Empty".into()),
            ),
            (
                "enum E { A, A }",
                "A",
                FailureKind::DuplicateMember {
                    owner: "E".into(),
                    member: "A".into(),
                },
            ),
            (
                "struct R { a:Bit, a:Bits<0> }",
                "a",
                FailureKind::DuplicateMember {
                    owner: "R".into(),
                    member: "a".into(),
                },
            ),
            (
                "enum Clash { A } fn Clash()->Unit{()}",
                "Clash",
                FailureKind::Duplicate("Clash".into()),
            ),
            (
                "fn Clash()->Unit{()} enum Clash { A }",
                "Clash",
                FailureKind::Duplicate("Clash".into()),
            ),
        ] {
            let ast = parse_module(source).unwrap();
            let error = Resolution::new([("m", &ast)]).unwrap_err();
            assert_eq!(error.kind, expected);
            assert_eq!(&source[error.span.start..error.span.end], name);
            assert_eq!(error.span.start, source.rfind(name).unwrap());
        }
        let ast = parse_module("struct Empty {} enum Singleton { Only }").unwrap();
        assert!(Resolution::new([("m", &ast)]).is_ok());
    }

    #[test]
    fn imports_cannot_shadow_types_or_hide_private_types_behind_aliases() {
        let leaf = parse_module("pub enum T { A } struct Hidden {} pub fn f()->Unit{()}").unwrap();
        for text in [
            "enum T { B } use leaf::T;",
            "use leaf::T; use leaf::T;",
            "use leaf::Hidden;",
        ] {
            let client = parse_module(text).unwrap();
            let table = Resolution::new([("leaf", &leaf), ("client", &client)]).unwrap();
            assert!(
                table
                    .imports(table.module("client").unwrap(), &client)
                    .is_err(),
                "{text}"
            );
        }
        let bad = parse_module("pub use loop_b::T;").unwrap();
        let other = parse_module("pub use loop_a::T;").unwrap();
        assert!(matches!(
            Resolution::new([("loop_a", &bad), ("loop_b", &other)])
                .unwrap_err()
                .kind,
            FailureKind::ExportCycle(_)
        ));
    }
}
