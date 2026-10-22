//! Transparent public exports, outside semantic acceptance. Each alias has one
//! original target; iterative resolution retains its function/type category.
use super::*;
use crate::frontend::ast::Ident;

struct Export<'a> {
    module: String,
    name: &'a Ident,
    span: Span,
}
type Key = (ModuleId, String);

pub(super) fn prepare<'a, E: From<Failure>>(
    resolution: &mut Resolution,
    modules: &BTreeMap<&'a str, &'a Module>,
    charge: &mut impl FnMut(Span, usize) -> Result<(), E>,
) -> Result<(), E> {
    let mut pending = BTreeMap::<Key, Export<'a>>::new();
    for (&name, &ast) in modules {
        let owner = resolution.module(name).expect("registered original module");
        for usage in &ast.uses {
            charge(usage.span, 1)?;
            if !usage.public {
                continue;
            }
            let failure = |kind, span| {
                E::from(Failure {
                    module: name.into(),
                    span,
                    kind,
                })
            };
            if usage.path.len() < 2 {
                return Err(failure(FailureKind::InvalidPath, usage.span));
            }
            let last = usage.path.last().expect("nonempty public path");
            charge(
                last.span,
                last.text.len().saturating_add(name.len()).saturating_add(2),
            )?;
            if resolution.local_target(owner, &last.text).is_some() {
                return Err(failure(
                    FailureKind::Collision(last.text.clone()),
                    last.span,
                ));
            }
            if name == "std::prelude" && PrimitiveId::lookup_unbound(&last.text).is_some() {
                return Err(failure(
                    FailureKind::PreludePrimitive(last.text.clone()),
                    last.span,
                ));
            }
            let key = (owner, last.text.clone());
            if pending.contains_key(&key) {
                return Err(failure(
                    FailureKind::DuplicateImport(last.text.clone()),
                    last.span,
                ));
            }
            let mut length = 0usize;
            for segment in &usage.path[..usage.path.len() - 1] {
                charge(segment.span, 1)?;
                length = length.saturating_add(segment.text.len()).saturating_add(2);
            }
            charge(usage.span, length.saturating_add(1))?;
            let mut module = String::new();
            for segment in &usage.path[..usage.path.len() - 1] {
                if !module.is_empty() {
                    module.push_str("::");
                }
                module.push_str(&segment.text);
            }
            pending.insert(
                key,
                Export {
                    module,
                    name: last,
                    span: usage.span,
                },
            );
        }
    }
    for (root, original) in &pending {
        charge(original.span, root.1.len().saturating_add(1))?;
        let root_module = root.0;
        if resolution.modules[root_module.0]
            .exports
            .contains_key(&root.1)
        {
            continue;
        }
        let mut next = root.clone();
        let mut path = Vec::<Key>::new();
        let mut active = BTreeSet::<Key>::new();
        let target = loop {
            let export = &pending[&next];
            charge(
                export.span,
                next.1.len().saturating_mul(2).saturating_add(3),
            )?;
            active.insert(next.clone());
            path.push(next.clone());
            let failure = |kind, span| {
                E::from(Failure {
                    module: resolution.module_name(next.0).into(),
                    span,
                    kind,
                })
            };
            charge(
                export.name.span,
                export
                    .module
                    .len()
                    .saturating_add(export.name.text.len())
                    .saturating_add(2),
            )?;
            if super::super::primitive::retired_name_hint(&export.module, &export.name.text)
                .is_some()
            {
                return Err(failure(
                    FailureKind::UnknownPrimitive {
                        module: export.module.clone(),
                        name: export.name.text.clone(),
                    },
                    export.name.span,
                ));
            }
            let owner = resolution.module(&export.module).ok_or_else(|| {
                failure(
                    FailureKind::MissingModule(export.module.clone()),
                    export.span,
                )
            })?;
            if let Some(id) = resolution.member(owner, &export.name.text) {
                if !resolution.target_visible(id, None) {
                    return Err(failure(
                        FailureKind::Private(format!("{}::{}", export.module, export.name.text)),
                        export.name.span,
                    ));
                }
                break id;
            }
            let key = (owner, export.name.text.clone());
            if !pending.contains_key(&key) {
                return Err(failure(
                    FailureKind::MissingName {
                        module: export.module.clone(),
                        name: export.name.text.clone(),
                    },
                    export.name.span,
                ));
            }
            if active.contains(&key) {
                return Err(failure(
                    FailureKind::ExportCycle(format!("{}::{}", export.module, export.name.text)),
                    export.name.span,
                ));
            }
            next = key;
        };
        for key in path.into_iter().rev() {
            charge(original.span, key.1.len().saturating_add(2))?;
            let next = resolution
                .module(&pending[&key].module)
                .expect("resolved export successor");
            let owner = key.0;
            resolution.modules[owner.0]
                .exports
                .insert(key.1, ExportBinding { target, next });
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::parser::parse_module;

    #[test]
    fn reexports_keep_original_identity_and_every_resolution_source() {
        let leaf = parse_module("pub observe fn f(q:Q<Bit>)->Q<Bit>{q}").unwrap();
        let middle = parse_module("pub use leaf::f;").unwrap();
        let client = parse_module("pub use middle::f;").unwrap();
        let modules = [("client", &client), ("middle", &middle), ("leaf", &leaf)];
        let table = Resolution::new(modules).unwrap();
        let reverse = Resolution::new(modules.into_iter().rev()).unwrap();
        let original = table.qualified("leaf::f").unwrap();
        for path in ["client::f", "middle::f", "leaf::f"] {
            assert_eq!(table.qualified(path), Ok(original));
            assert_eq!(table.qualified(path), reverse.qualified(path));
        }
        assert_eq!(table.path(original), "leaf::f");
        assert_eq!(table.declaration(original).kind, FnKind::Observe);
        let mut names = Vec::new();
        table
            .visit_name_sources(table.module("client").unwrap(), "client::f", |module| {
                names.push(table.module_name(module));
                Ok::<_, ()>(())
            })
            .unwrap();
        assert_eq!(names, ["client", "middle", "leaf"]);
    }

    #[test]
    fn a_prelude_cannot_capture_an_existing_bare_primitive() {
        let leaf = parse_module("pub unitary fn h(q:Q<Bit>)->Q<Bit>{q}").unwrap();
        let prelude = parse_module("pub use leaf::h;").unwrap();
        let error = Resolution::new([("leaf", &leaf), ("std::prelude", &prelude)]).unwrap_err();
        assert_eq!(error.kind, FailureKind::PreludePrimitive("h".into()));
    }

    #[test]
    fn iterative_export_resolution_respects_the_callers_work_limit() {
        let modules: Vec<_> = (0..24)
            .map(|i| {
                let text = if i == 23 {
                    "pub unitary fn f(q:Q<Bit>)->Q<Bit>{q}".into()
                } else {
                    format!("pub use m{}::f;", i + 1)
                };
                (format!("m{i}"), parse_module(&text).unwrap())
            })
            .collect();
        #[derive(Debug)]
        enum Error {
            Resolution(Failure),
            Limit,
        }
        impl From<Failure> for Error {
            fn from(failure: Failure) -> Self {
                Self::Resolution(failure)
            }
        }
        for (limit, succeeds) in [(64usize, false), (16_384, true)] {
            let mut remaining = limit;
            let result = Resolution::new_budgeted(
                modules.iter().map(|(name, ast)| (name.as_str(), ast)),
                |_, cells| {
                    remaining = remaining.checked_sub(cells).ok_or(Error::Limit)?;
                    Ok::<_, Error>(())
                },
            );
            match result {
                Ok(table) => {
                    assert!(succeeds);
                    assert_eq!(table.qualified("m0::f"), table.qualified("m23::f"));
                }
                Err(Error::Limit) => assert!(!succeeds),
                Err(Error::Resolution(failure)) => {
                    panic!("unexpected resolution error: {failure:?}")
                }
            }
        }
    }
}
