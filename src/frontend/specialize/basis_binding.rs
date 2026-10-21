//! Closed host descriptions use the common grammar and original type identity.
//! Resolution and preparation grant no native acceptance or runtime capability.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::{BasisBinding, Error, ParsedProgram, Result, SourceType, Span};
use crate::frontend::{
    ast, check,
    resolve::{ModuleId, Target, locals::ResolvedUse},
    types,
};
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Selection {
    expression: Arc<str>,
    sources: BTreeMap<String, Arc<str>>,
}

pub(super) fn parse(source: &str, program: Option<&ParsedProgram>) -> Result<BasisBinding> {
    let mut remaining = 100_000usize;
    parse_budgeted(source, program, &mut |span, cells| {
        remaining = remaining.checked_sub(cells).ok_or_else(|| {
            Error::new(
                "limit",
                span,
                "closed Basis preparation exceeds 100000 cells",
            )
        })?;
        Ok(())
    })
}

struct Context<'a, 'b> {
    program: Option<&'a ParsedProgram>,
    charge: &'b mut dyn FnMut(Span, usize) -> Result<()>,
    modules: BTreeSet<ModuleId>,
}

fn path_modules(
    program: &ParsedProgram,
    caller: ModuleId,
    name: &str,
    span: Span,
    modules: &mut BTreeSet<ModuleId>,
    charge: &mut dyn FnMut(Span, usize) -> Result<()>,
) -> Result<()> {
    charge(span, name.len() + 1)?;
    program
        .checked
        .resolution
        .visit_name_sources(caller, name, |owner| {
            charge(span, modules.len() + 1)?;
            modules.insert(owner);
            Ok(())
        })
}

/// Retain original type, alias and transitive Nat-helper source dependencies.
/// Only the complete immutable common judgment supplies these occurrences.
fn root_modules(
    program: &ParsedProgram,
    root: Target,
    span: Span,
    modules: &mut BTreeSet<ModuleId>,
    charge: &mut dyn FnMut(Span, usize) -> Result<()>,
) -> Result<()> {
    charge(span, 1)?;
    let mut pending = vec![root];
    let mut seen_types = BTreeSet::new();
    let mut seen_helpers = BTreeSet::new();
    while let Some(target) = pending.pop() {
        charge(span, 1)?;
        let (owner, uses) = match target {
            Target::Type(id) => {
                charge(span, seen_types.len() + 1)?;
                if !seen_types.insert(id) {
                    continue;
                }
                let record = program.checked.resolution.type_declaration(id);
                let uses = program.checked.nominal_uses.get(&id).ok_or_else(|| {
                    Error::new(
                        "source",
                        span,
                        "finite type lacks original dependency occurrences",
                    )
                })?;
                charge(span, uses.len())?;
                (
                    record.module,
                    uses.iter()
                        .map(|u| (u.name.as_str(), u.span, Some(u.target)))
                        .collect::<Vec<_>>(),
                )
            }
            Target::Declaration(id) => {
                charge(span, seen_helpers.len() + 1)?;
                if !seen_helpers.insert(id) {
                    continue;
                }
                let record = program.checked.resolution.declaration(id);
                if record.kind != ast::FnKind::Static {
                    return Err(Error::new(
                        "source",
                        span,
                        "field dependency is not an original Nat helper",
                    ));
                }
                let table = program.checked.lexical.get(&id).ok_or_else(|| {
                    Error::new(
                        "source",
                        span,
                        "Nat helper lacks its original lexical table",
                    )
                })?;
                charge(span, table.resolved_uses().len())?;
                (
                    record.module,
                    table
                        .resolved_uses()
                        .iter()
                        .map(|u| {
                            let target = match u.target {
                                ResolvedUse::Global(target) => Some(target),
                                _ => None,
                            };
                            (u.name.as_str(), u.span, target)
                        })
                        .collect::<Vec<_>>(),
                )
            }
            Target::Primitive(_) => continue,
        };
        charge(span, uses.len() + modules.len() + 1)?;
        modules.insert(owner);
        for (name, at, target) in uses {
            if let Some(target) = target {
                path_modules(program, owner, name, at, modules, charge)?;
                charge(at, 1)?;
                pending.push(target);
            }
        }
    }
    Ok(())
}

fn named_original<'a>(
    program: Option<&'a ParsedProgram>,
    name: &ast::Ident,
    charge: &mut dyn FnMut(Span, usize) -> Result<()>,
) -> Result<(&'a ParsedProgram, Target, &'a check::Ty)> {
    charge(name.span, name.text.len() + 1)?;
    let Some(program) = program else {
        return Err(Error::new(
            "type",
            name.span,
            format!(
                "closed Basis binding cannot contain named type {}",
                name.text
            ),
        ));
    };
    let resolution = &program.checked.resolution;
    let target = resolution.qualified_target(&name.text).map_err(|kind| {
        ParsedProgram::resolution_error(crate::frontend::resolve::Failure {
            module: String::new(),
            span: name.span,
            kind,
        })
    })?;
    let Target::Type(id) = target else {
        return Err(Error::new(
            "type",
            name.span,
            format!("{} is not an ordinary finite type", name.text),
        ));
    };
    if !resolution.target_visible(target, None) {
        return Err(Error::new(
            "visibility",
            name.span,
            format!("host Basis type {} is private", name.text),
        ));
    }
    let original = program
        .checked
        .nominals
        .get(&id)
        .ok_or_else(|| Error::new("source", name.span, "missing original finite type tree"))?;
    Ok((program, target, original))
}

impl types::SourceTypeContext for Context<'_, '_> {
    type Size = u32;
    type Error = Error;

    fn resolve_size(&mut self, n: &ast::Natural) -> Result<u32> {
        (self.charge)(n.span, 1)?;
        let bad = || {
            Error::new(
                "type",
                n.span,
                "closed Basis size must be a bounded nonnegative u32 expression",
            )
        };
        match &n.kind {
            ast::NatKind::Number(n) => u32::try_from(*n).map_err(|_| bad()),
            ast::NatKind::Name(_) | ast::NatKind::Call { .. } => Err(bad()),
            ast::NatKind::Add(a, b) => self
                .resolve_size(a)?
                .checked_add(self.resolve_size(b)?)
                .ok_or_else(bad),
            ast::NatKind::Sub(a, b) => self
                .resolve_size(a)?
                .checked_sub(self.resolve_size(b)?)
                .ok_or_else(bad),
            ast::NatKind::Mul(a, b) => self
                .resolve_size(a)?
                .checked_mul(self.resolve_size(b)?)
                .ok_or_else(bad),
        }
    }

    fn resolve_basis(&mut self, name: &ast::Ident) -> Result<SourceType> {
        let (program, target, original) = named_original(self.program, name, self.charge)?;
        let resolution = &program.checked.resolution;
        let owner = resolution
            .module(name.text.rsplit_once("::").expect("qualified target").0)
            .expect("resolved source module");
        path_modules(
            program,
            owner,
            &name.text,
            name.span,
            &mut self.modules,
            self.charge,
        )?;
        root_modules(program, target, name.span, &mut self.modules, self.charge)?;
        check::close_type_budgeted(
            original,
            &BTreeMap::new(),
            &BTreeMap::new(),
            name.span,
            |span, cells| (self.charge)(span, cells).map_err(check::SourceError::from),
        )
        .map_err(Error::from)
    }

    fn quantum_basis_error(&mut self, span: Span) -> Error {
        Error::new(
            "type",
            span,
            "closed Basis binding must be an ordinary type, not a Q owner",
        )
    }

    fn checked_node(&mut self, source: &ast::Type, _: types::Stage, ty: &SourceType) -> Result<()> {
        check::type_size_budgeted(ty, 4096, 64, true, source.span, &mut |span, cells| {
            (self.charge)(span, cells).map_err(check::SourceError::from)
        })
        .map_err(Error::from)?;
        if ty.basis_width().is_none_or(|n| n > 8) {
            return Err(Error::new(
                "limit",
                source.span,
                "closed Basis binding exceeds eight bits or type storage capacity",
            ));
        }
        Ok(())
    }
}

/// Reserve the complete expanded tree before any nominal body is copied.
fn preflight(
    source: &ast::Type,
    program: Option<&ParsedProgram>,
    charge: &mut dyn FnMut(Span, usize) -> Result<()>,
) -> Result<()> {
    charge(source.span, 1)?;
    let mut pending = vec![(source, 1usize)];
    let mut nodes = 0usize;
    while let Some((ty, depth)) = pending.pop() {
        charge(ty.span, 1)?;
        if depth > 64 {
            return Err(Error::new(
                "limit",
                ty.span,
                "closed Basis exceeds depth 64",
            ));
        }
        let added = match &ty.kind {
            ast::TypeKind::Named(name) => {
                let (_, _, original) = named_original(program, name, charge)?;
                let size = check::type_size_budgeted(
                    original,
                    4096,
                    64,
                    true,
                    name.span,
                    &mut |span, cells| charge(span, cells).map_err(check::SourceError::from),
                )
                .map_err(Error::from)?;
                if depth.saturating_add(size.depth).saturating_sub(1) > 64 {
                    return Err(Error::new(
                        "limit",
                        ty.span,
                        "expanded Basis exceeds depth 64",
                    ));
                }
                size.nodes
            }
            ast::TypeKind::Tuple(fields) => {
                charge(ty.span, fields.len())?;
                pending.extend(fields.iter().rev().map(|field| (field, depth + 1)));
                1
            }
            ast::TypeKind::Q(_) => {
                return Err(Error::new(
                    "type",
                    ty.span,
                    "closed Basis binding must be an ordinary type, not a Q owner",
                ));
            }
            _ => 1,
        };
        nodes = nodes.saturating_add(added);
        if nodes > 4096 {
            return Err(Error::new(
                "limit",
                ty.span,
                "expanded Basis exceeds 4096 cells",
            ));
        }
    }
    Ok(())
}

fn parse_budgeted(
    source: &str,
    program: Option<&ParsedProgram>,
    charge: &mut dyn FnMut(Span, usize) -> Result<()>,
) -> Result<BasisBinding> {
    charge(Span::default(), source.len() + 1)?;
    let syntax = crate::frontend::parser::parse_closed_basis(source)
        .map_err(|e| Error::new("type", e.span, e.message))?;
    preflight(&syntax, program, charge)?;
    let (ty, modules) = {
        let mut context = Context {
            program,
            charge,
            modules: BTreeSet::new(),
        };
        let ty = types::classify_source(&syntax, types::Stage::Basis, &mut context)?;
        (ty, context.modules)
    };
    let mut result = BasisBinding::checked(ty, syntax.span)?;
    if !modules.is_empty() {
        charge(syntax.span, source.len() + 1)?;
        let program = program.expect("resolved source type");
        let mut sources = BTreeMap::new();
        for module in modules {
            let name = program.checked.resolution.module_name(module);
            let original = program.sources.get(name).expect("retained original source");
            charge(syntax.span, name.len() + original.text().len() + 2)?;
            sources.insert(name.to_owned(), Arc::from(original.text()));
        }
        result.selection = Some(Arc::new(Selection {
            expression: Arc::from(source),
            sources,
        }));
    }
    Ok(result)
}

/// Re-resolve the original host selection before interface closure/cache reuse.
/// Same widths or a type copied from another preparation cannot replace it.
pub(super) fn validate(
    binding: &BasisBinding,
    program: &ParsedProgram,
    charge: &mut impl FnMut(Span, usize) -> Result<()>,
) -> Result<()> {
    let Some(selection) = &binding.selection else {
        return Ok(());
    };
    for (name, text) in &selection.sources {
        charge(Span::default(), name.len() + text.len() + 1)?;
        if program
            .sources
            .get(name)
            .is_none_or(|current| current.text() != text.as_ref())
        {
            return Err(Error::new(
                "source",
                Span::default(),
                "host Basis selection has changed original source dependencies",
            ));
        }
    }
    let current = parse_budgeted(&selection.expression, Some(program), charge)?;
    let same =
        binding
            .ty
            .equivalent_by_budgeted(&current.ty, &mut |a, b| Ok(a == b), &mut |cells| {
                charge(Span::default(), cells)
            })?;
    if !same {
        return Err(Error::new(
            "source",
            Span::default(),
            "host Basis selection differs from the receiving original type tree",
        ));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn program(leaf: &str, alias: &str, helper: &str) -> ParsedProgram {
        ParsedProgram::parse(
            crate::edition::Edition::E2026,
            BTreeMap::from([
                (
                    "main".into(),
                    "pub fn unused[const A:Basis]()->Unit{()}".into(),
                ),
                ("leaf".into(), leaf.into()),
                ("alias".into(), alias.into()),
                ("sizes".into(), helper.into()),
                ("private_alias".into(), "use leaf::Tri;".into()),
                ("other".into(), "pub enum Tri { A,B,C,D }".into()),
            ]),
        )
        .unwrap()
    }
    const LEAF: &str = "pub enum Tri { A,B,C } pub enum Four { A,B,C,D } enum Hidden { A } pub struct Empty {} pub struct Word { bits:Bits<sizes::width[2]()> } pub fn callable()->Unit{()}";
    const SIZES: &str = "pub static fn width[const n:Nat]()->Nat{n}";
    fn instantiate(p: &ParsedProgram, value: BasisBinding) -> Result<super::super::Instantiation> {
        p.instantiate_with_types(
            "main::unused",
            BTreeMap::from([("A".into(), value)]),
            BTreeMap::new(),
            BTreeMap::new(),
        )
    }

    #[test]
    fn public_host_roots_retain_original_trees_and_transitive_source_paths() {
        let p = program(LEAF, "pub use leaf::Tri; pub use leaf::Word;", SIZES);
        let alias = p.basis_binding("alias::Tri").unwrap();
        let direct = p.basis_binding("leaf::Tri").unwrap();
        assert_eq!(alias.ty, direct.ty);
        assert_eq!(alias.ty.basis_width(), Some(2));
        assert_ne!(alias.ty, p.basis_binding("leaf::Four").unwrap().ty);
        let named = p.basis_binding("(alias::Word,leaf::Empty)").unwrap();
        assert_eq!(named.ty.basis_width(), Some(2));
        assert_eq!(
            named
                .selection
                .as_ref()
                .unwrap()
                .sources
                .keys()
                .map(String::as_str)
                .collect::<Vec<_>>(),
            ["alias", "leaf", "sizes"]
        );
        let empty = p.basis_binding("leaf::Empty").unwrap();
        assert_eq!(empty.ty.basis_width(), Some(0));
        assert_ne!(empty.ty, BasisBinding::parse("Unit").unwrap().ty);
        assert_ne!(empty.ty, BasisBinding::parse("Bits<0>").unwrap().ty);
        let instance = instantiate(&p, named).unwrap();
        // This is real source preparation, with no invented body/effect facts.
        // Concrete execution still requires the actual typed native route.
        assert_eq!(instance.elaborate().unwrap_err().code(), "unsupported");
    }

    #[test]
    fn host_roots_have_no_module_privilege_or_wrong_category_fallback() {
        let p = program(LEAF, "pub use leaf::Tri;", SIZES);
        assert_eq!(
            p.basis_binding("leaf::Hidden").unwrap_err().code(),
            "visibility"
        );
        for text in [
            "private_alias::Tri",
            "leaf::Missing",
            "Tri",
            "leaf::callable",
            "sizes::width",
            "Q<alias::Tri>",
            "alias::Tri trailing",
        ] {
            assert!(p.basis_binding(text).is_err(), "{text}");
        }
        assert_eq!(BasisBinding::parse("leaf::Tri").unwrap_err().code(), "type");
    }

    #[test]
    fn receiving_preparation_rechecks_aliases_helpers_and_equal_width_changes() {
        let p = program(LEAF, "pub use leaf::Tri; pub use leaf::Word;", SIZES);
        let value = p.basis_binding("(alias::Tri,alias::Word)").unwrap();
        let identical = program(LEAF, "pub use leaf::Tri; pub use leaf::Word;", SIZES);
        instantiate(&identical, value.clone()).unwrap();
        for other in [
            program(LEAF, "pub use other::Tri; pub use leaf::Word;", SIZES),
            program(
                LEAF,
                "pub use leaf::Tri; pub use leaf::Word; // changed source",
                SIZES,
            ),
            program(
                LEAF,
                "pub use leaf::Tri; pub use leaf::Word;",
                "pub static fn width[const n:Nat]()->Nat{n+0}",
            ),
            program(
                &LEAF.replace("A,B,C }", "A,C,B }"),
                "pub use leaf::Tri; pub use leaf::Word;",
                SIZES,
            ),
        ] {
            assert_eq!(
                instantiate(&other, value.clone()).unwrap_err().code(),
                "source"
            );
        }
        // Reconstructing in the actual receiver is distinct from reusing stale
        // retained type data, even when the exact resulting width agrees.
        let changed = program(
            LEAF,
            "pub use leaf::Tri; pub use leaf::Word; // changed source",
            SIZES,
        );
        instantiate(
            &changed,
            changed.basis_binding("(alias::Tri,alias::Word)").unwrap(),
        )
        .unwrap();
    }

    #[test]
    fn common_body_checks_precede_execution_eligibility() {
        let source = "pub enum Tri { A,B,C } pub unitary fn bad(q:Q<Tri>)->Q<Tri>{(q,q)}";
        let e = ParsedProgram::parse(
            crate::edition::Edition::E2026,
            BTreeMap::from([("main".into(), source.into())]),
        )
        .unwrap_err();
        assert_ne!(e.code(), "unsupported");
        let p = ParsedProgram::parse(
            crate::edition::Edition::E2026,
            BTreeMap::from([(
                "main".into(),
                "pub enum Tri { A,B,C } pub unitary fn id(q:Q<Tri>)->Q<Tri>{q}".into(),
            )]),
        )
        .unwrap();
        assert_eq!(
            p.public_function_effect("main::id"),
            Some(crate::ir::Effect::Unitary)
        );
    }

    #[test]
    fn source_preparation_never_hides_observation_behind_nominal_types() {
        for effect in ["unitary", "isometry"] {
            let source = format!(
                "pub enum Tri {{ A,B,C }} pub {effect} fn hidden(q:Q<Tri>)->Unit{{discard(q)}}"
            );
            let e = ParsedProgram::parse(
                crate::edition::Edition::E2026,
                BTreeMap::from([("main".into(), source)]),
            )
            .unwrap_err();
            assert_eq!(e.code(), "effect");
        }
        let p = ParsedProgram::parse(
            crate::edition::Edition::E2026,
            BTreeMap::from([(
                "main".into(),
                "pub enum Tri { A,B,C } pub observe fn hidden(q:Q<Tri>)->Unit{discard(q)}".into(),
            )]),
        )
        .unwrap();
        assert_eq!(
            p.public_function_effect("main::hidden"),
            Some(crate::ir::Effect::Observe)
        );
    }

    #[test]
    fn a_same_width_tree_cannot_replace_a_retained_host_selection() {
        let p = program(LEAF, "pub use leaf::Tri;", SIZES);
        let mut value = p.basis_binding("alias::Tri").unwrap();
        value.ty = p.basis_binding("leaf::Four").unwrap().ty;
        assert_eq!(instantiate(&p, value).unwrap_err().code(), "source");
    }

    #[test]
    fn nominal_expansion_obeys_existing_storage_and_preallocation_bounds() {
        // Zero physical width isolates type-tree storage from quantum capacity.
        let fields = vec!["Unit"; 64].join(",");
        let leaf = format!("pub enum Tri {{ A }} pub struct Wide {{ field:({fields}) }}");
        let p = program(&leaf, "pub use leaf::Wide;", SIZES);
        let description = format!("({})", vec!["alias::Wide"; 63].join(","));
        assert_eq!(p.basis_binding(&description).unwrap_err().code(), "limit");
        let syntax = crate::frontend::parser::parse_closed_basis("alias::Wide").unwrap();
        let e = preflight(&syntax, Some(&p), &mut |span, _| {
            Err(Error::new("limit", span, "preallocation stopped"))
        })
        .unwrap_err();
        assert_eq!(e.message(), "preallocation stopped");
    }
}
