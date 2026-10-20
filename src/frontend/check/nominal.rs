//! Canonical ordinary finite type elaboration over original module sources.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::super::resolve::{ModuleId, Target};
use super::super::types::{
    SourceTypeContext, Stage,
    nominal::{Body, Field, Nominal, Origin},
};
use super::*;

/// Public Project ASTs are mutable. A nominal origin may only describe the
/// actual retained source, including helper and import declarations.
pub(super) fn validate_originals(
    modules: &BTreeMap<&str, &ast::Module>,
    sources: &BTreeMap<&str, &str>,
    budget: &Budget,
) -> Result<()> {
    let mut has_nominal = modules.values().any(|module| !module.type_decls.is_empty());
    // Inspect original tokens too: a mutable Project can delete all AST type
    // declarations. Comments and identifiers containing these strings are not
    // declarations. The byte search is only a negative lexer optimization.
    for (name, source) in sources {
        if has_nominal {
            break;
        }
        budget.charge(Span::default(), 1)?;
        if !source.contains("enum") && !source.contains("struct") {
            continue;
        }
        if source.len() > 65_536 {
            return Err(SourceError::new(
                "limit",
                Span::default(),
                "source exceeds 64 KiB per module",
            )
            .in_module(name));
        }
        budget.charge(Span::default(), source.len())?;
        has_nominal = super::super::lexer::lex(source).map_or(true, |tokens| {
            tokens.iter().any(|token| {
                matches!(
                    token.kind,
                    super::super::lexer::TokenKind::Enum | super::super::lexer::TokenKind::Struct
                )
            })
        });
    }
    // Non-nominal constructed-AST consumers retain their existing boundary;
    // they do not acquire a source-preservation claim from this check.
    if !has_nominal {
        return Ok(());
    }
    let mut bytes = 0usize;
    for (name, module) in modules {
        let source = sources.get(name).ok_or_else(|| {
            SourceError::new(
                "source",
                module.span,
                "finite type elaboration requires original module source bytes",
            )
            .in_module(name)
        })?;
        bytes = bytes
            .checked_add(source.len())
            .ok_or_else(|| SourceError::new("limit", module.span, "source byte count overflow"))?;
        if source.len() > 65_536 || bytes > 1_048_576 {
            return Err(SourceError::new(
                "limit",
                module.span,
                "source exceeds 64 KiB per module or 1 MiB aggregate",
            )
            .in_module(name));
        }
        budget.charge(module.span, source.len())?;
        let parsed = super::super::parser::parse_module(source).map_err(|e| {
            SourceError::new(
                "source",
                e.span,
                format!("original source cannot be parsed: {}", e.message),
            )
            .in_module(name)
        })?;
        if &parsed != *module {
            return Err(SourceError::new(
                "source",
                module.span,
                "source AST differs from its retained original bytes",
            )
            .in_module(name));
        }
    }
    Ok(())
}

fn target(resolution: &Resolution, module: ModuleId, name: &ast::Ident) -> Result<TypeId> {
    let selected = resolution
        .lookup_visible(module, &name.text)
        .map_err(|kind| {
            declarations::resolution_error(resolve::Failure {
                module: resolution.module_name(module).into(),
                span: name.span,
                kind,
            })
        })?;
    match selected {
        Some(Target::Type(id)) => Ok(id),
        _ => Err(SourceError::new(
            "type",
            name.span,
            format!("{} is not an available ordinary finite type", name.text),
        )),
    }
}

pub(super) fn prepare(p: &mut Program<'_>) -> Result<()> {
    let mut originals = BTreeMap::new();
    let mut edges = BTreeMap::new();
    for (name, module) in &p.modules {
        let owner = p.resolution.module(name).expect("registered module");
        for declaration in &module.type_decls {
            let Target::Type(id) = p
                .resolution
                .local_target(owner, &declaration.name.text)
                .expect("registered type")
            else {
                unreachable!("separate type registration")
            };
            p.budget.charge(declaration.span, 2)?;
            originals.insert(id, (owner, declaration));
            let mut dependencies = BTreeSet::new();
            if let ast::TypeDeclKind::Record { fields } = &declaration.kind {
                p.budget.charge(declaration.span, fields.len())?;
                let mut pending: Vec<_> = fields.iter().rev().map(|field| (&field.ty, 1)).collect();
                let mut cells = 0usize;
                while let Some((ty, depth)) = pending.pop() {
                    p.budget.charge(ty.span, 1)?;
                    cells += 1;
                    if cells > 4096 || depth > 64 {
                        return Err(SourceError::new(
                            "limit",
                            ty.span,
                            "record type exceeds 4096 cells or depth 64",
                        )
                        .in_module(name));
                    }
                    match &ty.kind {
                        ast::TypeKind::Named(name_ref) => {
                            let dependency = target(&p.resolution, owner, name_ref)
                                .map_err(|e| e.in_module(name))?;
                            p.budget.charge(ty.span, 1)?;
                            dependencies.insert(dependency);
                        }
                        ast::TypeKind::Tuple(fields) => {
                            p.budget.charge(ty.span, fields.len())?;
                            pending.extend(fields.iter().rev().map(|field| (field, depth + 1)));
                        }
                        ast::TypeKind::Q(_) => {
                            return Err(SourceError::new(
                                "type",
                                ty.span,
                                "an ordinary record field cannot contain quantum ownership",
                            )
                            .in_module(name));
                        }
                        _ => {}
                    }
                }
            }
            edges.insert(id, dependencies);
        }
    }
    let order = resolve::order_budgeted(edges, |s, c| p.budget.charge(s, c))?.map_err(|id| {
        let (owner, declaration) = originals[&id];
        SourceError::new(
            "cycle",
            declaration.name.span,
            "recursive finite type declarations are unsupported",
        )
        .in_module(p.resolution.module_name(owner))
    })?;
    let mut types = BTreeMap::new();
    let mut source_bytes: BTreeMap<ModuleId, Arc<str>> = BTreeMap::new();
    let scope = Scope {
        helpers: Rc::clone(&p.helpers),
        nominals: Rc::clone(&p.nominals),
        naturals: BTreeMap::new(),
        bases: BTreeMap::new(),
        operations: BTreeMap::new(),
        context: Context {
            alternatives: vec![vec![]],
        },
        values: BTreeMap::new(),
        moved: BTreeSet::new(),
        next_binding: Rc::new(Cell::new(0)),
    };
    for id in order {
        let (owner, declaration) = originals[&id];
        let module = p.resolution.module_name(owner);
        let result = (|| {
            let mut classifier = Classifier {
                resolution: &p.resolution,
                owner,
                types: &types,
                scope: &scope,
                budget: &p.budget,
            };
            let body = match &declaration.kind {
                ast::TypeDeclKind::Enum { variants } => {
                    p.budget.charge(
                        declaration.span,
                        variants.iter().map(|name| name.text.len() + 1).sum(),
                    )?;
                    Body::Enum(variants.iter().map(|name| name.text.clone()).collect())
                }
                ast::TypeDeclKind::Record { fields } => {
                    p.budget.charge(
                        declaration.span,
                        fields.iter().map(|field| field.name.text.len() + 2).sum(),
                    )?;
                    Body::Record(
                        fields
                            .iter()
                            .map(|field| {
                                Ok(Field {
                                    name: field.name.text.clone(),
                                    public: field.public,
                                    ty: super::super::types::classify_source(
                                        &field.ty,
                                        Stage::Basis,
                                        &mut classifier,
                                    )?,
                                })
                            })
                            .collect::<Result<_>>()?,
                    )
                }
            };
            if let std::collections::btree_map::Entry::Vacant(entry) = source_bytes.entry(owner) {
                let text = p.sources[module];
                p.budget.charge(declaration.span, text.len() + 1)?;
                entry.insert(Arc::from(text));
            }
            p.budget.charge(
                declaration.span,
                module.len() + declaration.name.text.len() + 2,
            )?;
            let ty = Ty::nominal(Nominal {
                origin: Arc::new(Origin {
                    module: module.into(),
                    name: declaration.name.text.clone(),
                    source: Arc::clone(&source_bytes[&owner]),
                    span: declaration.span,
                }),
                body,
            });
            p.budget.ty(declaration.span, &ty)?;
            Ok(ty)
        })()
        .map_err(|e: SourceError| e.in_module(module))?;
        types.insert(id, result);
    }
    p.nominals = Rc::new(types);
    Ok(())
}

struct Classifier<'a> {
    resolution: &'a Resolution,
    owner: ModuleId,
    types: &'a BTreeMap<TypeId, Ty>,
    scope: &'a Scope,
    budget: &'a Budget,
}
impl SourceTypeContext for Classifier<'_> {
    type Size = Linear;
    type Error = SourceError;
    fn resolve_size(&mut self, size: &ast::Natural) -> Result<Linear> {
        let n =
            normalize::module_natural(size, self.resolution, self.owner, self.scope, self.budget)?;
        if !n.terms.is_empty() || u32::try_from(n.constant).is_err() {
            return Err(SourceError::new(
                "size",
                size.span,
                "record field size must be a closed nonnegative u32",
            ));
        }
        Ok(n)
    }
    fn resolve_basis(&mut self, name: &ast::Ident) -> Result<Ty> {
        let id = target(self.resolution, self.owner, name)?;
        self.budget.copy_ty(name.span, &self.types[&id])
    }
    fn quantum_basis_error(&mut self, span: Span) -> SourceError {
        SourceError::new(
            "type",
            span,
            "an ordinary record field cannot contain quantum ownership",
        )
    }
    fn checked_node(&mut self, source: &ast::Type, _: Stage, ty: &Ty) -> Result<()> {
        self.budget.ty(source.span, ty).map(|_| ())
    }
}

#[cfg(test)]
mod tests;
