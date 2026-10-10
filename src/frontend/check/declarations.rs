//! Complete ordered original declaration interfaces, without body projections.
use super::super::ast::{Requirement, StaticParamKind};
use super::super::formals::{AccessError, Formals};
use super::super::pattern;
use super::super::resolve::locals::ResolvedUse;
use super::super::resolve::{Failure, FailureKind, Target};
use super::super::types::Stage;
use super::*;

pub(super) fn resolution_error(f: Failure) -> SourceError {
    let code = match &f.kind {
        FailureKind::InvalidPath | FailureKind::MissingModule(_) => "module",
        FailureKind::Private(_) => "visibility",
        _ => "name",
    };
    let message = match f.kind {
        FailureKind::InvalidPath => "import needs a module and a name".into(),
        FailureKind::MissingModule(m) => format!("missing module `{m}`"),
        FailureKind::MissingName { module, name } => {
            format!("module `{module}` has no name `{name}`")
        }
        FailureKind::UnknownPrimitive { module, name } => {
            format!("sealed module `{module}` has no public name `{name}`")
        }
        FailureKind::Private(name) => format!("`{name}` is not public"),
        FailureKind::Collision(name) | FailureKind::DuplicateImport(name) => {
            format!("name `{name}` collides with another declaration or import")
        }
        FailureKind::Duplicate(name) => format!("duplicate declaration `{name}`"),
    };
    SourceError::new(code, f.span, message).in_module(&f.module)
}
impl From<Failure> for SourceError {
    fn from(f: Failure) -> Self {
        resolution_error(f)
    }
}

pub(super) fn prepare(p: &mut Program<'_>) -> Result<()> {
    for (name, module) in &p.modules {
        let owner = p.resolution.module(name).expect("registered source module");
        let imports = p
            .resolution
            .imports_budgeted(owner, module, |span, cells| p.budget.charge(span, cells))?;
        p.resolution
            .set_scope_budgeted(owner, imports, |span, cells| p.budget.charge(span, cells))?;
    }
    for (name, module) in &p.modules {
        let owner = p.resolution.module(name).expect("registered source module");
        for declaration in &module.decls {
            let id = p
                .resolution
                .local(owner, &declaration.name.text)
                .expect("registered source declaration");
            let index = Index::new_budgeted(
                id,
                declaration,
                |name| p.resolution.lookup(owner, name),
                |span, cells| p.budget.charge(span, cells),
            )
            .map_err(|e: SourceError| e.in_module(name))?;
            p.budget.charge(declaration.span, 1)?;
            p.indices.insert(id, index);
        }
    }
    static_helpers::prepare(p)?;
    for (name, module) in &p.modules {
        let owner = p.resolution.module(name).expect("registered source module");
        for declaration in &module.decls {
            let id = p
                .resolution
                .local(owner, &declaration.name.text)
                .expect("registered declaration");
            if declaration.kind == FnKind::Static {
                continue;
            }
            let interface = interface(p, id).map_err(|e| e.in_module(name))?;
            p.budget.charge(declaration.span, 1)?;
            p.interfaces.insert(id, interface);
        }
    }
    // Meaning references now consume real checked interfaces, including ones
    // declared later in source order. They grant no matrix/equality certificate.
    for (name, module) in &p.modules {
        let owner = p.resolution.module(name).expect("registered source module");
        for declaration in &module.decls {
            let id = p
                .resolution
                .local(owner, &declaration.name.text)
                .expect("registered source declaration");
            if declaration.kind == FnKind::Static {
                continue;
            }
            let interface = &p.interfaces[&id];
            for formal in &interface.statics {
                if let StaticKind::Operation {
                    basis,
                    codomain,
                    meaning: Some(meaning),
                    ..
                } = &formal.kind
                {
                    let target = &p.interfaces[meaning];
                    if target.kind != FnKind::Meaning {
                        return Err(SourceError::new(
                            "type",
                            declaration.span,
                            "expected a declared finite meaning",
                        )
                        .in_module(&interface.module));
                    }
                    if let Some(codomain) = codomain {
                        normalize::expect(
                            codomain,
                            &target.result,
                            &interface.premises,
                            declaration.span,
                            &p.budget,
                        )
                        .map_err(|e| e.in_module(&interface.module))?;
                    }
                    normalize::expect(
                        basis,
                        &target.result,
                        &interface.premises,
                        declaration.span,
                        &p.budget,
                    )
                    .map_err(|e| e.in_module(&interface.module))?;
                }
            }
        }
    }
    Ok(())
}

fn interface(p: &Program<'_>, id: DefId) -> Result<Interface> {
    let decl = p.decl(id);
    let index = &p.indices[&id];
    let budget = &p.budget;
    if !matches!(
        (decl.kind, &decl.body),
        (FnKind::Classical, ast::FnBody::Basis(_))
            | (
                FnKind::Meaning,
                ast::FnBody::Meaning { .. }
                    | ast::FnBody::MeaningCompose { .. }
                    | ast::FnBody::MeaningTensor { .. }
            )
            | (
                FnKind::Inferred | FnKind::Isometry | FnKind::Unitary | FnKind::Observe,
                ast::FnBody::Quantum(_)
            )
    ) {
        return Err(SourceError::new(
            "type",
            decl.span,
            "declaration kind does not match its original body",
        ));
    }
    let mut names = BTreeSet::new();
    let mut naturals = BTreeMap::new();
    for formal in &decl.static_params {
        budget.charge(formal.name.span, 2)?;
        pattern::claim(&mut names, &formal.name.text, || {
            SourceError::new("binding", formal.name.span, "duplicate static parameter")
        })?;
        if matches!(formal.kind, StaticParamKind::Natural) {
            let key = index.table.key(index.binder(&formal.name));
            naturals.insert(
                budget.key(formal.name.span, key)?,
                Linear::variable_budgeted(key, formal.name.span, &mut |span, cells| {
                    budget.preparation_charge(span, cells)
                })?,
            );
        }
    }
    let context =
        Context::natural_refs_budgeted(naturals.keys(), decl.span, &mut |span, cells| {
            budget.preparation_charge(span, cells)
        })?;
    let mut scope = Scope {
        helpers: Rc::clone(&p.helpers),
        naturals,
        bases: BTreeMap::new(),
        operations: BTreeMap::new(),
        context,
        values: BTreeMap::new(),
        moved: BTreeSet::new(),
        next_binding: Rc::new(Cell::new(0)),
    };
    for requirement in &decl.requires {
        budget.charge(decl.span, 1)?;
        if let Requirement::Predicate(predicate) = requirement {
            scope.context = normalize::predicate(predicate, index, &scope, true, budget)?;
        }
    }
    if !scope.context.feasible_budgeted(
        decl.span,
        "while checking declared natural premises",
        &mut |span, cells| budget.preparation_charge(span, cells),
    )? {
        return Err(SourceError::new(
            "size",
            decl.span,
            "inconsistent declared natural premises",
        ));
    }
    let mut formals = Formals::<Linear, DefId>::new();
    for (ordinal, formal) in decl.static_params.iter().enumerate() {
        let key = index.table.key(index.binder(&formal.name));
        budget.charge(formal.name.span, 1)?;
        formals.advance(
            ordinal,
            formal,
            budget.key(formal.name.span, key)?,
            |prefix| {
                let StaticParamKind::Operation {
                    basis,
                    codomain,
                    meaning,
                } = &formal.kind
                else {
                    unreachable!("Op callback");
                };
                let basis =
                    normalize::ty(basis, index, &scope, Stage::Basis, Some(prefix), budget)?;
                let codomain = codomain
                    .as_ref()
                    .map(|ty| normalize::ty(ty, index, &scope, Stage::Basis, Some(prefix), budget))
                    .transpose()?;
                let meaning = meaning
                    .as_ref()
                    .map(|name| meaning_identity(p, id, name))
                    .transpose()?;
                Ok::<_, SourceError>((basis, codomain, meaning))
            },
        )?;
        if matches!(formal.kind, StaticParamKind::Basis) {
            budget.charge(formal.name.span, key.name.len() * 2 + 3)?;
            scope.bases.insert(
                budget.key(formal.name.span, key)?,
                normalize::symbolic_basis(key, formal.name.span),
            );
        }
    }
    for requirement in &decl.requires {
        if let Requirement::Access(requirement) = requirement {
            let key = match index.table.usage(index.usage(&requirement.name)).target {
                ResolvedUse::Local(id) => Some(index.table.key(id)),
                ResolvedUse::Global(_) => None,
                ResolvedUse::Unresolved => {
                    return Err(SourceError::new(
                        "name",
                        requirement.name.span,
                        format!("unknown operation parameter `{}`", requirement.name.text),
                    ));
                }
            };
            formals
                .grant(key, requirement.access)
                .map_err(|e| match e {
                    AccessError::UnknownOperation => SourceError::new(
                        "access",
                        requirement.span,
                        "access requirement names no operation parameter",
                    ),
                    AccessError::Duplicate => SourceError::new(
                        "access",
                        requirement.span,
                        "duplicate operation access requirement",
                    ),
                })?;
        }
    }
    let mut checked = formals.into_operations(decl.static_params.len());
    let mut statics = Vec::new();
    for formal in &decl.static_params {
        let key = index.table.key(index.binder(&formal.name));
        budget.charge(formal.name.span, 2)?;
        let kind = match formal.kind {
            StaticParamKind::Natural => StaticKind::Natural,
            StaticParamKind::Basis => StaticKind::Basis,
            StaticParamKind::Operation { .. } => {
                let mut op = checked.remove(key).expect("complete checked Op formal");
                if let Some(codomain) = &op.codomain {
                    // The explicit endomorphism and its abbreviation have the
                    // same law/effect bound. Retain two ports unless the shared
                    // exact-tree judgment establishes their equality.
                    if normalize::equivalent(
                        codomain,
                        &op.basis,
                        &scope.context,
                        formal.name.span,
                        budget,
                    )? {
                        op.codomain = None;
                    }
                }
                if op.access[2] {
                    if let Some(codomain) = &op.codomain {
                        normalize::expect(
                            codomain,
                            &op.basis,
                            &scope.context,
                            formal.name.span,
                            budget,
                        )?;
                    }
                }
                budget.ty(formal.name.span, &op.basis)?;
                scope.operations.insert(
                    budget.key(formal.name.span, key)?,
                    Operation {
                        basis: budget.copy_ty(formal.name.span, &op.basis)?,
                        codomain: op
                            .codomain
                            .as_ref()
                            .map(|ty| budget.copy_ty(formal.name.span, ty))
                            .transpose()?,
                        effect: formal_effect(&op.codomain, &op.access),
                        meaning: op.meaning,
                        access: op.access,
                    },
                );
                StaticKind::Operation {
                    basis: op.basis,
                    codomain: op.codomain,
                    meaning: op.meaning,
                    access: op.access,
                }
            }
        };
        statics.push(StaticFormal {
            key: budget.key(formal.name.span, key)?,
            kind,
        });
    }
    let mut params = Vec::new();
    for parameter in &decl.params {
        budget.charge(parameter.span, 1)?;
        body::pattern_work(&parameter.pattern, budget)?;
        pattern::claim_pattern_names(&parameter.pattern, &mut names, |name| {
            SourceError::new("binding", name.span, "duplicate runtime parameter")
        })?;
        let ty = normalize::ty(
            &parameter.ty,
            index,
            &scope,
            if decl.kind == FnKind::Classical {
                Stage::Basis
            } else {
                Stage::Runtime
            },
            None,
            budget,
        )?;
        // Real pattern shape/linearity checks are shared with body binding.
        body::bind(
            &parameter.pattern,
            budget.copy_ty(parameter.span, &ty)?,
            index,
            &mut scope,
            budget,
        )?;
        params.push(ty);
    }
    let result = normalize::ty(
        &decl.return_type,
        index,
        &scope,
        if matches!(decl.kind, FnKind::Classical | FnKind::Meaning) {
            Stage::Basis
        } else {
            Stage::Runtime
        },
        None,
        budget,
    )?;
    let resolved = p.resolution.declaration(id);
    budget.charge(decl.span, resolved.name.0.len() + 1)?;
    Ok(Interface {
        module: resolved.name.0.clone(),
        ast_index: resolved.ast_index,
        kind: decl.kind,
        statics,
        params,
        result,
        premises: scope.context,
    })
}

pub(super) fn scope(
    interface: &Interface,
    helpers: &StaticHelpers,
    budget: &Budget,
    span: Span,
) -> Result<Scope> {
    let mut scope = Scope {
        helpers: Rc::clone(helpers),
        naturals: BTreeMap::new(),
        bases: BTreeMap::new(),
        operations: BTreeMap::new(),
        context: budget.copy_context(span, &interface.premises)?,
        values: BTreeMap::new(),
        moved: BTreeSet::new(),
        next_binding: Rc::new(Cell::new(0)),
    };
    for formal in &interface.statics {
        budget.charge(span, 2)?;
        match &formal.kind {
            StaticKind::Natural => {
                scope.naturals.insert(
                    budget.key(span, &formal.key)?,
                    Linear::variable_budgeted(&formal.key, span, &mut |span, cells| {
                        budget.preparation_charge(span, cells)
                    })?,
                );
            }
            StaticKind::Basis => {
                budget.charge(span, formal.key.name.len() * 2 + 3)?;
                scope.bases.insert(
                    budget.key(span, &formal.key)?,
                    normalize::symbolic_basis(&formal.key, span),
                );
            }
            StaticKind::Operation {
                basis,
                codomain,
                meaning,
                access,
            } => {
                scope.operations.insert(
                    budget.key(span, &formal.key)?,
                    Operation {
                        basis: budget.copy_ty(span, basis)?,
                        codomain: codomain
                            .as_ref()
                            .map(|ty| budget.copy_ty(span, ty))
                            .transpose()?,
                        effect: formal_effect(codomain, access),
                        meaning: *meaning,
                        access: *access,
                    },
                );
            }
        }
    }
    Ok(scope)
}
pub(super) fn meaning_identity(
    p: &Program<'_>,
    definition: DefId,
    name: &ast::Ident,
) -> Result<DefId> {
    let index = &p.indices[&definition];
    match index.table.usage(index.usage(name)).target {
        ResolvedUse::Global(Target::Declaration(id)) if p.decl(id).kind == FnKind::Meaning => {
            Ok(id)
        }
        _ => Err(SourceError::new(
            "type",
            name.span,
            "expected a declared finite meaning",
        )),
    }
}
