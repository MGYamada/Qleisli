//! Provisional first-order Nat helpers, checked on the complete original AST.
//! These untrusted affine templates grant no runtime or native authority.
// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
use super::super::ast::{FnBody, NatKind, Requirement, StaticParamKind, TypeKind};
use super::super::resolve::Target;
use super::super::resolve::locals::ResolvedUse;
use super::*;

pub(super) fn target(index: &Index<'_>, name: &ast::Ident) -> Result<DefId> {
    match index.table.usage(index.usage(name)).target {
        ResolvedUse::Global(Target::Declaration(id)) => Ok(id),
        _ => Err(SourceError::new(
            "static",
            name.span,
            "a Nat helper call requires a declared static function",
        )),
    }
}

pub(super) fn prepare(p: &mut Program<'_>) -> Result<()> {
    let mut edges = BTreeMap::new();
    for (id, _) in p.resolution.declarations() {
        let declaration = p.decl(id);
        if declaration.kind != FnKind::Static {
            continue;
        }
        let FnBody::Natural(body) = &declaration.body else {
            return Err(SourceError::new(
                "static",
                declaration.span,
                "a static helper requires an original Nat expression body",
            )
            .in_module(p.module(id)));
        };
        if !declaration.params.is_empty()
            || !matches!(&declaration.return_type.kind, TypeKind::Named(name) if name.text == "Nat")
            || declaration
                .static_params
                .iter()
                .any(|formal| !matches!(formal.kind, StaticParamKind::Natural))
            || declaration
                .requires
                .iter()
                .any(|r| !matches!(r, Requirement::Predicate(_)))
        {
            return Err(SourceError::new("static", declaration.span, "a bounded Nat helper has only static Nat parameters, no runtime parameters, a Nat result and natural premises").in_module(p.module(id)));
        }
        p.budget
            .charge(declaration.span, 1 + declaration.requires.len())?;
        let mut pending = vec![body];
        for requirement in &declaration.requires {
            if let Requirement::Predicate(predicate) = requirement {
                pending.extend([&predicate.left, &predicate.right]);
            }
        }
        let mut dependencies = BTreeSet::new();
        while let Some(natural) = pending.pop() {
            p.budget.charge(natural.span, 1)?;
            match &natural.kind {
                NatKind::Call { callee, arguments } => {
                    let dependency =
                        target(&p.indices[&id], callee).map_err(|e| e.in_module(p.module(id)))?;
                    if p.decl(dependency).kind != FnKind::Static {
                        return Err(SourceError::new("static", callee.span, "natural expressions cannot call a runtime function, operation or Meaning").in_module(p.module(id)));
                    }
                    p.budget.charge(natural.span, 1 + arguments.len())?;
                    dependencies.insert(dependency);
                    pending.extend(arguments.iter().rev());
                }
                NatKind::Add(a, b) | NatKind::Sub(a, b) | NatKind::Mul(a, b) => {
                    p.budget.charge(natural.span, 2)?;
                    pending.extend([a.as_ref(), b.as_ref()]);
                }
                NatKind::Name(_) | NatKind::Number(_) => {}
            }
        }
        edges.insert(id, dependencies);
    }
    let order = resolve::order_budgeted(edges, |span, cells| p.budget.charge(span, cells))?
        .map_err(|id| {
            SourceError::new(
                "cycle",
                p.decl(id).span,
                "static Nat helper dependency cycles are forbidden",
            )
            .in_module(p.module(id))
        })?;
    for id in order {
        let helper = check(p, id).map_err(|e| e.in_module(p.module(id)))?;
        p.budget.charge(p.decl(id).span, 2)?;
        Rc::get_mut(&mut p.helpers)
            .expect("no retained checking scope")
            .insert(id, Arc::new(helper));
    }
    Ok(())
}

fn check(p: &Program<'_>, id: DefId) -> Result<StaticHelper> {
    let declaration = p.decl(id);
    let index = &p.indices[&id];
    let budget = &p.budget;
    let mut names = BTreeSet::new();
    let mut naturals = BTreeMap::new();
    let mut parameters = Vec::new();
    for parameter in &declaration.static_params {
        budget.charge(parameter.name.span, 1 + parameter.name.text.len())?;
        if !names.insert(parameter.name.text.as_str()) {
            return Err(SourceError::new(
                "binding",
                parameter.name.span,
                "duplicate static helper parameter",
            ));
        }
        let key = index.table.key(index.binder(&parameter.name));
        parameters.push(budget.key(parameter.name.span, key)?);
        naturals.insert(
            budget.key(parameter.name.span, key)?,
            Linear::variable_budgeted(key, parameter.name.span, &mut |s, c| {
                budget.sized_charge(s, c)
            })?,
        );
    }
    let context =
        Context::natural_refs_budgeted(naturals.keys(), declaration.span, &mut |s, c| {
            budget.sized_charge(s, c)
        })?;
    let mut scope = Scope {
        helpers: Rc::clone(&p.helpers),
        naturals,
        context,
        bases: BTreeMap::new(),
        operations: BTreeMap::new(),
        values: BTreeMap::new(),
        moved: BTreeSet::new(),
        next_binding: Rc::new(Cell::new(0)),
    };
    let mut requirements = Vec::new();
    for requirement in &declaration.requires {
        let Requirement::Predicate(predicate) = requirement else {
            unreachable!("checked helper shape")
        };
        let left = normalize::natural(&predicate.left, index, &scope, None, budget)?;
        let right = normalize::natural(&predicate.right, index, &scope, None, budget)?;
        budget.charge(declaration.span, 1)?;
        scope.context = normalize::predicate(predicate, index, &scope, true, budget)?;
        requirements.push((left, predicate.comparison, right));
    }
    if !scope.context.feasible_budgeted(
        declaration.span,
        "while checking static helper premises",
        &mut |s, c| budget.sized_charge(s, c),
    )? {
        return Err(SourceError::new(
            "size",
            declaration.span,
            "inconsistent static helper premises",
        ));
    }
    let FnBody::Natural(body) = &declaration.body else {
        unreachable!("checked helper shape")
    };
    let result = normalize::natural(body, index, &scope, None, budget)?;
    Ok(StaticHelper {
        parameters,
        result,
        requirements,
    })
}
