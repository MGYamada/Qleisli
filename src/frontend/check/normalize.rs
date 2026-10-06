//! Normalization borrows original occurrences; no projected syntax is built.
use super::super::ast::{NatKind, Natural, Predicate, TypeKind};
use super::super::formals::Prefix;
use super::super::resolve::locals::ResolvedUse;
use super::super::types::{SourceTypeContext, Stage, TypeParameter};
use super::*;

pub(super) fn located(error: super::super::sized::Error, span: Span) -> SourceError {
    let mut error = SourceError::from(error);
    if error.span == Span::default() {
        error.span = span;
    }
    error
}
fn arithmetic_context(error: super::super::sized::Error, span: Span, context: &str) -> SourceError {
    let needs_context = error.span() == Span::default();
    let mut error = located(error, span);
    if needs_context {
        error.message = format!("{context}: {}", error.message);
    }
    error
}

fn local<'a>(index: &'a Index<'_>, name: &ast::Ident) -> Option<&'a BinderKey> {
    match index.table.usage(index.usage(name)).target {
        ResolvedUse::Local(id) => Some(index.table.key(id)),
        _ => None,
    }
}
pub(super) fn natural(
    n: &Natural,
    index: &Index<'_>,
    scope: &Scope,
    prefix: Option<&BTreeSet<BinderKey>>,
    budget: &Budget,
) -> Result<Linear> {
    natural_inner(n, index, scope, prefix, budget, 1)
}
fn natural_inner(
    n: &Natural,
    index: &Index<'_>,
    scope: &Scope,
    prefix: Option<&BTreeSet<BinderKey>>,
    budget: &Budget,
    depth: usize,
) -> Result<Linear> {
    budget.charge(n.span, 1)?;
    if depth > 128 {
        return Err(SourceError::new(
            "limit",
            n.span,
            "natural expression exceeds depth 128",
        ));
    }
    let mut charge = |span, cells| budget.sized_charge(span, cells);
    let result = match &n.kind {
        NatKind::Number(value) => {
            if *value < 0 {
                return Err(SourceError::new(
                    "size",
                    n.span,
                    "natural literal must be nonnegative",
                ));
            }
            Linear::constant_budgeted(*value, n.span, &mut charge)?
        }
        NatKind::Name(name) => {
            let key = match index.table.usage(index.natural_usage(n)).target {
                ResolvedUse::Local(id) => index.table.key(id),
                _ => {
                    return Err(SourceError::new(
                        "static",
                        n.span,
                        format!("unknown natural name {name}"),
                    ));
                }
            };
            let x = prefix
                .filter(|p| !p.contains(key))
                .map_or_else(|| scope.naturals.get(key), |_| None)
                .ok_or_else(|| {
                    SourceError::new("static", n.span, format!("unknown natural name {name}"))
                })?;
            x.copy_budgeted(n.span, &mut charge)?
        }
        NatKind::Add(a, b) | NatKind::Sub(a, b) | NatKind::Mul(a, b) => {
            let a = natural_inner(a, index, scope, prefix, budget, depth + 1)?;
            let b = natural_inner(b, index, scope, prefix, budget, depth + 1)?;
            match &n.kind {
                NatKind::Add(..) => a.add_budgeted(&b, n.span, &mut charge).map_err(|error| {
                    arithmetic_context(error, n.span, "normalizing size expression")
                })?,
                NatKind::Sub(..) => {
                    if !scope.context.proves_le_budgeted(
                        &b,
                        &a,
                        n.span,
                        "while proving subtraction nonnegative",
                        &mut charge,
                    )? {
                        return Err(SourceError::new(
                            "size",
                            n.span,
                            "subtraction lacks a nonnegative guard",
                        ));
                    }
                    a.sub_budgeted(&b, n.span, &mut charge).map_err(|error| {
                        arithmetic_context(error, n.span, "normalizing size expression")
                    })?
                }
                _ => {
                    if a.terms.is_empty() {
                        b.scale_budgeted(a.constant, n.span, &mut charge)
                            .map_err(|error| {
                                arithmetic_context(error, n.span, "normalizing size expression")
                            })?
                    } else if b.terms.is_empty() {
                        a.scale_budgeted(b.constant, n.span, &mut charge)
                            .map_err(|error| {
                                arithmetic_context(error, n.span, "normalizing size expression")
                            })?
                    } else {
                        return Err(SourceError::new(
                            "unsupported",
                            n.span,
                            "multiplication of two symbolic sizes is nonlinear",
                        ));
                    }
                }
            }
        }
    };
    Ok(result)
}
pub(super) fn predicate(
    p: &Predicate,
    index: &Index<'_>,
    scope: &Scope,
    truth: bool,
    budget: &Budget,
) -> Result<Context> {
    let a = natural(&p.left, index, scope, None, budget)?;
    let b = natural(&p.right, index, scope, None, budget)?;
    let span = p.left.span.cover(p.right.span);
    Ok(scope
        .context
        .compare_budgeted(a, p.comparison, b, truth, span, &mut |span, cells| {
            budget.sized_charge(span, cells)
        })?)
}

pub(super) fn ty(
    source: &ast::Type,
    index: &Index<'_>,
    scope: &Scope,
    stage: Stage,
    prefix: Option<Prefix<'_>>,
    budget: &Budget,
) -> Result<Ty> {
    // All Basis occurrences are checked before any Natural normalization.
    budget.charge(source.span, 1)?;
    let mut pending = vec![(source, 1usize)];
    let mut cells = 0usize;
    while let Some((node, depth)) = pending.pop() {
        budget.charge(node.span, 1)?;
        if !matches!(node.kind, TypeKind::Q(_)) {
            cells += 1;
        }
        if cells > 4096 || depth > 64 {
            return Err(SourceError::new(
                "limit",
                node.span,
                "source type exceeds 4096 cells or depth 64",
            ));
        }
        match &node.kind {
            TypeKind::Named(name) => {
                let key = local(index, name).ok_or_else(|| {
                    SourceError::new(
                        "type",
                        name.span,
                        format!(
                            "Basis parameter {} is unavailable in this ordered kind",
                            name.text
                        ),
                    )
                })?;
                if prefix.is_some_and(|p| !p.bases.contains(key)) || !scope.bases.contains_key(key)
                {
                    return Err(SourceError::new(
                        "type",
                        name.span,
                        format!(
                            "Basis parameter {} is unavailable in this ordered kind",
                            name.text
                        ),
                    ));
                }
            }
            TypeKind::Q(child) => {
                budget.charge(node.span, 1)?;
                pending.push((child, depth));
            }
            TypeKind::Tuple(fields) => {
                if fields.len() > 64 {
                    return Err(SourceError::new(
                        "limit",
                        node.span,
                        "source tuple exceeds 64 fields",
                    ));
                }
                budget.charge(node.span, fields.len())?;
                pending.extend(fields.iter().rev().map(|t| (t, depth + 1)));
            }
            _ => {}
        }
    }
    struct Classifier<'a, 'ast> {
        index: &'a Index<'ast>,
        scope: &'a Scope,
        prefix: Option<Prefix<'a>>,
        budget: &'a Budget,
    }
    impl SourceTypeContext for Classifier<'_, '_> {
        type Size = Linear;
        type Error = SourceError;
        fn resolve_size(&mut self, n: &Natural) -> Result<Linear> {
            natural(
                n,
                self.index,
                self.scope,
                self.prefix.map(|p| p.naturals),
                self.budget,
            )
        }
        fn resolve_basis(&mut self, name: &ast::Ident) -> Result<Ty> {
            let key = local(self.index, name).expect("prechecked Basis occurrence");
            self.budget.copy_ty(name.span, &self.scope.bases[key])
        }
        fn quantum_basis_error(&mut self, span: Span) -> SourceError {
            SourceError::new("type", span, "a Basis type cannot contain a quantum owner")
        }
        fn checked_node(&mut self, source: &ast::Type, _stage: Stage, result: &Ty) -> Result<()> {
            self.budget.ty(source.span, result).map(|_| ())
        }
    }
    budget.charge(source.span, cells)?;
    super::super::types::classify_source(
        source,
        stage,
        &mut Classifier {
            index,
            scope,
            prefix,
            budget,
        },
    )
}

pub(super) fn substitute(
    ty: &Ty,
    naturals: &BTreeMap<BinderKey, Linear>,
    bases: &BTreeMap<BinderKey, Ty>,
    span: Span,
    budget: &Budget,
) -> Result<Ty> {
    budget.ty(span, ty)?;
    budget.charge(span, 1)?;
    let mut pending = vec![(ty, 1usize)];
    let mut cells = 0usize;
    while let Some((node, depth)) = pending.pop() {
        budget.charge(span, 1)?;
        if depth > 64 {
            return Err(SourceError::new(
                "limit",
                span,
                "substituted type exceeds depth 64",
            ));
        }
        let count = match &node.kind {
            Kind::Parameter(p) => {
                let replacement =
                    p.key
                        .as_ref()
                        .and_then(|key| bases.get(key))
                        .ok_or_else(|| {
                            SourceError::new(
                                "type",
                                span,
                                format!("unbound Basis parameter {}", p.name),
                            )
                        })?;
                let size = type_size_budgeted(
                    replacement,
                    4096,
                    65 - depth,
                    true,
                    span,
                    &mut |span, cells| budget.charge(span, cells),
                )?;
                budget.charge(span, size.nodes)?;
                size.nodes
            }
            Kind::Q(child) => {
                budget.charge(span, 1)?;
                pending.push((child, depth));
                0
            }
            Kind::Tuple(fields) => {
                budget.charge(span, fields.len())?;
                pending.extend(fields.iter().rev().map(|field| (field, depth + 1)));
                1
            }
            _ => 1,
        };
        cells = cells.checked_add(count).ok_or_else(|| {
            SourceError::new("limit", span, "substituted type cell count overflow")
        })?;
        if cells > 4096 {
            return Err(SourceError::new(
                "limit",
                span,
                "substituted type exceeds 4096 expanded cells",
            ));
        }
    }
    budget.charge(span, cells)?;
    let result = ty.map_parts(
        &mut |n| {
            let mut charge = |span, cells| budget.sized_charge(span, cells);
            n.substitute_budgeted(naturals, span, &mut charge)
                .map_err(|error| arithmetic_context(error, span, "substituted callee obligation"))
        },
        &mut |p| {
            let replacement = p
                .key
                .as_ref()
                .and_then(|key| bases.get(key))
                .ok_or_else(|| {
                    SourceError::new("type", span, format!("unbound Basis parameter {}", p.name))
                })?;
            budget.copy_ty(span, replacement)
        },
    )?;
    budget.ty(span, &result)?;
    Ok(result)
}

pub(super) fn symbolic_basis(key: &BinderKey, span: Span) -> Ty {
    Ty::parameter(TypeParameter {
        key: Some(key.clone()),
        name: key.name.clone(),
        span,
    })
}
pub(super) fn expect(
    actual: &Ty,
    expected: &Ty,
    context: &Context,
    span: Span,
    budget: &Budget,
) -> Result<()> {
    let same = equivalent(actual, expected, context, span, budget)?;
    if same {
        Ok(())
    } else {
        Err(SourceError::new(
            "type",
            span,
            format!(
                "type or tuple/size shape mismatch: expected `{}`, found `{}`",
                expected.display(Stage::Runtime),
                actual.display(Stage::Runtime)
            ),
        ))
    }
}
pub(super) fn equivalent(
    actual: &Ty,
    expected: &Ty,
    context: &Context,
    span: Span,
    budget: &Budget,
) -> Result<bool> {
    budget.ty(span, actual)?;
    budget.ty(span, expected)?;
    actual.equivalent_by_budgeted(
        expected,
        &mut |a, b| {
            Ok::<_, SourceError>(
                context.proves_le_budgeted(
                    a,
                    b,
                    span,
                    "while checking type size equality",
                    &mut |span, cells| budget.sized_charge(span, cells),
                )? && context.proves_le_budgeted(
                    b,
                    a,
                    span,
                    "while checking type size equality",
                    &mut |span, cells| budget.sized_charge(span, cells),
                )?,
            )
        },
        &mut |cells| budget.charge(span, cells),
    )
}
