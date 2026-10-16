//! Complete original body static metadata, independent of incidental call plans.
//! These borrowed associations supply no native acceptance or preservation proof.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.

use super::*;
use crate::frontend::resolve::locals::Lookup;

#[derive(Clone, Debug)]
pub(in crate::frontend) enum BodyStaticKind {
    Binding {
        key: BinderKey,
        value: Arc<ResolvedNatural>,
    },
    Natural {
        value: Arc<ResolvedNatural>,
    },
    Operation {
        operation: Arc<ResolvedStatic>,
        expression: NodeId,
        requested: [bool; 3],
    },
    Predicate {
        left: Arc<ResolvedNatural>,
        comparison: ast::Compare,
        right: Arc<ResolvedNatural>,
    },
    Fold {
        index: BinderKey,
        start: Arc<ResolvedNatural>,
        end: Arc<ResolvedNatural>,
        carry_type: Arc<Ty>,
    },
    PrimitiveCall {
        callee: ResolvedReference,
        arguments: Vec<Arc<ResolvedStatic>>,
    },
}

#[derive(Clone, Debug)]
pub(in crate::frontend) struct BodyStaticPlan {
    pub owner: DefId,
    pub module: ModuleId,
    pub node: NodeId,
    pub environment: Arc<StaticEnvironment>,
    pub kind: BodyStaticKind,
}

#[derive(Clone, Copy)]
pub(in crate::frontend) enum BodyStaticOriginal<'a> {
    Expression(&'a ast::Expr),
    Natural(&'a ast::Natural),
    Operation(&'a ast::StaticOp),
}

/// Borrow only the plan for this exact original occurrence and collection.
/// No cloned syntax, span search or other site's static environment is used.
pub(in crate::frontend) fn original_body_static<'plan, E>(
    program: &'plan CheckedProgram,
    locals: &Lookup<'_, '_>,
    owner: DefId,
    module: ModuleId,
    original: BodyStaticOriginal<'_>,
    charge: &mut impl FnMut(Span, usize) -> std::result::Result<(), E>,
    error: &impl Fn(Span, &'static str) -> E,
) -> std::result::Result<&'plan BodyStaticPlan, E> {
    let span = match original {
        BodyStaticOriginal::Expression(value) => value.span,
        BodyStaticOriginal::Natural(value) => value.span,
        BodyStaticOriginal::Operation(value) => value.span,
    };
    macro_rules! refuse {
        () => {{
            let message = "body static plan differs from its original occurrence";
            charge(span, message.len() + 1)?;
            return Err(error(span, message));
        }};
    }
    charge(span, 16)?;
    let node = match original {
        BodyStaticOriginal::Expression(value) => locals.try_node_id_expr(value),
        BodyStaticOriginal::Natural(value) => locals.try_node_id_natural(value),
        BodyStaticOriginal::Operation(value) => locals.try_node_id_static_op(value),
    };
    let Some(node) = node.filter(|node| node.definition() == owner) else {
        refuse!();
    };
    charge(span, 8)?;
    if !program
        .lexical
        .get(&owner)
        .is_some_and(|table| locals.original_table_is(owner, table))
    {
        refuse!();
    }
    let borrowed = locals.original_node_budgeted(node, &mut *charge)?;
    let same = match (original, borrowed) {
        (BodyStaticOriginal::Expression(a), Some(OriginalNode::Expression(b))) => {
            std::ptr::eq(a, b)
        }
        (BodyStaticOriginal::Natural(a), Some(OriginalNode::Natural(b))) => std::ptr::eq(a, b),
        (BodyStaticOriginal::Operation(a), Some(OriginalNode::Operation(b))) => std::ptr::eq(a, b),
        _ => false,
    };
    if !same {
        refuse!();
    }
    charge(span, 8)?;
    let Some(plan) = program.body_statics.get(&node) else {
        refuse!();
    };
    if plan.owner != owner
        || plan.module != module
        || plan.node != node
        || plan.environment.owner != owner
        || plan.environment.module != module
        || program
            .resolution
            .try_declaration(owner)
            .is_none_or(|declaration| declaration.module != module)
    {
        refuse!();
    }
    let kind_matches = match (original, &plan.kind) {
        (
            BodyStaticOriginal::Natural(_),
            BodyStaticKind::Binding { value, .. } | BodyStaticKind::Natural { value },
        ) => value.node == node,
        (
            BodyStaticOriginal::Operation(original),
            BodyStaticKind::Operation {
                operation,
                expression,
                requested,
            },
        ) => {
            let Some(OriginalNode::Expression(parent)) =
                locals.original_node_budgeted(*expression, &mut *charge)?
            else {
                refuse!();
            };
            let (child, demand) = match &parent.kind {
                ast::ExprKind::ApplyStatic { operation, .. } => (operation, [true, false, false]),
                ast::ExprKind::Adjoint { operation, .. } => (operation, [false, true, false]),
                ast::ExprKind::Controlled { operation, .. } => (operation, [false, false, true]),
                _ => refuse!(),
            };
            operation.node == Some(node) && std::ptr::eq(child, original) && requested == &demand
        }
        (
            BodyStaticOriginal::Expression(ast::Expr {
                kind: ast::ExprKind::StaticIf { .. },
                ..
            }),
            BodyStaticKind::Predicate { .. },
        ) => true,
        (
            BodyStaticOriginal::Expression(ast::Expr {
                kind: ast::ExprKind::StaticFold { .. },
                ..
            }),
            BodyStaticKind::Fold { .. },
        ) => true,
        (
            BodyStaticOriginal::Expression(expression),
            BodyStaticKind::PrimitiveCall { callee, arguments },
        ) => {
            let (name, source) = match &expression.kind {
                ast::ExprKind::Call {
                    callee,
                    static_args,
                    ..
                }
                | ast::ExprKind::AccessCall {
                    callee,
                    static_args,
                    ..
                } => (callee, static_args),
                _ => refuse!(),
            };
            charge(span, source.len() + 8)?;
            locals.try_reference_site(name) == Some(callee.site)
                && matches!(
                    callee.target,
                    ResolvedUse::Global(resolve::Target::Primitive(_))
                )
                && locals.usage(name).target == callee.target
                && source.len() == arguments.len()
        }
        _ => false,
    };
    if !kind_matches {
        refuse!();
    }
    Ok(plan)
}

/// Immediate static operands of one original runtime expression. Runtime
/// children are checked separately; natural arithmetic children remain in the
/// complete retained root rather than being copied quadratically.
pub(in crate::frontend::check) fn expression_natural_roots<'a>(
    expression: &'a ast::Expr,
    budget: &Budget,
) -> Result<Vec<&'a ast::Natural>> {
    enum Pending<'a> {
        Operation(&'a ast::StaticOp),
        Type(&'a ast::Type),
    }
    let mut pending = Vec::new();
    let mut roots = Vec::new();
    let span = expression.span;
    budget.charge(span, 2)?;
    match &expression.kind {
        ast::ExprKind::Call { static_args, .. } | ast::ExprKind::AccessCall { static_args, .. } => {
            budget.charge(span, static_args.len())?;
            pending.extend(static_args.iter().rev().map(Pending::Operation));
        }
        ast::ExprKind::ApplyStatic { operation, .. }
        | ast::ExprKind::Adjoint { operation, .. }
        | ast::ExprKind::Controlled { operation, .. } => {
            pending.push(Pending::Operation(operation))
        }
        ast::ExprKind::StaticIf { predicate, .. } => {
            budget.charge(span, 2)?;
            roots.extend([&predicate.left, &predicate.right]);
        }
        ast::ExprKind::StaticFold { start, end, .. } => {
            budget.charge(span, 2)?;
            roots.extend([start, end]);
        }
        _ => {}
    }
    if let ast::ExprKind::AccessCall { args, .. } = &expression.kind {
        for argument in args {
            budget.charge(argument.value.span, 1)?;
            if let Some(selection) = &argument.selection {
                for natural in selection.naturals() {
                    budget.charge(natural.span, 1)?;
                    roots.push(natural);
                }
            }
        }
    }
    while let Some(item) = pending.pop() {
        budget.charge(span, 3)?;
        match item {
            Pending::Operation(operation) => match &operation.kind {
                ast::StaticOpKind::Natural(natural) => roots.push(natural),
                ast::StaticOpKind::Type(ty) => pending.push(Pending::Type(ty)),
                ast::StaticOpKind::Repeat(count, child) => {
                    let (ast::Count::Natural(natural) | ast::Count::Power(natural)) = count;
                    roots.push(natural);
                    pending.push(Pending::Operation(child));
                }
                ast::StaticOpKind::Inverse(child) | ast::StaticOpKind::Controlled(child) => {
                    pending.push(Pending::Operation(child))
                }
                ast::StaticOpKind::Then(a, b)
                | ast::StaticOpKind::Tensor(a, b)
                | ast::StaticOpKind::Conjugate(a, b) => {
                    pending.extend([Pending::Operation(b), Pending::Operation(a)]);
                }
                ast::StaticOpKind::Specialize { arguments, .. } => {
                    budget.charge(operation.span, arguments.len())?;
                    pending.extend(arguments.iter().rev().map(Pending::Operation));
                }
                _ => {}
            },
            Pending::Type(ty) => match &ty.kind {
                ast::TypeKind::Bits(natural) => roots.push(natural),
                ast::TypeKind::Q(child) => pending.push(Pending::Type(child)),
                ast::TypeKind::Tuple(fields) => {
                    budget.charge(ty.span, fields.len())?;
                    pending.extend(fields.iter().rev().map(Pending::Type));
                }
                _ => {}
            },
        }
    }
    Ok(roots)
}

impl Validation<'_, '_> {
    fn body_static(&self, node: NodeId, plan: &BodyStaticPlan) -> Result<()> {
        let owner = plan.owner;
        let span = Span::default();
        self.budget.charge(span, 5)?;
        let kind = match &plan.kind {
            BodyStaticKind::Binding { .. } | BodyStaticKind::Natural { .. } => NodeKind::Natural,
            BodyStaticKind::Operation { .. } => NodeKind::StaticOp,
            _ => NodeKind::Expr,
        };
        let source = self.original(owner, node, kind, span)?;
        let span = source.span();
        if node != plan.node
            || plan.environment.owner != owner
            || plan.environment.module != plan.module
            || self
                .resolution
                .try_declaration(owner)
                .is_none_or(|declaration| declaration.module != plan.module)
        {
            return Err(self.failure(span));
        }
        self.environment_kind(&plan.environment, node, span, kind)?;
        match (&plan.kind, source) {
            (BodyStaticKind::Binding { key, value }, OriginalNode::Natural(source)) => {
                if self.key(owner, key, span)? != BindingKind::StaticNatural || value.node != node {
                    return Err(self.failure(span));
                }
                self.natural_at(owner, source, value, 1)?;
                self.local_initializer(owner, key, value, span)?;
            }
            (BodyStaticKind::Natural { value }, OriginalNode::Natural(source)) => {
                self.natural_at(owner, source, value, 1)?;
            }
            (
                BodyStaticKind::Operation {
                    operation,
                    expression,
                    requested,
                },
                OriginalNode::Operation(source),
            ) => {
                self.operation_at(owner, source, operation, 1)?;
                let parent = self.expression(owner, *expression, span)?;
                let (child, demand) = match &parent.kind {
                    ast::ExprKind::ApplyStatic { operation, .. } => {
                        (operation, [true, false, false])
                    }
                    ast::ExprKind::Adjoint { operation, .. } => (operation, [false, true, false]),
                    ast::ExprKind::Controlled { operation, .. } => {
                        (operation, [false, false, true])
                    }
                    _ => return Err(self.failure(span)),
                };
                if !std::ptr::eq(child, source) || requested != &demand {
                    return Err(self.failure(span));
                }
            }
            (
                BodyStaticKind::Predicate {
                    left,
                    comparison,
                    right,
                },
                OriginalNode::Expression(source),
            ) => {
                let ast::ExprKind::StaticIf { predicate, .. } = &source.kind else {
                    return Err(self.failure(span));
                };
                if *comparison != predicate.comparison {
                    return Err(self.failure(span));
                }
                self.natural_at(owner, &predicate.left, left, 1)?;
                self.natural_at(owner, &predicate.right, right, 1)?;
            }
            (
                BodyStaticKind::Fold {
                    index,
                    start,
                    end,
                    carry_type,
                },
                OriginalNode::Expression(source),
            ) => {
                let ast::ExprKind::StaticFold {
                    index: original_index,
                    start: original_start,
                    end: original_end,
                    ..
                } = &source.kind
                else {
                    return Err(self.failure(span));
                };
                if self.key(owner, index, span)? != BindingKind::FoldIndex
                    || self.indices[&owner].try_binder(original_index) != Some(index.id)
                {
                    return Err(self.failure(span));
                }
                self.natural_at(owner, original_start, start, 1)?;
                self.natural_at(owner, original_end, end, 1)?;
                self.ty(owner, carry_type, span)?;
            }
            (
                BodyStaticKind::PrimitiveCall { callee, arguments },
                OriginalNode::Expression(source),
            ) => {
                let (name, originals) = match &source.kind {
                    ast::ExprKind::Call {
                        callee,
                        static_args,
                        ..
                    }
                    | ast::ExprKind::AccessCall {
                        callee,
                        static_args,
                        ..
                    } => (callee, static_args),
                    _ => return Err(self.failure(span)),
                };
                self.reference(owner, callee, span)?;
                if !matches!(
                    callee.target,
                    ResolvedUse::Global(resolve::Target::Primitive(_))
                ) || self.indices[&owner].try_usage(name) != Some(callee.site)
                    || originals.len() != arguments.len()
                    || originals.is_empty()
                {
                    return Err(self.failure(span));
                }
                for (original, argument) in originals.iter().zip(arguments) {
                    self.operation_at(owner, original, argument, 1)?;
                }
            }
            _ => return Err(self.failure(span)),
        }
        Ok(())
    }

    fn require_body_site(
        &self,
        plans: &BTreeMap<NodeId, BodyStaticPlan>,
        expected: &mut BTreeSet<NodeId>,
        node: NodeId,
        span: Span,
        kind: impl FnOnce(&BodyStaticKind) -> bool,
    ) -> Result<()> {
        self.budget.charge(span, 3)?;
        if !plans.get(&node).is_some_and(|plan| kind(&plan.kind)) || !expected.insert(node) {
            return Err(self.failure(span));
        }
        Ok(())
    }

    pub(super) fn body_statics(&self, plans: &BTreeMap<NodeId, BodyStaticPlan>) -> Result<()> {
        for (node, plan) in plans {
            self.body_static(*node, plan)?;
        }
        let mut expected = BTreeSet::new();
        // Completeness is checked against every original source node, not the
        // presence of an incidental call/evidence plan in one branch or body.
        for index in self.indices.values() {
            for original in index.original_nodes() {
                self.budget.charge(original.span(), 1)?;
                match original {
                    OriginalNode::Expression(expression) => {
                        let node = index.node_id_expr(expression);
                        match &expression.kind {
                            ast::ExprKind::ApplyStatic { operation, .. }
                            | ast::ExprKind::Adjoint { operation, .. }
                            | ast::ExprKind::Controlled { operation, .. } => self
                                .require_body_site(
                                    plans,
                                    &mut expected,
                                    index.node_id_static_op(operation),
                                    operation.span,
                                    |kind| matches!(kind, BodyStaticKind::Operation { .. }),
                                )?,
                            ast::ExprKind::StaticIf { .. } => self.require_body_site(
                                plans,
                                &mut expected,
                                node,
                                expression.span,
                                |kind| matches!(kind, BodyStaticKind::Predicate { .. }),
                            )?,
                            ast::ExprKind::StaticFold { .. } => self.require_body_site(
                                plans,
                                &mut expected,
                                node,
                                expression.span,
                                |kind| matches!(kind, BodyStaticKind::Fold { .. }),
                            )?,
                            ast::ExprKind::Call {
                                callee,
                                static_args,
                                ..
                            }
                            | ast::ExprKind::AccessCall {
                                callee,
                                static_args,
                                ..
                            } if !static_args.is_empty() => {
                                self.budget.charge(expression.span, 2)?;
                                if matches!(
                                    index.table.usage(index.usage(callee)).target,
                                    ResolvedUse::Global(resolve::Target::Primitive(_))
                                ) {
                                    self.require_body_site(
                                        plans,
                                        &mut expected,
                                        node,
                                        expression.span,
                                        |kind| matches!(kind, BodyStaticKind::PrimitiveCall { .. }),
                                    )?;
                                }
                            }
                            _ => {}
                        }
                        for natural in expression_natural_roots(expression, self.budget)? {
                            self.require_body_site(
                                plans,
                                &mut expected,
                                index.node_id_natural(natural),
                                natural.span,
                                |kind| matches!(kind, BodyStaticKind::Natural { .. }),
                            )?;
                        }
                    }
                    OriginalNode::Block(block) => {
                        for statement in &block.statements {
                            self.budget.charge(statement.span, 1)?;
                            if let ast::StmtKind::StaticLet { value, .. } = &statement.kind {
                                self.require_body_site(
                                    plans,
                                    &mut expected,
                                    index.node_id_natural(value),
                                    value.span,
                                    |kind| matches!(kind, BodyStaticKind::Binding { .. }),
                                )?;
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        self.budget.charge(Span::default(), 1)?;
        if expected.len() != plans.len() {
            return Err(self.failure(Span::default()));
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests;
