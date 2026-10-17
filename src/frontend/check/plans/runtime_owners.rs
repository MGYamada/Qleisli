//! Original ordered owner types at common-checked coherent access actions.
//! These untrusted snapshots grant no caller-prefix or frame preservation proof.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.

use super::*;
use crate::frontend::resolve::locals::Lookup;

#[derive(Clone, Debug)]
pub(in crate::frontend) struct RuntimeOwnerPlan {
    pub reference: ResolvedReference,
    pub ty: Arc<Ty>,
    // Preserve the common capture's immutable type payload independently of
    // the transport field. Identity detects replacement, never proves typing.
    source_type: Arc<Ty>,
}

impl Capture<'_, '_> {
    pub fn runtime_owners(
        &self,
        expression: &ast::Expr,
        scope: &Scope,
    ) -> Result<Vec<RuntimeOwnerPlan>> {
        let span = expression.span;
        self.budget.charge(span, 4)?;
        let ast::ExprKind::AccessCall { args, .. } = &expression.kind else {
            return Err(SourceError::new(
                "source",
                span,
                "control snapshot lacks its original access call",
            ));
        };
        self.budget
            .charge(span, args.len().saturating_mul(2).saturating_add(1))?;
        if args.is_empty()
            || args.len() > 64
            || !args
                .iter()
                .any(|argument| argument.access == ast::QuantumAccess::Ctrl)
        {
            return Err(SourceError::new(
                "source",
                span,
                "control snapshot lacks its ordered Ctrl arguments",
            ));
        }
        let mut owners = Vec::with_capacity(args.len());
        for argument in args {
            self.budget.charge(argument.value.span, 2)?;
            let ast::ExprKind::Name(name) = &argument.value.kind else {
                return Err(SourceError::new(
                    "source",
                    argument.value.span,
                    "control snapshot requires original lexical owners",
                ));
            };
            let reference = self.reference(name)?;
            let Some(key) = reference.local.as_ref() else {
                return Err(SourceError::new(
                    "source",
                    name.span,
                    "control snapshot lacks its original runtime binder",
                ));
            };
            self.budget.charge(
                name.span,
                key.name
                    .len()
                    .saturating_mul(scope.values.len().saturating_add(1))
                    .saturating_add(3),
            )?;
            let binding = scope.values.get(key).ok_or_else(|| {
                SourceError::new(
                    "source",
                    name.span,
                    "control snapshot lacks its live original owner",
                )
            })?;
            if self
                .index
                .table
                .try_binder(key.id)
                .is_none_or(|binder| binder.kind != BindingKind::Runtime)
                || binding.ty.quantum_basis().is_none()
            {
                return Err(SourceError::new(
                    "source",
                    name.span,
                    "control snapshot requires one original quantum owner",
                ));
            }
            self.budget.charge(name.span, 2)?;
            let ty = Arc::new(self.budget.copy_ty(name.span, &binding.ty)?);
            owners.push(RuntimeOwnerPlan {
                reference,
                source_type: Arc::clone(&ty),
                ty,
            });
        }
        Ok(owners)
    }
}

impl Validation<'_, '_> {
    pub(super) fn runtime_owners(
        &self,
        owner: DefId,
        node: NodeId,
        kind: &ObligationKind,
        owners: &[RuntimeOwnerPlan],
        span: Span,
    ) -> Result<()> {
        self.budget.charge(span, owners.len().saturating_add(2))?;
        if !matches!(kind, ObligationKind::ControlSectors) {
            return if owners.is_empty() {
                Ok(())
            } else {
                Err(self.failure(span))
            };
        }
        let expression = self.expression(owner, node, span)?;
        let ast::ExprKind::AccessCall { args, .. } = &expression.kind else {
            return Err(self.failure(span));
        };
        self.budget.charge(span, args.len())?;
        if args.is_empty()
            || args.len() > 64
            || args.len() != owners.len()
            || !args
                .iter()
                .any(|argument| argument.access == ast::QuantumAccess::Ctrl)
        {
            return Err(self.failure(span));
        }
        for (argument, retained) in args.iter().zip(owners) {
            let ast::ExprKind::Name(name) = &argument.value.kind else {
                return Err(self.failure(argument.value.span));
            };
            self.named_reference(owner, &retained.reference, name)?;
            let Some(key) = retained.reference.local.as_ref() else {
                return Err(self.failure(name.span));
            };
            if self.key(owner, key, name.span)? != BindingKind::Runtime
                || retained.ty.quantum_basis().is_none()
                || !Arc::ptr_eq(&retained.ty, &retained.source_type)
            {
                return Err(self.failure(name.span));
            }
            self.ty(owner, &retained.ty, name.span)?;
        }
        Ok(())
    }
}

/// Borrow only the canonical common judgment for this exact original action.
/// Types are retained source metadata; a fresh native action gate is mandatory.
#[allow(clippy::too_many_arguments)]
pub(in crate::frontend) fn original_runtime_owners<'plan, E>(
    program: &'plan CheckedProgram,
    locals: &Lookup<'_, '_>,
    owner: DefId,
    module: ModuleId,
    original: &ast::Expr,
    obligation: &'plan Obligation,
    charge: &mut impl FnMut(Span, usize) -> std::result::Result<(), E>,
    error: &impl Fn(Span, &'static str) -> E,
) -> std::result::Result<&'plan [RuntimeOwnerPlan], E> {
    let span = original.span;
    macro_rules! refuse {
        () => {{
            let message = "runtime owner snapshot differs from its original control action";
            charge(span, message.len() + 1)?;
            return Err(error(span, message));
        }};
    }
    charge(span, 24)?;
    let plan = &obligation.plan;
    if !program
        .obligations
        .get(obligation.id.ordinal)
        .is_some_and(|canonical| std::ptr::eq(canonical, obligation))
        || obligation.id.definition != owner
        || obligation.definition != owner
        || !matches!(obligation.kind, ObligationKind::ControlSectors)
        || !matches!(plan.subject, EvidenceSubject::Expression)
        || plan.environment.owner != owner
        || plan.environment.module != module
        || program
            .resolution
            .try_declaration(owner)
            .is_none_or(|declaration| declaration.module != module)
        || !program
            .lexical
            .get(&owner)
            .is_some_and(|table| locals.original_table_is(owner, table))
        || locals.try_node_id_expr(original) != Some(plan.node)
    {
        refuse!();
    }
    let borrowed = locals.original_node_budgeted(plan.node, &mut *charge)?;
    if !matches!(borrowed, Some(OriginalNode::Expression(source)) if std::ptr::eq(source, original))
    {
        refuse!();
    }
    let ast::ExprKind::AccessCall { args, .. } = &original.kind else {
        refuse!();
    };
    charge(span, args.len().saturating_mul(4).saturating_add(2))?;
    if args.is_empty()
        || args.len() > 64
        || args.len() != plan.runtime_owners.len()
        || !args
            .iter()
            .any(|argument| argument.access == ast::QuantumAccess::Ctrl)
    {
        refuse!();
    }
    let table = &program.lexical[&owner];
    for (argument, retained) in args.iter().zip(&plan.runtime_owners) {
        let ast::ExprKind::Name(name) = &argument.value.kind else {
            refuse!();
        };
        let Some(key) = retained.reference.local.as_ref() else {
            refuse!();
        };
        charge(
            name.span,
            key.name.len().saturating_mul(2).saturating_add(8),
        )?;
        if locals.try_reference_site(name) != Some(retained.reference.site)
            || retained.reference.site.definition() != owner
            || retained.reference.target != ResolvedUse::Local(key.id)
            || table
                .try_usage(retained.reference.site)
                .is_none_or(|usage| usage.target != retained.reference.target)
            || table
                .try_binder(key.id)
                .is_none_or(|binder| binder.kind != BindingKind::Runtime || binder.key != *key)
            || retained.ty.quantum_basis().is_none()
            || !Arc::ptr_eq(&retained.ty, &retained.source_type)
        {
            refuse!();
        }
    }
    Ok(&plan.runtime_owners)
}
