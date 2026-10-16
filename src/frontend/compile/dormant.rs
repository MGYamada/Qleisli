//! Closed operation requests in uninstantiated Op-only bodies still need the
//! ordinary concrete gates. Unbound formals remain conditional; their closed
//! siblings and zero-count children do not inherit that deferral.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.

use super::*;
use crate::frontend::check::plans::{EvidenceSubject, ResolvedStatic, StaticEnvironment};
use crate::frontend::resolve::locals::{OriginalNode, UseSiteId};
use operations::{Bindings, Operation, RequiredOperation};

mod controls;
#[cfg(test)]
mod tests;

fn charge_port_copy(
    ty: &Ty,
    copies: usize,
    charge: &mut impl FnMut(usize) -> Result<(), CompileError>,
) -> Result<(), CompileError> {
    // Finite types already obey the shared depth limit. Recurse without an
    // allocation, charging both the visit and each later copied cell first.
    charge(1 + copies)?;
    match &ty.kind {
        Kind::Q(inner) => charge_port_copy(inner, copies, charge)?,
        Kind::Tuple(fields) => {
            charge(fields.len().saturating_mul(copies))?;
            for field in fields {
                charge_port_copy(field, copies, charge)?;
            }
        }
        _ => {}
    }
    Ok(())
}

impl<'a> Compiler<'a> {
    fn dormant_error(
        &mut self,
        module: &str,
        span: Span,
        code: ErrorCode,
        message: &'static str,
    ) -> Result<CompileError, CompileError> {
        self.charge(module, span, message.len() + 1)?;
        Ok(self.error(module, span, code, message))
    }

    fn dormant_module(&mut self, owner: Key, span: Span) -> Result<String, CompileError> {
        let name = &self.source.resolution.declaration(owner).name.0;
        let mut work = self.work;
        let charged = self.charge_at(&mut work, name, span, name.len() + 1);
        self.work = work;
        charged?;
        Ok(self.source.resolution.declaration(owner).name.0.clone())
    }

    fn original_operation(
        &mut self,
        owner: Key,
        module: &str,
        operation: &ResolvedStatic,
    ) -> Result<&'a StaticOp, CompileError> {
        let mut work = self.work;
        let original = match operation.node {
            Some(node) if node.definition() == owner => {
                self.locals().original_node_budgeted(node, |span, cells| {
                    self.charge_at(&mut work, module, span, cells)
                })
            }
            _ => Ok(None),
        };
        self.work = work;
        match original? {
            Some(OriginalNode::Operation(original)) if original.span == operation.span => {
                Ok(original)
            }
            _ => Err(self.dormant_error(
                module,
                operation.span,
                ErrorCode::TypeMismatch,
                "closed operation request lacks its original source association",
            )?),
        }
    }

    fn closed_operation(
        &mut self,
        module: &str,
        original: &StaticOp,
        environment: &StaticEnvironment,
        requested: [bool; 3],
        depth: usize,
    ) -> Result<Option<Operation>, CompileError> {
        self.tick(module, original.span)?;
        if depth > MAX_DEPTH {
            return Err(self.dormant_error(
                module,
                original.span,
                ErrorCode::Limit,
                "dormant operation exceeds the static depth limit",
            )?);
        }
        match &original.kind {
            StaticOpKind::Name(name) => {
                if self.unbound_operation(module, name, environment)? {
                    return Ok(None);
                }
                self.provider(module, name, None).map(Some)
            }
            StaticOpKind::Bind {
                implementation,
                meaning,
            } => {
                // A local implementation remains conditional, but its Meaning
                // reference must still name the original closed declaration.
                self.meaning_key(module, meaning)?;
                if self.unbound_operation(module, implementation, environment)? {
                    return Ok(None);
                }
                self.provider(module, implementation, Some(meaning))
                    .map(Some)
            }
            StaticOpKind::Inverse(child)
            | StaticOpKind::Controlled(child)
            | StaticOpKind::Repeat(_, child) => {
                let child_requests = match &original.kind {
                    // Forming adjoint itself requires the operand's J path.
                    StaticOpKind::Inverse(_) => [requested[1], true, requested[2]],
                    // Each requested path of the constructed controlled object
                    // uses the operand's C path; formation alone requests none.
                    StaticOpKind::Controlled(_) => {
                        [false, false, requested[0] || requested[1] || requested[2]]
                    }
                    // Even zero copies first materialize the original child.
                    _ => requested,
                };
                let Some(child) =
                    self.closed_operation(module, child, environment, child_requests, depth + 1)?
                else {
                    return Ok(None);
                };
                if matches!(original.kind, StaticOpKind::Inverse(_)) {
                    self.validate_operation_access(
                        &child,
                        [false, true, false],
                        module,
                        original.span,
                    )?;
                }
                self.construct(module, original.span, &original.kind, child, None)
                    .map(Some)
            }
            StaticOpKind::Then(left, right)
            | StaticOpKind::Tensor(left, right)
            | StaticOpKind::Conjugate(left, right) => {
                let left_requests = if matches!(original.kind, StaticOpKind::Conjugate(..)) {
                    let needed = requested[0] || requested[1] || requested[2];
                    [needed, needed, false]
                } else {
                    requested
                };
                let closed_left =
                    self.closed_operation(module, left, environment, left_requests, depth + 1)?;
                // Do not short-circuit: a deferred left operand cannot hide a
                // closed request in the right operand.
                let closed_right =
                    self.closed_operation(module, right, environment, requested, depth + 1)?;
                match (closed_left, closed_right) {
                    (Some(left), Some(right)) => self
                        .construct(module, original.span, &original.kind, left, Some(right))
                        .map(Some),
                    (closed_left, closed_right) => {
                        // Only maximal closed fragments need separate access
                        // checks. Complete composites retain their whole gate.
                        if let Some(operation) = closed_left {
                            self.validate_operation_access(
                                &operation,
                                left_requests,
                                module,
                                left.span,
                            )?;
                        }
                        if let Some(operation) = closed_right {
                            self.validate_operation_access(
                                &operation, requested, module, right.span,
                            )?;
                        }
                        Ok(None)
                    }
                }
            }
            StaticOpKind::Type(_) | StaticOpKind::Natural(_) | StaticOpKind::Specialize { .. } => {
                Err(self.dormant_error(
                    module,
                    original.span,
                    ErrorCode::Unsupported,
                    "static argument is outside the finite lowering profile",
                )?)
            }
        }
    }

    fn unbound_operation(
        &mut self,
        module: &str,
        name: &Ident,
        environment: &StaticEnvironment,
    ) -> Result<bool, CompileError> {
        self.tick(module, name.span)?;
        let ResolvedUse::Local(id) = self.locals().usage(name).target else {
            return Ok(false);
        };
        let binding = self.locals().info(id);
        self.charge(
            module,
            name.span,
            (binding.key.name.len() + 3).saturating_mul(environment.operations.len() + 1),
        )?;
        let binding = self.locals().info(id);
        if id.definition() == environment.owner
            && binding.kind == super::super::resolve::locals::BindingKind::StaticOperation
            && environment.operations.contains_key(&binding.key)
        {
            return Ok(true);
        }
        Err(self.dormant_error(
            module,
            name.span,
            ErrorCode::TypeMismatch,
            "only an unbound original Op formal can defer an operation request",
        )?)
    }

    pub(super) fn check_dormant_operations(&mut self) -> Result<(), CompileError> {
        let previous = self.checking;
        let result = self.check_dormant_operations_inner();
        self.checking = previous;
        result
    }

    fn check_dormant_operations_inner(&mut self) -> Result<(), CompileError> {
        let Some((&first, declaration)) = self.declarations.first_key_value() else {
            return Ok(());
        };
        let at = declaration.span;
        let root_module = self.dormant_module(first, at)?;
        // The complete original obligation collection is retained unchanged.
        // Runtime-expression subjects need their actual owner/frame gates;
        // this pass does not claim to discharge those conditional obligations.
        for ordinal in 0..self.source.obligations.len() {
            self.tick(&root_module, at)?;
            let obligation = &self.source.obligations[ordinal];
            let check::ObligationKind::MeaningEquality { required, .. } = obligation.kind else {
                continue;
            };
            if self.declarations[&obligation.definition]
                .static_params
                .is_empty()
            {
                continue;
            }
            let EvidenceSubject::Operation { .. } = &obligation.plan.subject else {
                continue;
            };
            let owner = obligation.definition;
            let span = obligation.span;
            let module = self.dormant_module(owner, span)?;
            self.charge(&module, span, 2)?;
            let obligation = &self.source.obligations[ordinal];
            let EvidenceSubject::Operation { operation, .. } = &obligation.plan.subject else {
                unreachable!("borrowed original operation subject")
            };
            let operation = Arc::clone(operation);
            let environment = Arc::clone(&obligation.plan.environment);
            self.checking = Some(owner);
            let original = self.original_operation(owner, &module, &operation)?;
            if let Some(actual) =
                self.closed_operation(&module, original, &environment, [false; 3], 1)?
            {
                let meaning = &self.meanings[&required];
                let mut work = self.work;
                let charged = (|| {
                    let mut charge = |cells| self.charge_at(&mut work, &module, span, cells);
                    charge_port_copy(&meaning.basis, 1, &mut charge)?;
                    charge_port_copy(&meaning.codomain, 1, &mut charge)?;
                    charge(meaning.matrix.entries().len() + 1)
                })();
                self.work = work;
                charged?;
                let meaning = &self.meanings[&required];
                let required = RequiredOperation {
                    basis: meaning.basis.clone(),
                    codomain: meaning.codomain.clone(),
                    // Explicit checked_op captures available access here,
                    // not a demand for every capability. Formal/constructor
                    // requests are checked separately at their actual sites.
                    access: [false; 3],
                    meaning: Some(meaning.matrix.clone()),
                };
                self.validate_required_operation(&required, &actual, &module, original.span)?;
            }
        }

        // Copy only numeric occurrence identities once, with charged storage.
        // Repeated nth() searches or deep plan clones would evade this budget.
        self.charge(&root_module, at, self.source.static_calls.len() + 1)?;
        let sites: Vec<_> = self.source.static_calls.keys().copied().collect();
        for site in sites {
            self.tick(&root_module, at)?;
            let plan = &self.source.static_calls[&site];
            if plan.arguments.is_empty() || self.declarations[&plan.owner].static_params.is_empty()
            {
                continue;
            }
            let (owner, target) = (plan.owner, plan.target);
            let at = self.declarations[&owner].span;
            let module = self.dormant_module(owner, at)?;
            if let Some(bindings) = self.closed_call_bindings(site, &module, at)? {
                self.checking = Some(target);
                lower::lower_bound_function(self, &target, bindings)?;
            }
        }
        Ok(())
    }

    /// Every closed actual reaches the same gates, including siblings of an
    /// unbound formal. None retains an unfinished call, never a successful one.
    fn closed_call_bindings(
        &mut self,
        site: UseSiteId,
        module: &str,
        at: Span,
    ) -> Result<Option<Bindings>, CompileError> {
        self.tick(module, at)?;
        let plan = &self.source.static_calls[&site];
        let (owner, target, count) = (plan.owner, plan.target, plan.arguments.len());
        self.charge(module, at, 2 + count * 2)?;
        let environment = Arc::clone(&self.source.static_calls[&site].environment);
        self.checking = Some(owner);
        let required = self.required_bindings(&target)?;
        let mut bindings = Bindings::new();
        let mut identity = Vec::with_capacity(count);
        let mut complete = true;
        for ordinal in 0..count {
            let actual = &self.source.static_calls[&site].arguments[ordinal];
            self.charge(module, actual.value.span, 1)?;
            let actual = &self.source.static_calls[&site].arguments[ordinal];
            let value = Arc::clone(&actual.value);
            let original = self.original_operation(owner, module, &value)?;
            // Obtain the actual formal demand before deciding whether the
            // complete argument closes. Deferral cannot erase this demand.
            let formal = &self.source.static_calls[&site].arguments[ordinal].formal;
            self.charge(
                module,
                original.span,
                (formal.name.len() + 2).saturating_mul(required.len() + 1),
            )?;
            let formal = &self.source.static_calls[&site].arguments[ordinal].formal;
            let requested = required[formal].access;
            if let Some(operation) =
                self.closed_operation(module, original, &environment, requested, 1)?
            {
                let formal = &self.source.static_calls[&site].arguments[ordinal].formal;
                self.charge(
                    module,
                    original.span,
                    (formal.name.len() + 2).saturating_mul(required.len() + 1),
                )?;
                let formal = &self.source.static_calls[&site].arguments[ordinal].formal;
                self.validate_required_operation(
                    &required[formal],
                    &operation,
                    module,
                    original.span,
                )?;
                let formal = &self.source.static_calls[&site].arguments[ordinal].formal;
                self.charge(
                    module,
                    original.span,
                    (formal.name.len() + 2).saturating_mul(bindings.len() + 1),
                )?;
                let mut work = self.work;
                let charged = (|| {
                    let mut charge =
                        |cells| self.charge_at(&mut work, module, original.span, cells);
                    charge_port_copy(&operation.basis, 2, &mut charge)?;
                    charge_port_copy(&operation.codomain, 2, &mut charge)?;
                    charge(
                        operation
                            .meaning
                            .as_ref()
                            .map_or(0, |m| m.entries().len())
                            .saturating_mul(2)
                            + 2,
                    )
                })();
                self.work = work;
                charged?;
                let formal = self.source.static_calls[&site].arguments[ordinal]
                    .formal
                    .clone();
                identity.push(operation.clone());
                bindings.insert(formal, operation);
            } else {
                complete = false;
            }
        }
        if complete {
            self.record_operation_instance(target, identity, module, at)?;
            Ok(Some(bindings))
        } else {
            Ok(None)
        }
    }
}
