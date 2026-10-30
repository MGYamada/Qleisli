//! Closed operation requests in uninstantiated Op-only bodies still need the
//! ordinary concrete gates. Unbound formals remain conditional; their closed
//! siblings and zero-count children do not inherit that deferral.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.

use super::*;
use crate::frontend::check::plans::{
    BodyStaticKind, BodyStaticOriginal, EvidenceSubject, ResolvedStatic, ResolvedStaticKind,
    StaticEnvironment, original_body_static,
};
use crate::frontend::resolve::locals::{OriginalNode, UseSiteId};
use operations::{Bindings, Operation, RequiredOperation};

mod controls;
#[cfg(test)]
mod tests;

pub(super) fn charge_port_copy(
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

pub(super) fn charge_source_type_copy(
    ty: &check::Ty,
    charge: &mut impl FnMut(usize) -> Result<(), CompileError>,
) -> Result<(), CompileError> {
    charge(2)?;
    match &ty.kind {
        Kind::Bits(size) => {
            charge(size.terms.len())?;
            for key in size.terms.keys() {
                charge(key.name.len() + 1)?;
            }
        }
        Kind::Parameter(parameter) => {
            charge(parameter.name.len() + 1)?;
            if let Some(key) = &parameter.key {
                charge(key.name.len() + 1)?;
            }
        }
        Kind::Q(child) => charge_source_type_copy(child, charge)?,
        Kind::Tuple(fields) => {
            charge(fields.len())?;
            for field in fields {
                charge_source_type_copy(field, charge)?;
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

    pub(super) fn dormant_module(
        &mut self,
        owner: Key,
        span: Span,
    ) -> Result<String, CompileError> {
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

    pub(super) fn dormant_operation_bindings(
        &mut self,
        module: &str,
        span: Span,
    ) -> Result<Bindings, CompileError> {
        let current = self.concrete_context.current.as_ref();
        let mut work = self.work;
        let result = (|| {
            let Some(current) = current else {
                return Ok(Bindings::new());
            };
            for (key, operation) in &current.operations {
                self.charge_at(
                    &mut work,
                    module,
                    span,
                    key.name.len() + operation.copy_size() + 1,
                )?;
            }
            Ok(current.operations.clone())
        })();
        self.work = work;
        result
    }

    fn visit_dormant_owner<T>(
        &mut self,
        owner: Key,
        module: &str,
        span: Span,
        visit: impl FnOnce(&mut Self) -> Result<T, CompileError>,
    ) -> Result<T, CompileError> {
        if self.current_instance_owner() == Some(owner) {
            return visit(self);
        }
        let frame = self.enter_dormant_owner(owner, module, span)?;
        let result = visit(self);
        self.leave_instance(frame);
        result
    }

    fn dormant_region_active(
        &mut self,
        environment: &StaticEnvironment,
        module: &str,
        span: Span,
    ) -> Result<Option<bool>, CompileError> {
        use check::plans::StaticRegion;
        let mut complete = true;
        for region in &environment.regions {
            self.tick(module, span)?;
            match region {
                StaticRegion::Predicate {
                    left,
                    comparison,
                    right,
                    truth,
                    ..
                } => {
                    let left = self.evaluate_plan_natural_partial(left, environment)?;
                    let right = self.evaluate_plan_natural_partial(right, environment)?;
                    if let (Some(left), Some(right)) = (left, right) {
                        let actual = match comparison {
                            Compare::Eq => left == right,
                            Compare::Ne => left != right,
                            Compare::Lt => left < right,
                            Compare::Le => left <= right,
                            Compare::Gt => left > right,
                            Compare::Ge => left >= right,
                        };
                        if actual != *truth {
                            return Ok(Some(false));
                        }
                    } else {
                        complete = false;
                    }
                }
                StaticRegion::Fold { start, end, .. } => {
                    let start = self.evaluate_plan_natural_partial(start, environment)?;
                    let end = self.evaluate_plan_natural_partial(end, environment)?;
                    if let (Some(start), Some(end)) = (start, end) {
                        if start > end {
                            return Err(self.dormant_error(
                                module,
                                span,
                                ErrorCode::TypeMismatch,
                                "active original static fold has reversed bounds",
                            )?);
                        }
                        if start == end {
                            return Ok(Some(false));
                        }
                    } else {
                        complete = false;
                    }
                }
            }
        }
        Ok(complete.then_some(true))
    }

    fn visit_dormant_environment<T>(
        &mut self,
        environment: &StaticEnvironment,
        module: &str,
        span: Span,
        visit: impl FnOnce(&mut Self, bool) -> Result<T, CompileError>,
    ) -> Result<T, CompileError> {
        self.visit_dormant_owner(environment.owner, module, span, |compiler| {
            let inactive =
                compiler.dormant_region_active(environment, module, span)? == Some(false);
            if inactive {
                // Retain closed independent siblings while original formals in
                // an inactive region remain conditional. Never replay n-1 at
                // n=0 outside the premise under which its source was checked.
                let frame = compiler.enter_inactive_region(environment.owner, module, span)?;
                let result = visit(compiler, true);
                compiler.leave_instance(frame);
                result
            } else {
                visit(compiler, false)
            }
        })
    }

    fn closed_operation(
        &mut self,
        module: &str,
        value: &ResolvedStatic,
        environment: &StaticEnvironment,
        requested: [bool; 3],
    ) -> Result<Option<Operation>, CompileError> {
        self.original_operation(environment.owner, module, value)?;
        let outer = self.dormant_operation_bindings(module, value.span)?;
        match self.evaluate_source_static(
            value,
            environment,
            check::plans::StaticCategory::Operation,
            requested,
            &outer,
            module,
        )? {
            instances::StaticValue::Operation(operation) => Ok(Some(operation)),
            instances::StaticValue::Deferred => Ok(None),
            _ => Err(self.dormant_error(
                module,
                value.span,
                ErrorCode::TypeMismatch,
                "dormant operation differs from its original static category",
            )?),
        }
    }

    fn dormant_operation_root(
        &mut self,
        module: &str,
        operation: &ResolvedStatic,
        environment: &StaticEnvironment,
        requested: [bool; 3],
        inactive: bool,
    ) -> Result<(), CompileError> {
        let original = self.original_operation(environment.owner, module, operation)?;
        let mut leaf = original;
        while let StaticOpKind::Repeat(_, child) = &leaf.kind {
            self.tick(module, leaf.span)?;
            leaf = child;
        }
        let name = match &leaf.kind {
            StaticOpKind::Name(name) | StaticOpKind::Specialize { name, .. } => Some(name),
            _ => None,
        };
        let direct = if let Some(name) = name {
            self.charge(module, name.span, 8)?;
            self.locals().try_reference_site(name).and_then(|site| {
                (site.definition() == environment.owner)
                    .then(|| (site, self.locals().usage(name).target))
            })
        } else {
            None
        };
        if let Some((site, ResolvedUse::Global(target))) = direct {
            // Direct runtime declaration/group transforms and legacy sealed
            // literal repetition are not opaque one-owner Op providers.
            // Their retained ordinary Nat counts still visit every child,
            // including under zero copies or an unresolved outer count.
            let mut value = operation;
            while let ResolvedStaticKind::Repeat {
                power,
                count,
                child,
            } = &value.kind
            {
                if let Some(count_value) = self.evaluate_plan_natural_partial(count, environment)? {
                    self.closed_repeat_count(count_value, *power, module, count.span)?;
                }
                value = child;
            }
            match target {
                Target::Declaration(target) => {
                    self.charge(module, operation.span, 12)?;
                    let Some(plan) = self.source.static_calls.get(&site) else {
                        return Err(self.dormant_error(
                            module,
                            operation.span,
                            ErrorCode::TypeMismatch,
                            "direct dormant transform lacks its original call plan",
                        )?);
                    };
                    if plan.owner != environment.owner
                        || plan.module != environment.module
                        || plan.target != target
                        || plan.callee.site != site
                        || plan.callee.target != ResolvedUse::Global(Target::Declaration(target))
                        || plan.callee.local.is_some()
                        || requested
                            .iter()
                            .zip(plan.access)
                            .any(|(requested, available)| *requested && !available)
                    {
                        return Err(self.dormant_error(module, operation.span, ErrorCode::TypeMismatch,
                            "direct dormant transform differs from its original call identity or access")?);
                    }
                    if let Some(instance) =
                        self.closed_call_instance(site, module, operation.span)?
                    {
                        if !inactive
                            || !self.instance_is_active(&instance, module, operation.span)?
                        {
                            self.materialize_instance(instance, module, operation.span)?;
                        }
                    }
                    return Ok(());
                }
                Target::Primitive(_) => return Ok(()),
                Target::Type(_) => {
                    return Err(self.dormant_error(
                        module,
                        operation.span,
                        ErrorCode::TypeMismatch,
                        "a type declaration is not an operation provider",
                    )?);
                }
            }
        }
        self.closed_operation(module, operation, environment, requested)
            .map(|_| ())
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
            return Ok(self
                .concrete_context
                .current
                .as_ref()
                .is_none_or(|instance| !instance.operations.contains_key(&binding.key)));
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
        let result = self.check_dormant_operations_inner(None);
        self.checking = previous;
        result
    }

    /// Closed function pairs remain semantic obligations in unused generic
    /// bodies and zero-count regions. Both source adapters use this same gate.
    pub(super) fn check_dormant_function_contracts(&mut self) -> Result<(), CompileError> {
        let previous = self.checking;
        let result = (|| {
            for ordinal in 0..self.source.obligations.len() {
                let obligation = &self.source.obligations[ordinal];
                let check::ObligationKind::FunctionEquality {
                    implementation,
                    specification,
                } = obligation.kind
                else {
                    continue;
                };
                let (definition, span) = (obligation.definition, obligation.span);
                self.checking = Some(definition);
                let module = self
                    .source
                    .resolution
                    .declaration(definition)
                    .name
                    .0
                    .clone();
                if self.effect_in_module(&module, implementation)
                    == Some(crate::ir::Effect::Observe)
                {
                    self.instrument_contract_evidence(
                        &module,
                        span,
                        implementation,
                        specification,
                    )?;
                } else {
                    self.function_contract_evidence(&module, span, implementation, specification)?;
                }
            }
            Ok(())
        })();
        self.checking = previous;
        result
    }

    /// Every concrete owner revisits its original dead/zero source obligations
    /// before executable-body reuse. No placeholder actual or function handle
    /// stands in for a genuinely unbound original formal.
    pub(super) fn check_dormant_instance(
        &mut self,
        instance: Arc<instances::ClosedInstance>,
        module: &str,
        span: Span,
    ) -> Result<(), CompileError> {
        let owner = instance.definition;
        let frame = self.enter_instance(instance, module, span)?;
        let result = (|| {
            self.check_dormant_operations_inner(Some(owner))?;
            self.check_dormant_controls_inner(Some(owner))
        })();
        self.leave_instance(frame);
        result
    }

    fn check_dormant_operations_inner(
        &mut self,
        owner_filter: Option<Key>,
    ) -> Result<(), CompileError> {
        let Some((&first, declaration)) = self.declarations.first_key_value() else {
            return Ok(());
        };
        let at = declaration.span;
        let root_module = self.dormant_module(first, at)?;
        for ordinal in 0..self.source.obligations.len() {
            self.tick(&root_module, at)?;
            let obligation = &self.source.obligations[ordinal];
            let check::ObligationKind::MeaningEquality { required, .. } = obligation.kind else {
                continue;
            };
            if owner_filter.is_some_and(|owner| owner != obligation.definition) {
                continue;
            }
            let EvidenceSubject::Operation { .. } = &obligation.plan.subject else {
                continue;
            };
            let (owner, span) = (obligation.definition, obligation.span);
            let module = self.dormant_module(owner, span)?;
            self.charge(&module, span, 2)?;
            let obligation = &self.source.obligations[ordinal];
            let EvidenceSubject::Operation { operation, .. } = &obligation.plan.subject else {
                unreachable!()
            };
            let operation = Arc::clone(operation);
            let environment = Arc::clone(&obligation.plan.environment);
            self.visit_dormant_environment(&environment, &module, span, |compiler, _inactive| {
                let Some(actual) =
                    compiler.closed_operation(&module, &operation, &environment, [false; 3])?
                else {
                    return Ok(());
                };
                let meaning = &compiler.meanings[&required];
                let mut work = compiler.work;
                let charged = (|| {
                    let mut charge = |cells| compiler.charge_at(&mut work, &module, span, cells);
                    charge_port_copy(&meaning.basis, 1, &mut charge)?;
                    charge_port_copy(&meaning.codomain, 1, &mut charge)?;
                    charge(meaning.matrix.entries().len() + 1)
                })();
                compiler.work = work;
                charged?;
                let meaning = &compiler.meanings[&required];
                let requirement = RequiredOperation {
                    basis: meaning.basis.clone(),
                    codomain: meaning.codomain.clone(),
                    access: [false; 3],
                    meaning: Some(meaning.matrix.clone()),
                };
                compiler.validate_required_operation(&requirement, &actual, &module, operation.span)
            })?;
        }
        // Standalone original body statics do not require an incidental call
        // or Meaning obligation. Visit their closed siblings even when an
        // initializer is unused or a fold executes zero times.
        self.charge(&root_module, at, self.source.body_statics.len() + 1)?;
        let nodes: Vec<_> = self.source.body_statics.keys().copied().collect();
        for node in nodes {
            self.tick(&root_module, at)?;
            let plan = &self.source.body_statics[&node];
            if owner_filter.is_some_and(|owner| owner != plan.owner)
                || matches!(plan.kind, BodyStaticKind::PrimitiveCall { .. })
            {
                continue;
            }
            let (owner, module_id) = (plan.owner, plan.module);
            let declaration_span = self.declarations[&owner].span;
            let module = self.dormant_module(owner, declaration_span)?;
            let mut work = self.work;
            let captured = (|| {
                let Some(original) = self.locals().original_node_budgeted(node, |at, cells| {
                    self.charge_at(&mut work, &module, at, cells)
                })?
                else {
                    let message = "dormant static root lacks its original source association";
                    self.charge_at(&mut work, &module, declaration_span, message.len() + 1)?;
                    return Err(self.error(
                        &module,
                        declaration_span,
                        ErrorCode::TypeMismatch,
                        message,
                    ));
                };
                let span = original.span();
                let source = match original {
                    OriginalNode::Operation(original) => BodyStaticOriginal::Operation(original),
                    OriginalNode::Natural(original) => BodyStaticOriginal::Natural(original),
                    OriginalNode::Expression(original) => BodyStaticOriginal::Expression(original),
                    _ => {
                        let message =
                            "dormant static root has a different original syntax category";
                        self.charge_at(&mut work, &module, span, message.len() + 1)?;
                        return Err(self.error(&module, span, ErrorCode::TypeMismatch, message));
                    }
                };
                let plan = original_body_static(
                    &self.source,
                    &self.locals(),
                    owner,
                    module_id,
                    source,
                    &mut |at, cells| self.charge_at(&mut work, &module, at, cells),
                    &|at, message| self.error(&module, at, ErrorCode::TypeMismatch, message),
                )?;
                self.charge_at(&mut work, &module, span, 6)?;
                let (naturals, operation, range) = match &plan.kind {
                    BodyStaticKind::Binding { value, .. } | BodyStaticKind::Natural { value } => {
                        (vec![Arc::clone(value)], None, false)
                    }
                    BodyStaticKind::Predicate { left, right, .. } => {
                        (vec![Arc::clone(left), Arc::clone(right)], None, false)
                    }
                    BodyStaticKind::Fold { start, end, .. } => {
                        (vec![Arc::clone(start), Arc::clone(end)], None, true)
                    }
                    BodyStaticKind::Operation {
                        operation,
                        requested,
                        ..
                    } => (Vec::new(), Some((Arc::clone(operation), *requested)), false),
                    BodyStaticKind::PrimitiveCall { .. } => {
                        unreachable!("primitive operands retain separate natural roots")
                    }
                };
                Ok::<_, CompileError>((
                    naturals,
                    operation,
                    range,
                    Arc::clone(&plan.environment),
                    span,
                ))
            })();
            self.work = work;
            let (naturals, operation, range, environment, span) = captured?;
            self.visit_dormant_environment(&environment, &module, span, |compiler, inactive| {
                let mut start = None;
                for (ordinal, natural) in naturals.iter().enumerate() {
                    let value = compiler.evaluate_plan_natural_partial(natural, &environment)?;
                    if ordinal == 0 {
                        start = value;
                    } else if range
                        && matches!((start,value),(Some(start),Some(end)) if start > end)
                    {
                        return Err(compiler.dormant_error(
                            &module,
                            span,
                            ErrorCode::TypeMismatch,
                            "original static fold has reversed closed bounds",
                        )?);
                    }
                }
                if let Some((operation, requested)) = &operation {
                    compiler.dormant_operation_root(
                        &module,
                        operation,
                        &environment,
                        *requested,
                        inactive,
                    )?;
                }
                Ok(())
            })?;
        }
        self.charge(&root_module, at, self.source.static_calls.len() + 1)?;
        let sites: Vec<_> = self.source.static_calls.keys().copied().collect();
        for site in sites {
            self.tick(&root_module, at)?;
            let plan = &self.source.static_calls[&site];
            if plan.arguments.is_empty() || owner_filter.is_some_and(|owner| owner != plan.owner) {
                continue;
            }
            let (owner, span) = (plan.owner, self.declarations[&plan.owner].span);
            let module = self.dormant_module(owner, span)?;
            self.charge(&module, span, 1)?;
            let environment = Arc::clone(&self.source.static_calls[&site].environment);
            self.visit_dormant_environment(&environment, &module, span, |compiler, inactive| {
                if let Some(instance) = compiler.closed_call_instance(site, &module, span)? {
                    // All actuals and their formal contracts were checked by
                    // the binder. An inactive edge back to this exact active
                    // instance cannot execute; its selected body is already
                    // being checked. Independent closed callees still recurse.
                    if !inactive || !compiler.instance_is_active(&instance, &module, span)? {
                        compiler.materialize_instance(instance, &module, span)?;
                    }
                }
                Ok(())
            })?;
        }
        Ok(())
    }

    /// Check all original categories/siblings and formal access demands before
    /// deferral; only a complete substitution can obtain an actual instance.
    fn closed_call_instance(
        &mut self,
        site: UseSiteId,
        module: &str,
        at: Span,
    ) -> Result<Option<Arc<instances::ClosedInstance>>, CompileError> {
        self.tick(module, at)?;
        let plan = &self.source.static_calls[&site];
        let (owner, target, node) = (plan.owner, plan.target, plan.node);
        let mut work = self.work;
        let arguments = (|| {
            self.charge_at(
                &mut work,
                module,
                at,
                plan.arguments.len().saturating_mul(2) + 16,
            )?;
            if self
                .source
                .resolution
                .try_declaration(owner)
                .is_none_or(|declaration| {
                    declaration.module != plan.module || declaration.name.0 != module
                })
                || plan.environment.owner != owner
                || plan.environment.module != plan.module
                || self
                    .source
                    .lexical
                    .get(&owner)
                    .is_none_or(|table| !self.locals().original_table_is(owner, table))
                || self
                    .source
                    .lexical
                    .get(&owner)
                    .and_then(|table| table.try_usage(site))
                    .is_none_or(|usage| {
                        usage.target != ResolvedUse::Global(Target::Declaration(target))
                    })
                || plan.source_effect != self.effect_in_module(module, target)
            {
                let message = "dormant call differs from its original collection and source effect";
                self.charge_at(&mut work, module, at, message.len() + 1)?;
                return Err(self.error(module, at, ErrorCode::TypeMismatch, message));
            }
            let expression = self.locals().original_node_budgeted(node, |span, cells| {
                self.charge_at(&mut work, module, span, cells)
            })?;
            let Some(OriginalNode::Expression(expression)) = expression else {
                let message = "dormant call lacks its original expression association";
                self.charge_at(&mut work, module, at, message.len() + 1)?;
                return Err(self.error(module, at, ErrorCode::TypeMismatch, message));
            };
            let runtime = matches!(expression.kind, ExprKind::Call { .. });
            for actual in &plan.arguments {
                self.charge_at(
                    &mut work,
                    module,
                    actual.value.span,
                    actual.formal.name.len() + 2,
                )?;
            }
            Ok((
                plan.arguments.clone(),
                Arc::clone(&plan.environment),
                runtime,
            ))
        })();
        self.work = work;
        let (arguments, environment, runtime) = arguments?;
        let outer = self.dormant_operation_bindings(module, at)?;
        if runtime {
            self.bind_runtime_source_instance_partial(
                target,
                &arguments,
                &environment,
                &outer,
                module,
                at,
            )
        } else {
            self.bind_source_instance_partial(target, &arguments, &environment, &outer, module, at)
        }
    }
}
