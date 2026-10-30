//! Original closed static actual preparation; source profile admission is separate.
use super::*;
use crate::frontend::check::plans::{
    ResolvedStatic, ResolvedStaticKind, StaticActual, StaticCategory,
};
use crate::frontend::resolve::{Target, locals::BindingKind};

impl Compiler<'_> {
    pub(super) fn source_environment(
        &mut self,
        environment: &StaticEnvironment,
        module: &str,
        span: Span,
    ) -> Result<(), CompileError> {
        self.charge(module, span, module.len() + 4)?;
        let declaration = self.source.resolution.try_declaration(environment.owner);
        if self.current_instance_owner() != Some(environment.owner)
            || declaration.is_none_or(|declaration| {
                declaration.name.0 != module || declaration.module != environment.module
            })
            || !self.source.lexical.contains_key(&environment.owner)
        {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "static plan differs from its active original source owner",
            ));
        }
        Ok(())
    }

    pub(super) fn source_reference(
        &mut self,
        reference: &ResolvedReference,
        environment: &StaticEnvironment,
        module: &str,
        span: Span,
    ) -> Result<(), CompileError> {
        self.charge(
            module,
            span,
            4 + reference.local.as_ref().map_or(0, |key| key.name.len()),
        )?;
        let table = &self.source.lexical[&environment.owner];
        let Some(original) = table.try_usage(reference.site) else {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "static reference has no original occurrence",
            ));
        };
        let local = match original.target {
            ResolvedUse::Local(id) => table.try_binder(id).map(|binding| &binding.key),
            _ => None,
        };
        if reference.site.definition() != environment.owner
            || original.target != reference.target
            || local != reference.local.as_ref()
        {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "static reference differs from its original occurrence",
            ));
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    pub(in crate::frontend::compile) fn evaluate_source_static(
        &mut self,
        value: &ResolvedStatic,
        environment: &StaticEnvironment,
        category: StaticCategory,
        requested: [bool; 3],
        outer_ops: &operations::Bindings,
        module: &str,
    ) -> Result<StaticValue, CompileError> {
        self.source_environment(environment, module, value.span)?;
        let span = value.span;
        let value = self.source_static(
            value,
            environment,
            category,
            requested,
            outer_ops,
            module,
            1,
        )?;
        if let StaticValue::Operation(operation) = &value {
            self.validate_operation_access(operation, requested, module, span)?;
        }
        Ok(value)
    }

    #[allow(clippy::too_many_arguments)]
    fn source_static(
        &mut self,
        value: &ResolvedStatic,
        environment: &StaticEnvironment,
        category: StaticCategory,
        requested: [bool; 3],
        outer_ops: &operations::Bindings,
        module: &str,
        depth: usize,
    ) -> Result<StaticValue, CompileError> {
        self.tick(module, value.span)?;
        if depth > MAX_DEPTH {
            return Err(self.error(
                module,
                value.span,
                ErrorCode::Limit,
                "static description exceeds its finite depth limit",
            ));
        }
        if value
            .node
            .is_some_and(|node| node.definition() != environment.owner)
        {
            return Err(self.error(
                module,
                value.span,
                ErrorCode::TypeMismatch,
                "foreign original static occurrence",
            ));
        }
        match category {
            StaticCategory::Basis => match &value.kind {
                ResolvedStaticKind::Basis(basis) => Ok(self
                    .close_resolved_basis(basis, environment, module, value.span)?
                    .map_or(StaticValue::Deferred, StaticValue::Basis)),
                ResolvedStaticKind::Name(reference) => {
                    self.source_reference(reference, environment, module, value.span)?;
                    let Some(key) = reference.local.as_ref() else {
                        return Err(self.error(
                            module,
                            value.span,
                            ErrorCode::TypeMismatch,
                            "Basis actual requires an original Basis binder",
                        ));
                    };
                    self.charge(
                        module,
                        value.span,
                        key.name.len() + environment.bases.len() + 2,
                    )?;
                    if self.source.lexical[&environment.owner]
                        .try_binder(key.id)
                        .is_none_or(|binder| binder.kind != BindingKind::StaticBasis)
                        || !environment.bases.contains_key(key)
                    {
                        return Err(self.error(
                            module,
                            value.span,
                            ErrorCode::TypeMismatch,
                            "static reference is not an original Basis formal",
                        ));
                    }
                    let Some(basis) = self
                        .concrete_context
                        .current
                        .as_ref()
                        .and_then(|instance| instance.interface.bases.get(key))
                    else {
                        return Ok(StaticValue::Deferred);
                    };
                    let mut work = self.work;
                    let mut precise = None;
                    let checked =
                        types::closed_basis_capacity(basis, value.span, &mut |span, cells| {
                            self.charge_at(&mut work, module, span, cells)
                                .map_err(|error| {
                                    precise = Some(error);
                                    SourceError::new("limit", span, "Basis actual work limit")
                                })
                        });
                    self.work = work;
                    if let Some(error) = precise {
                        return Err(error);
                    }
                    checked.map_err(|error| self.originals.error(error.in_module(module)))?;
                    let cost = operations::port_nodes(
                        &self
                            .concrete_context
                            .current
                            .as_ref()
                            .unwrap()
                            .interface
                            .bases[key],
                    );
                    self.charge(module, value.span, cost)?;
                    Ok(StaticValue::Basis(
                        self.concrete_context
                            .current
                            .as_ref()
                            .unwrap()
                            .interface
                            .bases[key]
                            .clone(),
                    ))
                }
                _ => Err(self.error(
                    module,
                    value.span,
                    ErrorCode::TypeMismatch,
                    "static actual is not a Basis",
                )),
            },
            StaticCategory::Natural => {
                let number = match &value.kind {
                    ResolvedStaticKind::Natural(number) => {
                        self.evaluate_plan_natural_partial(number, environment)?
                    }
                    ResolvedStaticKind::Name(reference) => {
                        self.source_reference(reference, environment, module, value.span)?;
                        self.evaluate_plan_reference_partial(reference, value.span, environment)?
                    }
                    _ => {
                        return Err(self.error(
                            module,
                            value.span,
                            ErrorCode::TypeMismatch,
                            "static actual is not a Nat",
                        ));
                    }
                };
                Ok(number.map_or(StaticValue::Deferred, StaticValue::Natural))
            }
            StaticCategory::Operation => {
                self.source_operation(value, environment, requested, outer_ops, module, depth)
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn source_operation(
        &mut self,
        value: &ResolvedStatic,
        environment: &StaticEnvironment,
        requested: [bool; 3],
        outer_ops: &operations::Bindings,
        module: &str,
        depth: usize,
    ) -> Result<StaticValue, CompileError> {
        use operations::Constructor;
        let operation = match &value.kind {
            ResolvedStaticKind::Name(reference) => {
                self.source_reference(reference, environment, module, value.span)?;
                match reference.target {
                    ResolvedUse::Local(id) => {
                        let Some(key) = reference.local.as_ref() else {
                            return Err(self.error(
                                module,
                                value.span,
                                ErrorCode::TypeMismatch,
                                "local Op has no original binder",
                            ));
                        };
                        self.charge(
                            module,
                            value.span,
                            key.name
                                .len()
                                .saturating_mul(outer_ops.len() + environment.operations.len() + 1)
                                + 3,
                        )?;
                        if self.source.lexical[&environment.owner]
                            .try_binder(id)
                            .is_none_or(|binder| binder.kind != BindingKind::StaticOperation)
                            || !environment.operations.contains_key(key)
                        {
                            return Err(self.error(
                                module,
                                value.span,
                                ErrorCode::TypeMismatch,
                                "only an original unbound Op formal can defer",
                            ));
                        }
                        let Some(operation) = outer_ops.get(key) else {
                            return Ok(StaticValue::Deferred);
                        };
                        self.charge(module, value.span, operation.copy_size())?;
                        outer_ops[key].clone()
                    }
                    ResolvedUse::Global(Target::Declaration(target)) => {
                        let instance = self.prepare_instance(
                            target,
                            BTreeMap::new(),
                            BTreeMap::new(),
                            BTreeMap::new(),
                            module,
                            value.span,
                        )?;
                        self.provider_instance(instance, None, module, value.span)?
                    }
                    _ => {
                        return Err(self.error(
                            module,
                            value.span,
                            ErrorCode::TypeMismatch,
                            "operation actual requires a checked provider",
                        ));
                    }
                }
            }
            ResolvedStaticKind::Specialize(reference, arguments) => {
                self.source_reference(reference, environment, module, value.span)?;
                let ResolvedUse::Global(Target::Declaration(target)) = reference.target else {
                    return Err(self.error(
                        module,
                        value.span,
                        ErrorCode::TypeMismatch,
                        "specialized provider requires an original declaration",
                    ));
                };
                let Some(instance) = self.bind_resolved_instance(
                    target,
                    arguments.iter(),
                    environment,
                    outer_ops,
                    module,
                    value.span,
                    false,
                )?
                else {
                    return Ok(StaticValue::Deferred);
                };
                self.provider_instance(instance, None, module, value.span)?
            }
            ResolvedStaticKind::Bind(implementation, meaning) => {
                self.source_reference(meaning, environment, module, value.span)?;
                let ResolvedUse::Global(Target::Declaration(meaning)) = meaning.target else {
                    return Err(self.error(
                        module,
                        value.span,
                        ErrorCode::TypeMismatch,
                        "checked_op requires an original closed Meaning",
                    ));
                };
                if !self.meanings.contains_key(&meaning) {
                    return Err(self.error(
                        module,
                        value.span,
                        ErrorCode::TypeMismatch,
                        "checked_op specification is not a Meaning",
                    ));
                }
                self.source_reference(implementation, environment, module, value.span)?;
                match implementation.target {
                    ResolvedUse::Local(id) => {
                        let key = implementation.local.as_ref().ok_or_else(|| {
                            self.error(
                                module,
                                value.span,
                                ErrorCode::TypeMismatch,
                                "checked_op local implementation lacks its original binder",
                            )
                        })?;
                        self.charge(
                            module,
                            value.span,
                            key.name
                                .len()
                                .saturating_mul(outer_ops.len() + environment.operations.len() + 1)
                                + 3,
                        )?;
                        if self.source.lexical[&environment.owner]
                            .try_binder(id)
                            .is_none_or(|binder| binder.kind != BindingKind::StaticOperation)
                            || !environment.operations.contains_key(key)
                        {
                            return Err(self.error(
                                module,
                                value.span,
                                ErrorCode::TypeMismatch,
                                "checked_op local implementation is not an original Op formal",
                            ));
                        }
                        let Some(operation) = outer_ops.get(key) else {
                            return Ok(StaticValue::Deferred);
                        };
                        self.charge(module, value.span, operation.copy_size())?;
                        let operation = outer_ops[key].clone();
                        self.bind_operation_meaning(operation, meaning, module, value.span)?
                    }
                    ResolvedUse::Global(Target::Declaration(target)) => {
                        let instance = self.prepare_instance(
                            target,
                            BTreeMap::new(),
                            BTreeMap::new(),
                            BTreeMap::new(),
                            module,
                            value.span,
                        )?;
                        self.provider_instance(instance, Some(meaning), module, value.span)?
                    }
                    _ => {
                        return Err(self.error(
                            module,
                            value.span,
                            ErrorCode::TypeMismatch,
                            "checked_op requires an original provider",
                        ));
                    }
                }
            }
            ResolvedStaticKind::Inverse(child)
            | ResolvedStaticKind::Controlled(child)
            | ResolvedStaticKind::Repeat { child, .. } => {
                let demand = match &value.kind {
                    ResolvedStaticKind::Inverse(_) => [requested[1], true, requested[2]],
                    ResolvedStaticKind::Controlled(_) => {
                        [false, false, requested.iter().any(|demand| *demand)]
                    }
                    _ => requested,
                };
                let child = self.source_static(
                    child,
                    environment,
                    StaticCategory::Operation,
                    demand,
                    outer_ops,
                    module,
                    depth + 1,
                )?;
                // Counts are original ordinary-u32 plans, even when the child
                // is deferred or the eventual repeat has zero executions.
                let constructor = match &value.kind {
                    ResolvedStaticKind::Inverse(_) => Some(Constructor::Inverse),
                    ResolvedStaticKind::Controlled(_) => Some(Constructor::Controlled),
                    ResolvedStaticKind::Repeat { power, count, .. } => self
                        .evaluate_plan_natural_partial(count, environment)?
                        .map(|number| self.closed_repeat_count(number, *power, module, count.span))
                        .transpose()?
                        .map(Constructor::Repeat),
                    _ => unreachable!(),
                };
                match (child, constructor) {
                    (StaticValue::Operation(child), Some(constructor)) => {
                        if matches!(constructor, Constructor::Inverse) {
                            self.validate_operation_access(
                                &child,
                                [false, true, false],
                                module,
                                value.span,
                            )?;
                        }
                        self.construct_closed(module, value.span, constructor, child, None)?
                    }
                    (StaticValue::Operation(child), None) => {
                        self.validate_operation_access(&child, demand, module, value.span)?;
                        return Ok(StaticValue::Deferred);
                    }
                    (StaticValue::Deferred, _) => return Ok(StaticValue::Deferred),
                    _ => unreachable!("operation category"),
                }
            }
            ResolvedStaticKind::Then(left, right)
            | ResolvedStaticKind::Tensor(left, right)
            | ResolvedStaticKind::Conjugate(left, right) => {
                let demand = if matches!(value.kind, ResolvedStaticKind::Conjugate(..)) {
                    let needed = requested.iter().any(|demand| *demand);
                    [needed, needed, false]
                } else {
                    requested
                };
                let left = self.source_static(
                    left,
                    environment,
                    StaticCategory::Operation,
                    demand,
                    outer_ops,
                    module,
                    depth + 1,
                )?;
                let right = self.source_static(
                    right,
                    environment,
                    StaticCategory::Operation,
                    requested,
                    outer_ops,
                    module,
                    depth + 1,
                )?;
                match (left, right) {
                    (StaticValue::Operation(left), StaticValue::Operation(right)) => {
                        let constructor = match value.kind {
                            ResolvedStaticKind::Then(..) => Constructor::Then,
                            ResolvedStaticKind::Tensor(..) => Constructor::Tensor,
                            _ => Constructor::Conjugate,
                        };
                        self.construct_closed(module, value.span, constructor, left, Some(right))?
                    }
                    (left, right) => {
                        if let StaticValue::Operation(left) = left {
                            self.validate_operation_access(&left, demand, module, value.span)?;
                        }
                        if let StaticValue::Operation(right) = right {
                            self.validate_operation_access(&right, requested, module, value.span)?;
                        }
                        return Ok(StaticValue::Deferred);
                    }
                }
            }
            _ => {
                return Err(self.error(
                    module,
                    value.span,
                    ErrorCode::TypeMismatch,
                    "static actual is not an Op",
                ));
            }
        };
        // The caller checks the complete aggregate once; partial composites
        // above independently check only their maximal closed fragments.
        Ok(StaticValue::Operation(operation))
    }

    pub(in crate::frontend::compile) fn closed_repeat_count(
        &self,
        number: u32,
        power: bool,
        module: &str,
        span: Span,
    ) -> Result<u16, CompileError> {
        let count = if power {
            1u32.checked_shl(number)
        } else {
            Some(number)
        };
        count
            .and_then(|count| u16::try_from(count).ok())
            .filter(|count| *count <= 4096)
            .ok_or_else(|| {
                self.error(
                    module,
                    span,
                    ErrorCode::Limit,
                    "static repetition exceeds 4096",
                )
            })
    }

    #[allow(clippy::too_many_arguments)]
    pub(in crate::frontend::compile) fn bind_source_instance_partial(
        &mut self,
        target: Key,
        actuals: &[StaticActual],
        environment: &StaticEnvironment,
        outer_ops: &operations::Bindings,
        module: &str,
        span: Span,
    ) -> Result<Option<Arc<ClosedInstance>>, CompileError> {
        self.bind_source_instance_partial_mode(
            target,
            actuals,
            environment,
            outer_ops,
            module,
            span,
            false,
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(in crate::frontend::compile) fn bind_runtime_source_instance_partial(
        &mut self,
        target: Key,
        actuals: &[StaticActual],
        environment: &StaticEnvironment,
        outer_ops: &operations::Bindings,
        module: &str,
        span: Span,
    ) -> Result<Option<Arc<ClosedInstance>>, CompileError> {
        let typed = self.source.interfaces[&target]
            .statics
            .iter()
            .all(|formal| !matches!(formal.kind, StaticKind::Operation { .. }));
        self.bind_source_instance_partial_mode(
            target,
            actuals,
            environment,
            outer_ops,
            module,
            span,
            typed,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn bind_source_instance_partial_mode(
        &mut self,
        target: Key,
        actuals: &[StaticActual],
        environment: &StaticEnvironment,
        outer_ops: &operations::Bindings,
        module: &str,
        span: Span,
        typed: bool,
    ) -> Result<Option<Arc<ClosedInstance>>, CompileError> {
        self.source_environment(environment, module, span)?;
        self.charge(module, span, actuals.len() + 1)?;
        let count = self
            .source
            .interfaces
            .get(&target)
            .ok_or_else(|| {
                self.error(
                    module,
                    span,
                    ErrorCode::TypeMismatch,
                    "callee has no original checked interface",
                )
            })?
            .statics
            .len();
        if count != actuals.len() {
            return Err(self.error(
                module,
                span,
                ErrorCode::Arity,
                "static actual count differs from the original interface",
            ));
        }
        for (ordinal, actual) in actuals.iter().enumerate() {
            let key_size = self.source.interfaces[&target].statics[ordinal]
                .key
                .name
                .len();
            self.charge(module, span, key_size + actual.formal.name.len() + 2)?;
            let formal = &self.source.interfaces[&target].statics[ordinal];
            let category = match formal.kind {
                StaticKind::Basis => StaticCategory::Basis,
                StaticKind::Natural => StaticCategory::Natural,
                StaticKind::Operation { .. } => StaticCategory::Operation,
            };
            if actual.formal != formal.key || actual.category != category {
                return Err(self.error(
                    module,
                    span,
                    ErrorCode::TypeMismatch,
                    "static actual differs from its original formal/category",
                ));
            }
        }
        self.bind_resolved_instance(
            target,
            actuals.iter().map(|actual| actual.value.as_ref()),
            environment,
            outer_ops,
            module,
            span,
            typed,
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(in crate::frontend::compile) fn bind_source_instance(
        &mut self,
        target: Key,
        actuals: &[StaticActual],
        environment: &StaticEnvironment,
        outer_ops: &operations::Bindings,
        module: &str,
        span: Span,
    ) -> Result<Arc<ClosedInstance>, CompileError> {
        self.bind_source_instance_partial(target, actuals, environment, outer_ops, module, span)?
            .ok_or_else(|| {
                self.error(
                    module,
                    span,
                    ErrorCode::TypeMismatch,
                    "static actual remains unbound in the concrete instance",
                )
            })
    }

    #[allow(clippy::too_many_arguments)]
    pub(in crate::frontend::compile) fn bind_runtime_source_instance(
        &mut self,
        target: Key,
        actuals: &[StaticActual],
        environment: &StaticEnvironment,
        outer_ops: &operations::Bindings,
        module: &str,
        span: Span,
    ) -> Result<Arc<ClosedInstance>, CompileError> {
        self.bind_runtime_source_instance_partial(
            target,
            actuals,
            environment,
            outer_ops,
            module,
            span,
        )?
        .ok_or_else(|| {
            self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "static actual remains unbound in the concrete runtime instance",
            )
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn bind_resolved_instance<'s>(
        &mut self,
        target: Key,
        actuals: impl ExactSizeIterator<Item = &'s ResolvedStatic>,
        environment: &StaticEnvironment,
        outer_ops: &operations::Bindings,
        module: &str,
        span: Span,
        typed: bool,
    ) -> Result<Option<Arc<ClosedInstance>>, CompileError> {
        self.tick(module, span)?;
        let Some(interface) = self.source.interfaces.get(&target) else {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "specialized provider has no original checked interface",
            ));
        };
        let count = interface.statics.len();
        if count != actuals.len() {
            return Err(self.error(
                module,
                span,
                ErrorCode::Arity,
                "explicit static argument count does not match",
            ));
        }
        // Keep only charged immutable formal keys/kinds needed across recursive
        // provider calls. The original interface remains the final contract.
        self.charge(module, span, count.saturating_mul(2))?;
        let mut bases = BTreeMap::new();
        let mut naturals = BTreeMap::new();
        let mut operations = BTreeMap::new();
        let mut complete = true;
        for (ordinal, actual) in actuals.enumerate() {
            let formal = &self.source.interfaces[&target].statics[ordinal];
            let (category, requested, ceiling) = match formal.kind {
                StaticKind::Basis => (StaticCategory::Basis, [false; 3], None),
                StaticKind::Natural => (StaticCategory::Natural, [false; 3], None),
                StaticKind::Operation {
                    access,
                    ref codomain,
                    ..
                } => (
                    StaticCategory::Operation,
                    access,
                    Some(if codomain.is_some() && !access[1] && !access[2] {
                        Effect::Isometry
                    } else {
                        Effect::Unitary
                    }),
                ),
            };
            // The formal demand is read before any deferral decision (#413).
            let value = if typed && matches!(category, StaticCategory::Basis) {
                self.runtime_basis(actual, environment, module)?
                    .map_or(StaticValue::Deferred, StaticValue::Basis)
            } else {
                self.source_static(
                    actual,
                    environment,
                    category,
                    requested,
                    outer_ops,
                    module,
                    1,
                )?
            };
            let formal = &self.source.interfaces[&target].statics[ordinal];
            self.charge(module, actual.span, formal.key.name.len() + 2)?;
            let key = self.source.interfaces[&target].statics[ordinal].key.clone();
            match value {
                StaticValue::Basis(basis) => {
                    bases.insert(key, basis);
                }
                StaticValue::Natural(number) => {
                    naturals.insert(key, number);
                }
                StaticValue::Operation(operation) => {
                    self.validate_operation_access(&operation, requested, module, actual.span)?;
                    if ceiling.is_some_and(|ceiling| operation.effect > ceiling) {
                        return Err(self.error(module, actual.span, ErrorCode::Effect, "actual provider's source effect exceeds its original operation ceiling"));
                    }
                    let meaning = match self.source.interfaces[&target].statics[ordinal].kind {
                        StaticKind::Operation { meaning, .. } => meaning,
                        _ => None,
                    };
                    if let Some(meaning) = meaning {
                        self.validate_operation_meaning(&operation, meaning, module, actual.span)?;
                    }
                    operations.insert(key, operation);
                }
                StaticValue::Deferred => complete = false,
            }
        }
        self.validate_partial_instance_contracts(
            target,
            &bases,
            &naturals,
            &operations,
            module,
            span,
        )?;
        if !complete {
            return Ok(None);
        }
        self.prepare_instance_with_basis_transport(
            target, bases, naturals, operations, module, span, typed,
        )
        .map(Some)
    }
}
