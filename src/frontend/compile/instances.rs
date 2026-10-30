//! Complete original closed substitutions and private specialization identity.
//!
//! Reuse follows source/actual checks; neither this registry nor its state is
//! semantic evidence. Only the ordinary native gates accept a produced body.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.

use super::*;
use crate::frontend::check::plans::{ResolvedNatural, ResolvedReference, StaticEnvironment};
use crate::ir::Effect;

mod bindings;
mod closure;
mod contracts;
mod provider;
mod runtime_basis;
#[cfg(test)]
mod tests;

pub(super) enum StaticValue {
    Basis(Ty),
    Natural(u32),
    Operation(operations::Operation),
    Deferred,
}

pub(super) enum Argument {
    Basis(Ty),
    Natural(u32),
    Operation(operations::Operation),
}
pub(super) struct Identity {
    pub definition: Key,
    pub arguments: Vec<Argument>,
    pub source_effect: Effect,
}
pub(super) enum BodyState {
    Unprepared,
    Preparing,
    Ready(AcceptedProgram),
}
pub(super) struct Record {
    identity: Identity,
    pub body: BodyState,
    pub providers: Vec<(Option<Key>, operations::Operation)>,
}
pub(super) struct ClosedInstance {
    pub definition: Key,
    pub interface: super::super::closed::ClosedInterface,
    pub operations: operations::Bindings,
    pub source_effect: Effect,
    pub record: Option<usize>,
}
#[derive(Default)]
pub(super) struct Context {
    pub owner: Option<Key>,
    pub current: Option<Arc<ClosedInstance>>,
    pub naturals: BTreeMap<BinderKey, u32>,
    active: Vec<usize>,
    depth: usize,
    conditional_naturals: bool,
}
pub(super) struct Frame {
    checking: Option<Key>,
    owner: Option<Key>,
    current: Option<Arc<ClosedInstance>>,
    naturals: BTreeMap<BinderKey, u32>,
    record: Option<usize>,
    depth: usize,
    conditional_naturals: bool,
}
pub(super) struct NaturalFrame {
    key: BinderKey,
    previous: Option<u32>,
}

impl Identity {
    fn same(
        &self,
        other: &Self,
        charge: &mut impl FnMut(usize) -> Result<(), CompileError>,
    ) -> Result<bool, CompileError> {
        charge(3)?;
        if self.definition != other.definition
            || self.source_effect != other.source_effect
            || self.arguments.len() != other.arguments.len()
        {
            return Ok(false);
        }
        for (left, right) in self.arguments.iter().zip(&other.arguments) {
            charge(1)?;
            let same = match (left, right) {
                (Argument::Basis(left), Argument::Basis(right)) => {
                    operations::same_port_budgeted(left, right, charge)?
                }
                (Argument::Natural(left), Argument::Natural(right)) => left == right,
                (Argument::Operation(left), Argument::Operation(right)) => {
                    left.same_descriptor_budgeted(right, charge)?
                }
                _ => false,
            };
            if !same {
                return Ok(false);
            }
        }
        Ok(true)
    }
}

impl Compiler<'_> {
    pub(super) fn record_instance_identity(
        &mut self,
        identity: Identity,
        module: &str,
        span: Span,
    ) -> Result<usize, CompileError> {
        let mut work = self.work;
        let found = (|| {
            for (ordinal, record) in self.instances.iter().enumerate() {
                if record.identity.same(&identity, &mut |cells| {
                    self.charge_at(&mut work, module, span, cells)
                })? {
                    return Ok(Some(ordinal));
                }
            }
            Ok::<_, CompileError>(None)
        })();
        self.work = work;
        if let Some(ordinal) = found? {
            return Ok(ordinal);
        }
        if self.instances.len() >= 256 {
            return Err(self.error(
                module,
                span,
                ErrorCode::Limit,
                "project exceeds 256 distinct operation specializations",
            ));
        }
        if self.instances.len() == self.instances.capacity() {
            self.charge(module, span, self.instances.len().saturating_add(1))?;
            self.instances.reserve_exact(1);
        }
        self.charge(module, span, 1)?;
        let ordinal = self.instances.len();
        self.instances.push(Record {
            identity,
            body: BodyState::Unprepared,
            providers: Vec::new(),
        });
        Ok(ordinal)
    }

    pub(super) fn prepare_instance(
        &mut self,
        definition: Key,
        bases: BTreeMap<BinderKey, Ty>,
        naturals: BTreeMap<BinderKey, u32>,
        operations: operations::Bindings,
        module: &str,
        span: Span,
    ) -> Result<Arc<ClosedInstance>, CompileError> {
        self.prepare_instance_with_basis_transport(
            definition, bases, naturals, operations, module, span, false,
        )
    }

    pub(super) fn prepare_runtime_instance(
        &mut self,
        definition: Key,
        bases: BTreeMap<BinderKey, Ty>,
        naturals: BTreeMap<BinderKey, u32>,
        operations: operations::Bindings,
        module: &str,
        span: Span,
    ) -> Result<Arc<ClosedInstance>, CompileError> {
        let typed = self.source.interfaces[&definition]
            .statics
            .iter()
            .all(|formal| !matches!(formal.kind, StaticKind::Operation { .. }));
        self.prepare_instance_with_basis_transport(
            definition, bases, naturals, operations, module, span, typed,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn prepare_instance_with_basis_transport(
        &mut self,
        definition: Key,
        bases: BTreeMap<BinderKey, Ty>,
        naturals: BTreeMap<BinderKey, u32>,
        operations: operations::Bindings,
        module: &str,
        span: Span,
        typed: bool,
    ) -> Result<Arc<ClosedInstance>, CompileError> {
        let source_effect = self.effect_in_module(module, definition).ok_or_else(|| {
            self.error(
                module,
                span,
                ErrorCode::Effect,
                "callee has no available source effect",
            )
        })?;
        // The shared closer checks every Basis actual, including unused ones.
        let closed = self.close_instance_interface(definition, bases, naturals, span, typed)?;
        let required = self.required_bindings_closed(&definition, &closed)?;
        self.charge(
            module,
            span,
            operations.len().saturating_add(required.len()),
        )?;
        if operations.len() != required.len() {
            return Err(self.error(
                module,
                span,
                ErrorCode::Arity,
                "closed operation bindings do not match the declaration",
            ));
        }
        for (key, operation) in &operations {
            self.charge(
                module,
                span,
                key.name.len().saturating_mul(required.len() + 1),
            )?;
            let Some(required) = required.get(key) else {
                return Err(self.error(
                    module,
                    span,
                    ErrorCode::TypeMismatch,
                    "foreign closed operation binding",
                ));
            };
            if operation.effect > closed.operations[key].ceiling() {
                return Err(self.error(
                    module,
                    span,
                    ErrorCode::Effect,
                    "actual provider's source effect exceeds its original operation ceiling",
                ));
            }
            self.validate_required_operation(required, operation, module, span)?;
        }
        let interface = &self.source.interfaces[&definition];
        let mut work = self.work;
        let identity = (|| {
            self.charge_at(&mut work, module, span, interface.statics.len())?;
            let mut arguments = Vec::with_capacity(interface.statics.len());
            for formal in &interface.statics {
                self.charge_at(&mut work, module, span, formal.key.name.len() + 1)?;
                arguments.push(match &formal.kind {
                    StaticKind::Basis => {
                        let basis = &closed.bases[&formal.key];
                        self.charge_at(&mut work, module, span, operations::port_nodes(basis))?;
                        Argument::Basis(basis.clone())
                    }
                    StaticKind::Natural => Argument::Natural(closed.naturals[&formal.key]),
                    StaticKind::Operation { .. } => {
                        let operation = &operations[&formal.key];
                        self.charge_at(&mut work, module, span, operation.copy_size())?;
                        Argument::Operation(operation.clone())
                    }
                });
            }
            Ok::<_, CompileError>(Identity {
                definition,
                arguments,
                source_effect,
            })
        })();
        self.work = work;
        let identity = identity?;
        let record = if identity.arguments.is_empty() {
            None
        } else {
            Some(self.record_instance_identity(identity, module, span)?)
        };
        self.charge(module, span, 1)?;
        Ok(Arc::new(ClosedInstance {
            definition,
            interface: closed,
            operations,
            source_effect,
            record,
        }))
    }

    pub(super) fn current_instance_owner(&self) -> Option<Key> {
        self.concrete_context.owner
    }

    pub(super) fn in_inactive_region(&self) -> bool {
        self.concrete_context.conditional_naturals
    }

    pub(super) fn instance_is_active(
        &mut self,
        instance: &ClosedInstance,
        module: &str,
        span: Span,
    ) -> Result<bool, CompileError> {
        self.charge(module, span, self.concrete_context.active.len() + 1)?;
        Ok(instance
            .record
            .is_some_and(|record| self.concrete_context.active.contains(&record)))
    }

    pub(super) fn enter_instance(
        &mut self,
        instance: Arc<ClosedInstance>,
        module: &str,
        span: Span,
    ) -> Result<Frame, CompileError> {
        self.charge(module, span, self.concrete_context.active.len() + 2)?;
        if self.concrete_context.depth >= MAX_DEPTH {
            return Err(self.error(
                module,
                span,
                ErrorCode::Limit,
                "concrete instance expansion exceeds depth 64",
            ));
        }
        if let Some(record) = instance.record {
            if self.concrete_context.active.contains(&record) {
                return Err(self.error(
                    module,
                    span,
                    ErrorCode::RecursiveCall,
                    "active concrete specialization repeats its complete identity",
                ));
            }
        }
        for key in instance.interface.naturals.keys() {
            self.charge(module, span, key.name.len() + 2)?;
        }
        let naturals = instance.interface.naturals.clone();
        if let Some(record) = instance.record {
            if self.concrete_context.active.len() == self.concrete_context.active.capacity() {
                self.charge(module, span, self.concrete_context.active.len() + 1)?;
                self.concrete_context.active.reserve_exact(1);
            }
            self.concrete_context.active.push(record);
        }
        let depth = self.concrete_context.depth;
        self.concrete_context.depth += 1;
        Ok(Frame {
            depth,
            conditional_naturals: std::mem::replace(
                &mut self.concrete_context.conditional_naturals,
                false,
            ),
            record: instance.record,
            checking: self.checking.replace(instance.definition),
            owner: self.concrete_context.owner.replace(instance.definition),
            current: self.concrete_context.current.replace(instance),
            naturals: std::mem::replace(&mut self.concrete_context.naturals, naturals),
        })
    }

    pub(super) fn leave_instance(&mut self, frame: Frame) {
        self.concrete_context.depth = frame.depth;
        self.concrete_context.conditional_naturals = frame.conditional_naturals;
        if let Some(record) = frame.record {
            assert_eq!(self.concrete_context.active.pop(), Some(record));
        }
        self.concrete_context.current = frame.current;
        self.checking = frame.checking;
        self.concrete_context.owner = frame.owner;
        self.concrete_context.naturals = frame.naturals;
    }

    pub(super) fn enter_dormant_owner(
        &mut self,
        owner: Key,
        module: &str,
        span: Span,
    ) -> Result<Frame, CompileError> {
        self.charge(module, span, 3)?;
        if self
            .source
            .resolution
            .try_declaration(owner)
            .is_none_or(|declaration| {
                self.source.resolution.module(module) != Some(declaration.module)
            })
        {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "dormant context lacks its original source owner",
            ));
        }
        Ok(Frame {
            depth: self.concrete_context.depth,
            conditional_naturals: std::mem::replace(
                &mut self.concrete_context.conditional_naturals,
                false,
            ),
            checking: self.checking.replace(owner),
            owner: self.concrete_context.owner.replace(owner),
            current: self.concrete_context.current.take(),
            naturals: std::mem::take(&mut self.concrete_context.naturals),
            record: None,
        })
    }

    /// Inactive source regions keep known actual owners/Bases/Ops. Only the
    /// original formal-dependent Nat replay becomes conditional; normalized
    /// owner types may still use their globally valid actual sizes.
    pub(super) fn enter_inactive_region(
        &mut self,
        owner: Key,
        module: &str,
        span: Span,
    ) -> Result<Frame, CompileError> {
        self.charge(module, span, module.len() + 3)?;
        if self.current_instance_owner() != Some(owner) {
            let frame = self.enter_dormant_owner(owner, module, span)?;
            self.concrete_context.conditional_naturals = true;
            return Ok(frame);
        }
        if self
            .source
            .resolution
            .try_declaration(owner)
            .is_none_or(|declaration| declaration.name.0 != module)
        {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "inactive region differs from its original source module",
            ));
        }
        self.charge(module, span, self.concrete_context.naturals.len() + 2)?;
        for key in self.concrete_context.naturals.keys() {
            let mut work = self.work;
            let result = self.charge_at(&mut work, module, span, key.name.len() + 2);
            self.work = work;
            result?;
        }
        let frame = Frame {
            checking: self.checking,
            owner: self.concrete_context.owner,
            current: self.concrete_context.current.clone(),
            naturals: self.concrete_context.naturals.clone(),
            record: None,
            depth: self.concrete_context.depth,
            conditional_naturals: self.concrete_context.conditional_naturals,
        };
        self.concrete_context.conditional_naturals = true;
        Ok(frame)
    }

    pub(super) fn push_natural_binding(
        &mut self,
        key: &BinderKey,
        value: u32,
        span: Span,
    ) -> Result<NaturalFrame, CompileError> {
        let owner = self.current_instance_owner().ok_or_else(|| {
            self.error(
                "main",
                span,
                ErrorCode::TypeMismatch,
                "natural binding has no active original instance",
            )
        })?;
        let module = self.dormant_module(owner, span)?;
        self.charge(
            &module,
            span,
            key.name.len().saturating_mul(2).saturating_add(3),
        )?;
        if key.id.definition() != owner
            || self.source.lexical[&owner]
                .try_binder(key.id)
                .is_none_or(|binding| {
                    binding.kind != super::super::resolve::locals::BindingKind::FoldIndex
                        || binding.key != *key
                })
        {
            return Err(self.error(
                &module,
                span,
                ErrorCode::TypeMismatch,
                "natural binding belongs to another original instance",
            ));
        }
        Ok(NaturalFrame {
            key: key.clone(),
            previous: self.concrete_context.naturals.insert(key.clone(), value),
        })
    }

    pub(super) fn restore_natural_binding(&mut self, frame: NaturalFrame) {
        match frame.previous {
            Some(value) => {
                self.concrete_context.naturals.insert(frame.key, value);
            }
            None => {
                self.concrete_context.naturals.remove(&frame.key);
            }
        }
    }

    pub(super) fn evaluate_plan_natural(
        &mut self,
        value: &ResolvedNatural,
        environment: &StaticEnvironment,
    ) -> Result<u32, CompileError> {
        let result = self.evaluate_plan_natural_partial(value, environment)?;
        self.require_closed_natural(result, environment, value.span)
    }

    pub(super) fn evaluate_plan_natural_partial(
        &mut self,
        value: &ResolvedNatural,
        environment: &StaticEnvironment,
    ) -> Result<Option<u32>, CompileError> {
        self.evaluate_natural_with(environment, value.span, |values, charge, call, error| {
            naturals::evaluate(
                value,
                environment,
                values,
                &mut |span, cells| charge(span, cells),
                &mut |span| call(span),
                &|span, code, message| error(span, code, message),
            )
        })
    }

    pub(super) fn evaluate_plan_reference(
        &mut self,
        reference: &ResolvedReference,
        span: Span,
        environment: &StaticEnvironment,
    ) -> Result<u32, CompileError> {
        let result = self.evaluate_plan_reference_partial(reference, span, environment)?;
        self.require_closed_natural(result, environment, span)
    }

    pub(super) fn evaluate_plan_reference_partial(
        &mut self,
        reference: &ResolvedReference,
        span: Span,
        environment: &StaticEnvironment,
    ) -> Result<Option<u32>, CompileError> {
        self.evaluate_natural_with(environment, span, |values, charge, call, error| {
            naturals::evaluate_reference(
                reference,
                span,
                environment,
                values,
                &mut |span, cells| charge(span, cells),
                &mut |span| call(span),
                &|span, code, message| error(span, code, message),
            )
        })
    }

    fn require_closed_natural(
        &self,
        value: Option<u32>,
        environment: &StaticEnvironment,
        span: Span,
    ) -> Result<u32, CompileError> {
        value.ok_or_else(|| {
            self.error(
                &self.source.resolution.declaration(environment.owner).name.0,
                span,
                ErrorCode::TypeMismatch,
                "original natural remains unbound in the concrete instance",
            )
        })
    }

    fn evaluate_natural_with(
        &mut self,
        environment: &StaticEnvironment,
        span: Span,
        evaluate: impl FnOnce(
            &BTreeMap<BinderKey, u32>,
            &mut dyn FnMut(Span, usize) -> Result<(), CompileError>,
            &mut dyn FnMut(Span) -> Result<(), CompileError>,
            &dyn Fn(Span, ErrorCode, &'static str) -> CompileError,
        ) -> Result<naturals::NaturalValue, CompileError>,
    ) -> Result<Option<u32>, CompileError> {
        let module = self.dormant_module(environment.owner, span)?;
        self.tick(&module, span)?;
        if self.current_instance_owner() != Some(environment.owner)
            || self.source.resolution.module(&module) != Some(environment.module)
        {
            return Err(self.error(
                &module,
                span,
                ErrorCode::TypeMismatch,
                "natural plan differs from its active original instance",
            ));
        }
        let work = std::cell::Cell::new(self.work);
        let charge = |span, cells| {
            let mut used = work.get();
            let result = self.charge_at(&mut used, &module, span, cells);
            work.set(used);
            result
        };
        let deferred_values = BTreeMap::new();
        let values = if self.concrete_context.conditional_naturals {
            &deferred_values
        } else {
            &self.concrete_context.naturals
        };
        let result = evaluate(
            values,
            &mut |span, cells| charge(span, cells),
            &mut |span| charge(span, 1),
            &|span, code, message| self.error(&module, span, code, message),
        );
        self.work = work.get();
        match result? {
            naturals::NaturalValue::Closed(value) => Ok(Some(value)),
            naturals::NaturalValue::Deferred => Ok(None),
        }
    }

    pub(super) fn close_body_type(
        &mut self,
        owner: Key,
        checked: &check::Ty,
        span: Span,
    ) -> Result<Ty, CompileError> {
        let module = self.dormant_module(owner, span)?;
        let Some(instance) = self.concrete_context.current.as_ref() else {
            return Err(self.error(
                &module,
                span,
                ErrorCode::TypeMismatch,
                "body type lacks its active original instance",
            ));
        };
        if instance.definition != owner {
            return Err(self.error(
                &module,
                span,
                ErrorCode::TypeMismatch,
                "body type belongs to another original instance",
            ));
        }
        let mut work = self.work;
        let mut charge_error = None;
        let closed = check::close_type_budgeted(
            checked,
            &self.concrete_context.naturals,
            &instance.interface.bases,
            span,
            &mut |span, cells| {
                self.charge_at(&mut work, &module, span, cells)
                    .map_err(|error| {
                        charge_error = Some(error);
                        SourceError::new("limit", span, "closed body type work limit")
                    })
            },
        );
        self.work = work;
        if let Some(error) = charge_error {
            return Err(error);
        }
        let closed = closed.map_err(|error| self.originals.error(error.in_module(&module)))?;
        let mut work = self.work;
        let result = types::finite_body_type(self, &mut work, &module, span, &closed);
        self.work = work;
        result
    }
}
