//! Full-instance body/provider reuse after ordinary original contract checks.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;

impl Compiler<'_> {
    fn accepted_copy_work(instance: &ClosedInstance, body: &AcceptedProgram) -> usize {
        total_size(
            instance
                .interface
                .parameters
                .iter()
                .chain([&instance.interface.result])
                .map(operations::port_nodes),
        )
        .saturating_add(total_size(
            body.output_ports().iter().map(|port| port.wires.len() + 3),
        ))
        .saturating_add(4)
    }

    pub(in crate::frontend::compile) fn materialize_instance(
        &mut self,
        instance: Arc<ClosedInstance>,
        module: &str,
        span: Span,
    ) -> Result<AcceptedProgram, CompileError> {
        if self.effect_in_module(module, instance.definition) != Some(instance.source_effect) {
            return Err(self.error(
                module,
                span,
                ErrorCode::Effect,
                "instance source effect differs from this original caller",
            ));
        }
        self.validate_interface_naturals(instance.definition, &instance.interface, span)?;
        let required = self.required_bindings_closed(&instance.definition, &instance.interface)?;
        self.charge(module, span, instance.operations.len() + required.len() + 1)?;
        if instance.operations.len() != required.len() {
            return Err(self.error(
                module,
                span,
                ErrorCode::Arity,
                "instance operation actuals do not match its original interface",
            ));
        }
        for (formal, operation) in &instance.operations {
            self.charge(
                module,
                span,
                formal.name.len().saturating_mul(required.len() + 1) + 2,
            )?;
            let requirement = required.get(formal).ok_or_else(|| {
                self.error(
                    module,
                    span,
                    ErrorCode::TypeMismatch,
                    "instance has a foreign operation actual",
                )
            })?;
            if operation.effect > instance.interface.operations[formal].ceiling() {
                return Err(self.error(
                    module,
                    span,
                    ErrorCode::Effect,
                    "instance operation exceeds its original source effect ceiling",
                ));
            }
            self.validate_required_operation(requirement, operation, module, span)?;
        }
        self.check_dormant_instance(Arc::clone(&instance), module, span)?;
        if let Some(record) = instance.record {
            match &self.instances[record].body {
                BodyState::Preparing => {
                    return Err(self.error(
                        module,
                        span,
                        ErrorCode::RecursiveCall,
                        "concrete body is already preparing for this complete identity",
                    ));
                }
                BodyState::Ready(body) => {
                    let raw = body.raw();
                    let transport = crate::frontend::raw_state::operations_size(&raw.operations)
                        .saturating_add(raw.classical_inputs.len())
                        .saturating_add(raw.classical_outputs.len())
                        .saturating_add(raw.quantum_outputs.len())
                        .saturating_add(total_size(
                            raw.quantum_inputs.iter().map(|port| port.wires.len() + 3),
                        ));
                    let work = Self::accepted_copy_work(&instance, body).saturating_add(transport);
                    self.charge(module, span, work)?;
                    let BodyState::Ready(body) = &self.instances[record].body else {
                        unreachable!()
                    };
                    // A Ready key does not replace this occurrence's actual
                    // native Raw/body gate, including nested evidence/arms.
                    let checked = self.kernel.check_program(body).map_err(|error| {
                        self.error(
                            module,
                            span,
                            match error.code {
                                "limit" => ErrorCode::Limit,
                                "contract" => ErrorCode::Contract,
                                _ => ErrorCode::InvalidIr,
                            },
                            error.to_string(),
                        )
                    })?;
                    self.exact_work
                        .charge(checked.native_exact_work())
                        .map_err(|error| self.op_error(module, span, error.into()))?;
                    return Ok(body.clone());
                }
                BodyState::Unprepared => {}
            }
            self.instances[record].body = BodyState::Preparing;
        }
        let result = lower::lower_instance_function(self, Arc::clone(&instance));
        if let Some(record) = instance.record {
            match &result {
                Ok(body) => {
                    let charge =
                        self.charge(module, span, Self::accepted_copy_work(&instance, body));
                    if let Err(error) = charge {
                        self.instances[record].body = BodyState::Unprepared;
                        return Err(error);
                    }
                    self.instances[record].body = BodyState::Ready(body.clone());
                }
                Err(_) => self.instances[record].body = BodyState::Unprepared,
            }
        }
        result
    }

    pub(in crate::frontend::compile) fn provider_instance(
        &mut self,
        instance: Arc<ClosedInstance>,
        meaning: Option<Key>,
        module: &str,
        span: Span,
    ) -> Result<operations::Operation, CompileError> {
        if instance.source_effect > Effect::Isometry
            || self.effect_in_module(module, instance.definition) != Some(instance.source_effect)
        {
            return Err(self.error(
                module,
                span,
                ErrorCode::Effect,
                "provider's caller-visible source effect must be at most Isometry",
            ));
        }
        let [input] = instance.interface.parameters.as_slice() else {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "provider requires one quantum input and output",
            ));
        };
        let (Some(basis), Some(codomain)) = (
            input.quantum_basis(),
            instance.interface.result.quantum_basis(),
        ) else {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "provider requires exact Q<A> -> Q<B> ports",
            ));
        };
        if let Some(meaning) = meaning {
            let expected = &self.meanings[&meaning];
            let cost = operations::port_nodes(&expected.basis)
                + operations::port_nodes(&expected.codomain)
                + operations::port_nodes(basis)
                + operations::port_nodes(codomain);
            self.charge(module, span, cost)?;
            let expected = &self.meanings[&meaning];
            if expected.basis != *basis || expected.codomain != *codomain {
                return Err(self.error(
                    module,
                    span,
                    ErrorCode::TypeMismatch,
                    "provider and Meaning have different exact ports",
                ));
            }
        }
        // Even a warm provider lookup first traverses the full ordinary actual
        // contract/body gate; its Ready body remains tied to the complete key.
        let body = self.materialize_instance(Arc::clone(&instance), module, span)?;
        let closed_provider = if instance.record.is_none() {
            self.charge(module, span, 5)?;
            if !self.source.interfaces[&instance.definition]
                .statics
                .is_empty()
                || !instance.interface.bases.is_empty()
                || !instance.interface.naturals.is_empty()
                || !instance.operations.is_empty()
            {
                return Err(self.error(
                    module,
                    span,
                    ErrorCode::TypeMismatch,
                    "nongeneric provider cache requires the original empty substitution",
                ));
            }
            Some((instance.definition, meaning, instance.source_effect))
        } else {
            None
        };
        if let Some(cache) = closed_provider {
            self.charge(module, span, self.providers.len() + 1)?;
            if let Some(cached) = self.providers.get(&cache) {
                // The original definition in this immutable source collection
                // binds the source. Fresh native decoding issues fresh receipt
                // identities, so compare the complete canonical accepted Raw
                // graph and retained dependency source bytes before reuse.
                let cost = cached
                    .body
                    .artifact()
                    .len()
                    .saturating_add(body.artifact().len())
                    .saturating_add(cached.operation.copy_size())
                    .saturating_add(1);
                self.charge(module, span, cost)?;
                let cached = &self.providers[&cache];
                if cached.body.artifact() != body.artifact() {
                    return Err(self.error(
                        module,
                        span,
                        ErrorCode::Contract,
                        "cached provider has a different freshly checked Raw/source graph",
                    ));
                }
                return Ok(cached.operation.clone());
            }
        }
        if let Some(record) = instance.record {
            self.charge(module, span, self.instances[record].providers.len() + 1)?;
            let mut found = None;
            for (ordinal, (requested, _)) in self.instances[record].providers.iter().enumerate() {
                if *requested == meaning {
                    found = Some(ordinal);
                    break;
                }
            }
            if let Some(ordinal) = found {
                let cost = self.instances[record].providers[ordinal].1.copy_size();
                self.charge(module, span, cost)?;
                return Ok(self.instances[record].providers[ordinal].1.clone());
            }
        }
        self.charge(
            module,
            span,
            operations::port_nodes(basis) + operations::port_nodes(codomain),
        )?;
        let mut operation = self.provider_program(
            module,
            span,
            instance.definition,
            meaning,
            instance.source_effect,
            basis.clone(),
            codomain.clone(),
            &body,
            &instance.operations,
        )?;
        self.charge(module, span, instance.operations.len().saturating_mul(3))?;
        let reverse = instance
            .operations
            .values()
            .all(|operation| operation.access[0] && operation.access[1]);
        let control = instance
            .operations
            .values()
            .all(|operation| operation.access.iter().all(|access| *access));
        operation.access[1] &= reverse;
        operation.access[2] &= reverse && control;
        if let Some(record) = instance.record {
            let providers = &self.instances[record].providers;
            let growth = if providers.len() == providers.capacity() {
                providers.len() + 1
            } else {
                0
            };
            self.charge(module, span, growth + operation.copy_size() + 1)?;
            if growth != 0 {
                self.instances[record].providers.reserve_exact(1);
            }
            self.instances[record]
                .providers
                .push((meaning, operation.clone()));
        } else if let Some(cache) = closed_provider {
            self.charge(module, span, operation.copy_size() + 1)?;
            self.providers.insert(
                cache,
                operations::CachedProvider {
                    operation: operation.clone(),
                    body,
                },
            );
        }
        Ok(operation)
    }
}
