//! Explicit function-contract applications retain independently checked evidence.

use super::super::operations::contract_basis;
use super::*;
use crate::contract::instrument::InstrumentEvidence;
use crate::contract::{FunctionEvidence, MAX_CONTRACT_BITS, function::RetainedIdentity};
use crate::frontend::raw_state::operations_size;
use std::sync::Arc;

impl Lowerer<'_, '_> {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn apply_function_contract(
        &mut self,
        module: &str,
        span: Span,
        implementation: &Ident,
        specification: &Ident,
        input: Value,
        env: &Env,
    ) -> Result<Value, CompileError> {
        if let Callee::User(key) = self.compiler.resolve(module, implementation)? {
            if self.compiler.effect_in_module(module, key) == Some(Effect::Observe) {
                return self.apply_instrument_contract(
                    module,
                    span,
                    implementation,
                    specification,
                    input,
                    env,
                );
            }
        }
        let slot = self.quantum(module, span, &input, false)?;
        self.compiler
            .charge(module, span, self.raw.registers[&slot].size())?;
        let basis = self.raw.registers[&slot].basis.clone();
        let bits = self.circuit_width(module, span, &basis)?;
        if bits > MAX_CONTRACT_BITS {
            return Err(self.error(
                module,
                span,
                ErrorCode::Limit,
                format!("function contracts support at most {MAX_CONTRACT_BITS} interface bits"),
            ));
        }
        let implementation_key = self.contract_function(module, implementation, &basis, env)?;
        let declared_meaning = self.compiler.meaning_key(module, specification).ok();
        let specification_key =
            if let Some(key) = declared_meaning {
                if self
                    .compiler
                    .locals()
                    .local_key(specification)
                    .is_some_and(|key| env.contains_key(key))
                    || self.bound_operation(specification).is_some()
                {
                    return Err(self.error(module, specification.span, ErrorCode::TypeMismatch,
                    "apply_contract requires global specification declarations, not local values"));
                }
                if self.compiler.meanings[&key].basis != basis {
                    return Err(self.error(
                        module,
                        specification.span,
                        ErrorCode::TypeMismatch,
                        "contract implementation and Meaning basis trees differ",
                    ));
                }
                key
            } else {
                self.contract_function(module, specification, &basis, env)?
            };
        let evidence = self.compiler.function_contract_evidence(
            module,
            span,
            implementation_key,
            specification_key,
        )?;
        self.apply_circuit(
            slot,
            vec![CircuitStep {
                controls: vec![],
                action: CircuitAction::Contract {
                    indices: (0..bits).collect(),
                    evidence,
                    adjoint: false,
                },
            }],
        );
        Ok(input)
    }

    fn apply_instrument_contract(
        &mut self,
        module: &str,
        span: Span,
        implementation: &Ident,
        specification: &Ident,
        input: Value,
        env: &Env,
    ) -> Result<Value, CompileError> {
        let mut keys = Vec::new();
        for name in [implementation, specification] {
            if self
                .compiler
                .locals()
                .local_key(name)
                .is_some_and(|key| env.contains_key(key))
                || self.bound_operation(name).is_some()
            {
                return Err(self.error(
                    module,
                    name.span,
                    ErrorCode::TypeMismatch,
                    "apply_contract requires global ordinary function names, not local values",
                ));
            }
            let Callee::User(key) = self.compiler.resolve(module, name)? else {
                return Err(self.error(
                    module,
                    name.span,
                    ErrorCode::TypeMismatch,
                    "observing contracts require ordinary function names",
                ));
            };
            keys.push(key);
        }
        let slot = self.quantum(module, span, &input, false)?;
        self.compiler
            .charge(module, span, self.raw.registers[&slot].size())?;
        let register = &self.raw.registers[&slot];
        let port = QuantumPort {
            token: register.token,
            wires: register.wires.clone(),
            shape: BasisShape {
                bits: register.wires.len() as u8,
            },
        };
        let (parameters, result_type) = self.compiler.signature(&keys[0])?;
        if parameters != [input.ty()] {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "observing contract input changes the complete quantum basis tree",
            ));
        }
        let signature = crate::frontend::instrument::signature(
            &parameters,
            &result_type,
            |size| Some(*size),
            &mut self.compiler.exact_work,
        )
        .map_err(|error| self.compiler.instrument_error(module, span, error))?;
        let evidence = self
            .compiler
            .instrument_contract_evidence(module, span, keys[0], keys[1])?;
        let actual_effect = self.compiler.checked[&keys[0]].raw().declared_effect;
        let first = self.raw.operations.len();
        // Ordinary inlining consumes the live input once and executes only the
        // implementation. The independently selected reference is not called.
        let result = self.call_user(&keys[0], vec![input], None)?;
        // The source contract remains Observe even when the independently
        // checked concrete implementation emits a pure instrument.
        self.add_contract_effect(module, span, Effect::Observe);
        if result.ty() != result_type {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "observing contract result changes its complete declared type",
            ));
        }
        self.compiler.charge(
            module,
            span,
            operations_size(&self.raw.operations[first..])
                + result.tree_size().nodes.saturating_mul(2)
                + module.len()
                + 3,
        )?;
        let mut quantum_outputs = Vec::new();
        let mut classical_outputs = Vec::new();
        result.outputs(
            &self.raw.registers,
            &mut quantum_outputs,
            &mut classical_outputs,
        );
        let call = RawProgram {
            quantum_inputs: vec![port],
            classical_inputs: vec![],
            operations: self.raw.operations[first..].to_vec(),
            quantum_outputs,
            classical_outputs,
            declared_effect: actual_effect,
        };
        let checked = evidence
            .check_call(
                &self.compiler.kernel,
                &signature,
                &call,
                (module.into(), span.start, span.end),
                &mut self.compiler.exact_work,
            )
            .map_err(|error| self.compiler.instrument_error(module, span, error))?;
        self.instrument_calls.push(checked);
        Ok(result)
    }

    fn contract_function(
        &mut self,
        module: &str,
        name: &Ident,
        basis: &Ty,
        env: &Env,
    ) -> Result<Key, CompileError> {
        if self
            .compiler
            .locals()
            .local_key(name)
            .is_some_and(|key| env.contains_key(key))
            || self.bound_operation(name).is_some()
        {
            return Err(self.error(
                module,
                name.span,
                ErrorCode::TypeMismatch,
                "apply_contract requires function names, not local values",
            ));
        }
        let Callee::User(key) = self.compiler.resolve(module, name)? else {
            return Err(self.error(
                module,
                name.span,
                ErrorCode::TypeMismatch,
                "apply_contract requires ordinary functions with inferred Unitary body effects",
            ));
        };
        if self.compiler.effect_in_module(module, key) != Some(Effect::Unitary) {
            return Err(self.error(
                module,
                name.span,
                ErrorCode::Effect,
                crate::frontend::effects::unitary_required(
                    "apply_contract requires available Unitary source effects",
                ),
            ));
        }
        if !self.compiler.declarations[&key].static_params.is_empty() {
            return Err(self.error(
                module,
                name.span,
                ErrorCode::Arity,
                "contract functions must be closed",
            ));
        }
        let expected = Ty::quantum(basis.clone());
        let (params, result) = self.compiler.signature(&key)?;
        if params != [expected.clone()] || result != expected {
            return Err(self.error(
                module,
                name.span,
                ErrorCode::TypeMismatch,
                "contract functions require one Q<A> input and the same exact Q<A> output",
            ));
        }
        Ok(key)
    }
}

impl Compiler<'_> {
    pub(in crate::frontend::compile) fn instrument_error(
        &self,
        module: &str,
        span: Span,
        error: crate::contract::ContractError,
    ) -> CompileError {
        self.error(
            module,
            span,
            if error.is_capacity() {
                ErrorCode::Limit
            } else if matches!(
                error,
                crate::contract::ContractError::InvalidCircuit(_)
                    | crate::contract::ContractError::EvidenceMismatch
            ) {
                ErrorCode::InvalidIr
            } else {
                ErrorCode::Contract
            },
            format!("observing function semantic contract: {error}"),
        )
    }

    pub(in crate::frontend::compile) fn instrument_contract_evidence(
        &mut self,
        module: &str,
        span: Span,
        implementation: Key,
        specification: Key,
    ) -> Result<Arc<InstrumentEvidence>, CompileError> {
        for key in [implementation, specification] {
            if matches!(
                self.declarations[&key].kind,
                FnKind::Classical | FnKind::Meaning
            ) || !self.declarations[&key].static_params.is_empty()
                || self.effect_in_module(module, key) != Some(Effect::Observe)
            {
                return Err(self.error(module, span, ErrorCode::Effect,
                    "observing contracts require two closed ordinary functions with available Observe source effects"));
            }
            let actual = self.checked.get(&key).ok_or_else(|| {
                self.error(
                    module,
                    span,
                    ErrorCode::InvalidIr,
                    "instrument dependency has not been independently checked",
                )
            })?;
            if actual.raw().declared_effect != Effect::Observe {
                return Err(self.error(
                    module,
                    span,
                    ErrorCode::Unsupported,
                    "observing function contracts require actual Observe Raw artifacts; a broader public effect cannot replace the implementation classification",
                ));
            }
        }
        let (parameters, result) = self.signature(&implementation)?;
        let (expected_parameters, expected_result) = self.signature(&specification)?;
        if parameters != expected_parameters || result != expected_result {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "observing contract functions must have the same complete input/result types",
            ));
        }
        let signature = crate::frontend::instrument::signature(
            &parameters,
            &result,
            |size| Some(*size),
            &mut self.exact_work,
        )
        .map_err(|error| self.instrument_error(module, span, error))?;
        let expected_signature = crate::frontend::instrument::signature(
            &expected_parameters,
            &expected_result,
            |size| Some(*size),
            &mut self.exact_work,
        )
        .map_err(|error| self.instrument_error(module, span, error))?;
        // Call checking binds the literal caller span as well as both bodies.
        self.charge(module, span, 1)?;
        let instance = self.concrete_context.current.clone();
        let caller = self
            .current_instance_owner()
            .or(self.checking)
            .ok_or_else(|| {
                self.error(
                    module,
                    span,
                    ErrorCode::InvalidIr,
                    "instrument contract lacks its original caller definition",
                )
            })?;
        if self.source.resolution.declaration(caller).name.0 != module {
            return Err(self.error(
                module,
                span,
                ErrorCode::InvalidIr,
                "instrument contract caller module differs from its original definition",
            ));
        }
        let key = (
            implementation,
            specification,
            caller,
            instance.as_ref().and_then(|instance| instance.record),
        );
        if let Some(evidence) = self.instrument_evidence.get(&key) {
            // Immutable selected source preparation only. Every emitted call
            // below still obtains its own fresh original-artifact decision.
            return Ok(Arc::clone(evidence));
        }
        let empty = super::super::operations::Bindings::new();
        let bindings = instance
            .as_ref()
            .map_or(&empty, |instance| &instance.operations);
        let sources = self.retained_sources(
            module,
            span,
            &[implementation, specification, caller],
            bindings,
            &[],
        )?;
        let identity = RetainedIdentity::interned(
            self.source.resolution.path(implementation),
            self.source.resolution.path(specification),
            sources,
        );
        let implementation = self.checked.get(&implementation).ok_or_else(|| {
            self.error(
                module,
                span,
                ErrorCode::InvalidIr,
                "instrument implementation has not been independently checked",
            )
        })?;
        let specification = self.checked.get(&specification).ok_or_else(|| {
            self.error(
                module,
                span,
                ErrorCode::InvalidIr,
                "instrument specification has not been independently checked",
            )
        })?;
        let evidence = Arc::new(
            InstrumentEvidence::check(
                &self.kernel,
                signature,
                expected_signature,
                implementation,
                specification,
                identity,
                &mut self.exact_work,
            )
            .map_err(|error| self.instrument_error(module, span, error))?,
        );
        self.instrument_evidence.insert(key, Arc::clone(&evidence));
        Ok(evidence)
    }

    pub(in crate::frontend::compile) fn function_contract_evidence(
        &mut self,
        module: &str,
        span: Span,
        implementation_key: Key,
        specification_key: Key,
    ) -> Result<Arc<FunctionEvidence>, CompileError> {
        let (params, result) = self.signature(&implementation_key)?;
        let Kind::Q(basis) = &result.kind else {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "contract function requires Q<A> output",
            ));
        };
        if params != [result.clone()]
            || !self.declarations[&implementation_key]
                .static_params
                .is_empty()
            || self.effect_in_module(module, implementation_key) != Some(Effect::Unitary)
        {
            return Err(self.error(module, span, ErrorCode::TypeMismatch, "contract implementation must be a closed exact quantum endomorphism with an available Unitary source effect"));
        }
        let declared_meaning = self
            .meanings
            .contains_key(&specification_key)
            .then_some(specification_key);
        if let Some(key) = declared_meaning {
            if self.meanings[&key].basis != **basis {
                return Err(self.error(
                    module,
                    span,
                    ErrorCode::TypeMismatch,
                    "contract implementation and Meaning basis trees differ",
                ));
            }
        } else {
            let (specified_params, specified_result) = self.signature(&specification_key)?;
            if specified_params != params
                || specified_result != result
                || !self.declarations[&specification_key]
                    .static_params
                    .is_empty()
                || self.effect_in_module(module, specification_key) != Some(Effect::Unitary)
            {
                return Err(self.error(module, span, ErrorCode::TypeMismatch, "contract specification must have the same closed exact quantum interface with an available Unitary source effect"));
            }
        }
        let cache_key = (implementation_key, specification_key);
        let evidence = if let Some(evidence) = self.function_evidence.get(&cache_key) {
            // Only this compiler populates the cache, using the exact resolved
            // keys and independently checked raw functions below. The loaded
            // project and those dependencies cannot change during compilation.
            // Reuse therefore needs neither a digest nor repeated source/raw
            // comparisons. External evidence still uses check_binding.
            Arc::clone(evidence)
        } else {
            let implementation_name = self.source.resolution.path(implementation_key);
            let specification_name = self.source.resolution.path(specification_key);
            let sources = self.retained_sources(
                module,
                span,
                &[implementation_key, specification_key],
                &super::super::operations::Bindings::new(),
                &[],
            )?;
            let snapshot_size = total_size(
                [&implementation_key, &specification_key]
                    .into_iter()
                    .filter_map(|key| self.checked.get(key))
                    .map(|program| representation_size(program.program())),
            );
            let snapshot_work = snapshot_size
                .saturating_add(implementation_name.len())
                .saturating_add(specification_name.len());
            // Raw snapshots and pair names remain private to each distinct
            // pair. Original module bytes are retained and charged once across closures.
            self.charge(module, span, snapshot_work).map_err(|mut error| {
                error.message.push_str(&format!(
                    "; retaining a new function-contract pair snapshot ({snapshot_size} raw representation units, plus pair names); original module bytes are shared across relevant source closures"
                ));
                error
            })?;
            let identity =
                RetainedIdentity::interned(implementation_name, specification_name, sources);
            let raw = |key: &Key| {
                self.checked
                    .get(key)
                    .map(|program| program.program().clone())
                    .ok_or_else(|| {
                        self.error(
                            module,
                            span,
                            ErrorCode::InvalidIr,
                            "contract dependency has not been independently checked",
                        )
                    })
            };
            let implementation = raw(&implementation_key)?;
            let signature = contract_basis(basis);
            let specification = if let Some(key) = declared_meaning {
                self.meanings[&key].raw.clone()
            } else {
                raw(&specification_key)?
            };
            let budget = &mut self.exact_work;
            let evidence = FunctionEvidence::check_retained_with_kernel(
                &self.kernel,
                signature,
                implementation,
                specification,
                identity,
                budget,
            )
            .map_err(|error| {
                self.error(
                    module,
                    span,
                    if error.error.is_capacity() {
                        ErrorCode::Limit
                    } else if matches!(error.error, crate::contract::ContractError::InvalidCircuit(_) | crate::contract::ContractError::EvidenceMismatch) {
                        ErrorCode::InvalidIr
                    } else {
                        ErrorCode::Contract
                    },
                    format!("function semantic contract: {error}{}", if matches!(error.error,
                        crate::contract::ContractError::Arithmetic(crate::contract::exact::ExactError::ArithmeticCapacity)) {
                        " (bounded i128 coefficients or dyadic denominator exponent above 126); no approximate fallback is used"
                    } else { "" }),
                )
            })?;
            let evidence = Arc::new(evidence);
            self.function_evidence
                .insert(cache_key, Arc::clone(&evidence));
            evidence
        };
        Ok(evidence)
    }
}

// Count raw snapshot cloning without opening shared opaque evidence dependencies.
fn representation_size(program: &RawProgram) -> usize {
    let mut size = program.classical_inputs.len()
        + program.classical_outputs.len()
        + program.quantum_outputs.len();
    for input in &program.quantum_inputs {
        size = size.saturating_add(input.wires.len() + 3);
    }
    size.saturating_add(operations_size(&program.operations))
}
