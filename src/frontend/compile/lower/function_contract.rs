//! Explicit function-contract applications retain independently checked evidence.

use super::super::operations::contract_basis;
use super::*;
use crate::contract::{FunctionEvidence, MAX_CONTRACT_BITS, function::RetainedIdentity};
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
        let slot = self.quantum(module, span, &input, false)?;
        self.compiler
            .charge(module, span, self.raw.registers[&slot].size())?;
        let basis = self.raw.registers[&slot].basis.clone();
        let bits = basis.basis_bits().expect("quantum basis");
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
                    .locals
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

    fn contract_function(
        &mut self,
        module: &str,
        name: &Ident,
        basis: &Ty,
        env: &Env,
    ) -> Result<Key, CompileError> {
        if self
            .compiler
            .locals
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
        if self.compiler.effects.get(&key).map(|fact| fact.inferred()) != Some(Effect::Unitary) {
            return Err(self.error(
                module,
                name.span,
                ErrorCode::Effect,
                crate::frontend::effects::unitary_required(
                    "apply_contract requires inferred Unitary functions",
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
            || self.effects[&implementation_key].inferred() != Effect::Unitary
        {
            return Err(self.error(module, span, ErrorCode::TypeMismatch, "contract implementation must be a closed principal-Unitary exact quantum endomorphism"));
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
                || self.effects[&specification_key].inferred() != Effect::Unitary
            {
                return Err(self.error(module, span, ErrorCode::TypeMismatch, "contract specification must have the same closed principal-Unitary exact quantum interface"));
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
            let implementation_name = self.resolution.path(implementation_key);
            let specification_name = self.resolution.path(specification_key);
            let sources = self.retained_sources(module, span)?;
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
            // pair. Source bytes were retained and charged once for the project.
            self.charge(module, span, snapshot_work).map_err(|mut error| {
                error.message.push_str(&format!(
                    "; retaining a new function-contract pair snapshot ({snapshot_size} raw representation units, plus pair names); source bytes use the shared project snapshot"
                ));
                error
            })?;
            let identity =
                RetainedIdentity::shared(implementation_name, specification_name, sources);
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
    let mut pending = vec![program.operations.as_slice()];
    while let Some(operations) = pending.pop() {
        for operation in operations {
            size = size.saturating_add(8);
            let extra = match operation {
                RawOp::ApplyUnitary { steps, .. } => {
                    total_size(steps.iter().map(super::super::circuit::size))
                }
                RawOp::CertifiedCompute {
                    ancilla_wires,
                    function,
                    use_steps,
                    logical_steps,
                    ..
                } => total_size([
                    ancilla_wires.len(),
                    function.len(),
                    total_size(use_steps.iter().map(super::super::circuit::size)),
                    total_size(logical_steps.iter().map(super::super::circuit::size)),
                ]),
                RawOp::LiftBasis {
                    output_wires,
                    table,
                    ..
                } => output_wires.len() + table.len(),
                RawOp::QuantumIf {
                    zero_ops, one_ops, ..
                } => 4 * (zero_ops.len() + one_ops.len()),
                RawOp::ClassicalBranch {
                    then_ops,
                    else_ops,
                    quantum_phis,
                    classical_phis,
                    ..
                } => {
                    pending.extend([then_ops.as_slice(), else_ops.as_slice()]);
                    total_size(quantum_phis.iter().map(|phi| phi.output_wires.len() + 3))
                        .saturating_add(classical_phis.len().saturating_mul(3))
                }
                RawOp::ComputeUseUncompute {
                    targets,
                    ancilla_wires,
                    function,
                    use_ops,
                    ..
                } => total_size([
                    targets.len().saturating_mul(2),
                    ancilla_wires.len(),
                    function.len(),
                    total_size(use_ops.iter().map(|usage| match usage {
                        ProtectedUse::ProtectedGate { .. } => 3,
                        ProtectedUse::ControlledTargetGate { controls, .. }
                        | ProtectedUse::ControlledPhase { controls, .. } => 3 + controls.len() * 3,
                    })),
                ]),
                _ => 0,
            };
            size = size.saturating_add(extra);
        }
    }
    size
}
