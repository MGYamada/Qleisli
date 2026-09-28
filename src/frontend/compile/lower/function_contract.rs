//! Explicit function-contract applications retain independently checked evidence.

use super::*;
use crate::contract::{
    BasisType, DEFAULT_EXACT_WORK, FunctionEvidence, FunctionIdentity, MAX_CONTRACT_BITS,
    exact::Budget,
};
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
            .charge(module, span, self.registers[&slot].size())?;
        let basis = self.registers[&slot].basis.clone();
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
        let specification_key = self.contract_function(module, specification, &basis, env)?;
        let cache_key = (implementation_key.clone(), specification_key.clone());
        let evidence = if let Some(evidence) = self.compiler.function_evidence.get(&cache_key) {
            // Only this compiler populates the cache, using the exact resolved
            // keys and independently checked raw functions below. The loaded
            // project and those dependencies cannot change during compilation.
            // Reuse therefore needs neither a digest nor repeated source/raw
            // comparisons. External evidence still uses check_binding.
            Arc::clone(evidence)
        } else {
            let implementation_name = format!("{}::{}", implementation_key.0, implementation_key.1);
            let specification_name = format!("{}::{}", specification_key.0, specification_key.1);
            let source_size = total_size(
                self.compiler
                    .project
                    .modules
                    .iter()
                    .map(|(name, source)| name.len().saturating_add(source.source.len())),
            );
            let snapshot_size = total_size(
                [&implementation_key, &specification_key]
                    .into_iter()
                    .filter_map(|key| self.compiler.checked.get(key))
                    .map(|program| representation_size(program.program())),
            );
            let snapshot_work = source_size
                .saturating_add(snapshot_size)
                .saturating_add(implementation_name.len())
                .saturating_add(specification_name.len());
            // Charge the snapshots before cloning them, once for each new
            // implementation/specification pair rather than at every call.
            self.compiler.charge(module, span, snapshot_work)?;
            let identity = FunctionIdentity {
                implementation: implementation_name,
                specification: specification_name,
                sources: self
                    .compiler
                    .project
                    .modules
                    .iter()
                    .map(|(name, source)| (name.clone(), source.source.clone()))
                    .collect(),
            };
            let raw = |key: &Key| {
                self.compiler
                    .checked
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
            let specification = raw(&specification_key)?;
            let signature = contract_basis(&basis);
            let mut budget = Budget::new(DEFAULT_EXACT_WORK);
            let evidence = FunctionEvidence::check_diagnostic(
                signature,
                implementation,
                specification,
                identity,
                &mut budget,
            )
            .map_err(|error| {
                self.error(
                    module,
                    span,
                    ErrorCode::InvalidIr,
                    format!("function semantic contract: {error}"),
                )
            })?;
            let evidence = Arc::new(evidence);
            self.compiler
                .function_evidence
                .insert(cache_key, Arc::clone(&evidence));
            evidence
        };
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
        if env.contains_key(&name.text) || self.bindings.contains_key(&name.text) {
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
                "apply_contract requires ordinary declared unitary functions",
            ));
        };
        if self.compiler.declarations[&key].kind != FnKind::Unitary {
            return Err(self.error(
                module,
                name.span,
                ErrorCode::Effect,
                "apply_contract requires declared unitary functions",
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
        let expected = Ty::Q(Box::new(basis.clone()));
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

// Source types have already passed their depth/node bounds. Contract construction
// independently enforces its stricter type-tree profile before accepting evidence.
fn contract_basis(basis: &Ty) -> BasisType {
    match basis {
        Ty::Unit => BasisType::Unit,
        Ty::Bit => BasisType::Bit,
        Ty::Pair(left, right) => BasisType::pair(contract_basis(left), contract_basis(right)),
        _ => unreachable!("quantum basis type"),
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
