//! Isolated lowering for exact semantic compute/use/uncompute contracts.
//!
//! Both circuits are retained in raw IR. The independent verifier, rather than
//! this frontend, establishes their intertwining equation and authorizes the
//! private auxiliary's exact cleanup.

use super::*;
use crate::contract::{MAX_CONTRACT_BITS, MAX_CONTRACT_STEPS};

impl Lowerer<'_, '_> {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn certified_computed(
        &mut self,
        module: &str,
        span: Span,
        source: Value,
        function: &Ident,
        logical: &Ident,
        data_binder: &Ident,
        ancilla_binder: &Ident,
        body: &Block,
        env: &Env,
    ) -> Result<Value, CompileError> {
        let source_slot = self.quantum(module, span, &source, false)?;
        self.compiler
            .charge(module, span, self.registers[&source_slot].size())?;
        let source_reg = self.registers[&source_slot].clone();
        if source_reg.wires.len() >= MAX_CONTRACT_BITS {
            return Err(self.error(
                module,
                span,
                ErrorCode::Limit,
                format!(
                    "semantic contracts currently allow at most {} data bits and 1 auxiliary bit",
                    MAX_CONTRACT_BITS - 1
                ),
            ));
        }
        if self
            .compiler
            .locals
            .local_key(function)
            .is_some_and(|key| env.contains_key(key))
            || self.bound_operation(function).is_some()
        {
            return Err(self.error(
                module,
                function.span,
                ErrorCode::TypeMismatch,
                "with_computed requires a basis function name, not a local value",
            ));
        }
        let Callee::User(key) = self.compiler.resolve(module, function)? else {
            return Err(self.error(
                module,
                function.span,
                ErrorCode::TypeMismatch,
                "predicate must be a basis function",
            ));
        };
        let predicate = self.compiler.basis.get(&key).ok_or_else(|| {
            self.error(
                module,
                function.span,
                ErrorCode::TypeMismatch,
                "predicate must be a basis function",
            )
        })?;
        let size = predicate
            .signature_size()
            .saturating_add(predicate.table.len());
        self.compiler.charge(module, function.span, size)?;
        let predicate = self.compiler.basis[&key].clone();
        self.compiler.check_predicate_domain(
            module,
            function.span,
            &predicate,
            &source_reg.basis,
        )?;
        if data_binder.text == ancilla_binder.text {
            return Err(self.error(
                module,
                ancilla_binder.span,
                ErrorCode::Ownership,
                "certified data and auxiliary binders must be distinct",
            ));
        }
        let logical_steps = self.static_steps(module, logical, &source_reg.basis, env)?;
        let use_steps = self.certified_body(
            module,
            &source_reg.basis,
            data_binder,
            ancilla_binder,
            body,
            env,
        )?;
        if use_steps.len() > MAX_CONTRACT_STEPS || logical_steps.len() > MAX_CONTRACT_STEPS {
            return Err(self.error(
                module,
                span,
                ErrorCode::Limit,
                format!(
                    "semantic contract circuits currently allow at most {MAX_CONTRACT_STEPS} steps each"
                ),
            ));
        }
        if self.abstract_check {
            // This skeleton is used only for parametric source checking. No
            // certificate or executable generic body is produced from it.
            self.apply_circuit(source_slot, logical_steps);
            return Ok(source);
        }
        let wire = self.wire();
        let output = self.token();
        self.operations.push(RawOp::CertifiedCompute {
            source: source_reg.token,
            source_out: output,
            ancilla_wires: vec![wire],
            function: predicate.table,
            use_steps,
            logical_steps,
        });
        self.registers
            .get_mut(&source_slot)
            .expect("owned source")
            .token = output;
        Ok(source)
    }

    fn certified_body(
        &mut self,
        module: &str,
        basis: &Ty,
        data_binder: &Ident,
        ancilla_binder: &Ident,
        body: &Block,
        env: &Env,
    ) -> Result<Vec<CircuitStep>, CompileError> {
        let joint = Ty::quantum(Ty::pair(basis.clone(), Ty::bit()));
        self.compiler
            .check_tree(module, body.span, joint.tree_size())?;
        self.compiler.charge(
            module,
            body.span,
            joint.tree_size().nodes.saturating_mul(3) + env_size(env),
        )?;
        self.compiler.charge(
            module,
            body.span,
            total_size(
                self.bindings
                    .values()
                    .map(super::super::operations::Operation::copy_size),
            ),
        )?;
        let mut inner = Lowerer {
            compiler: self.compiler,
            registers: BTreeMap::new(),
            operations: vec![],
            operation_sources: BTreeMap::new(),
            tuple_binding_origins: Vec::new(),
            next_token: 0,
            next_wire: 0,
            next_classical: 0,
            next_slot: 0,
            effect: Effect::Unitary,
            effect_source: None,
            depth: self.depth,
            bindings: self.bindings.clone(),
            abstract_check: self.abstract_check,
        };
        let mut quantum_inputs = vec![];
        let mut classical_inputs = vec![];
        let input = inner.input(
            &joint,
            module,
            body.span,
            &mut quantum_inputs,
            &mut classical_inputs,
        )?;
        let Value::Pair(data, ancilla) =
            inner.sealed(module, body.span, "std::quantum", "split", vec![input])?
        else {
            unreachable!("split returns a pair")
        };
        // Hidden outer names still hide functions, but no outer classical or
        // quantum value can be captured by the independently checked circuit.
        let mut local: Env = env
            .iter()
            .map(|(name, binding)| (name.clone(), binding.hidden()))
            .collect();
        inner.bind_env(data_binder, Binding::Live(*data), &mut local);
        inner.bind_env(ancilla_binder, Binding::Live(*ancilla), &mut local);
        let result = inner.block(module, body, &mut local)?;
        inner.no_owned_bindings(module, body.span, &local, [data_binder, ancilla_binder])?;
        if inner.effect != Effect::Unitary {
            return Err(inner.error(
                module,
                body.span,
                ErrorCode::Effect,
                "certified with_computed body must be unitary",
            ));
        }
        let expected = Ty::pair(Ty::quantum(basis.clone()), Ty::quantum(Ty::bit()));
        if result.ty() != expected {
            return Err(inner.error(
                module,
                body.result.span,
                ErrorCode::TypeMismatch,
                "certified with_computed must return (Q<A>, Q<Bit>) in data/auxiliary order",
            ));
        }
        let Value::Pair(data, ancilla) = result else {
            unreachable!("checked pair type")
        };
        let result = inner.sealed(
            module,
            body.span,
            "std::quantum",
            "join",
            vec![*data, *ancilla],
        )?;
        let slot = inner.quantum(module, body.span, &result, false)?;
        let raw = RawProgram {
            quantum_inputs,
            classical_inputs,
            operations: inner.operations,
            quantum_outputs: vec![inner.registers[&slot].token],
            classical_outputs: vec![],
            declared_effect: Effect::Unitary,
        };
        let checked = inner
            .compiler
            .kernel
            .accept_raw_with_budget(raw, &mut inner.compiler.exact_work)
            .map_err(|err| {
                let limit = err.code == "limit";
                verification_error(
                    inner.compiler,
                    &inner.operation_sources,
                    module,
                    body.span,
                    err,
                    limit,
                )
            })?;
        super::super::circuit::flatten(inner.compiler, module, body.span, &checked)
    }
}
