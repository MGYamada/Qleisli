//! Static descriptions are compile-time arguments, never runtime owners.
use super::super::operations::{Bindings, Operation};
use super::*;

impl Lowerer<'_, '_> {
    pub(super) fn apply_operation(
        &mut self,
        module: &str,
        span: Span,
        op: &Operation,
        value: Value,
        access: Access,
    ) -> Result<Value, CompileError> {
        let slot = self.quantum(module, span, &value, false)?;
        let (domain, codomain) = if access == Access::Adjoint {
            (&op.codomain, &op.basis)
        } else {
            (&op.basis, &op.codomain)
        };
        if self.raw.registers[&slot].basis != *domain {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "operation and argument have different exact basis trees",
            ));
        }
        if !op.needs_raw() {
            let steps = op.steps(module, span, access, self.compiler)?;
            self.apply_circuit(slot, steps);
            self.add_contract_effect(module, span, op.effect);
            return Ok(value);
        }
        let body = op.raw(module, span, access, self.compiler)?;
        let original = &self.raw.registers[&slot];
        let input = QuantumPort {
            token: original.token,
            wires: original.wires.clone(),
            shape: body.boundary().input().shape,
        };
        let start = self.raw.operations.len();
        let output = crate::frontend::raw_splice::append(
            &mut self.raw,
            body.program(),
            &input,
            &mut self.compiler.exact_work,
        )
        .map_err(|e| self.compiler.op_error(module, span, e))?;
        // Check the actual renamed fragment, including its concrete ordered ports.
        let emitted = RawProgram {
            quantum_inputs: vec![input],
            classical_inputs: vec![],
            operations: self.raw.operations[start..].to_vec(),
            quantum_outputs: vec![output.token],
            classical_outputs: vec![],
            declared_effect: body.program().raw().declared_effect,
        };
        crate::frontend::pure::check(
            &self.compiler.kernel,
            &emitted,
            body.boundary().domain(),
            body.boundary().codomain(),
            Some(body.meaning()),
            &mut self.compiler.exact_work,
        )
        .map_err(|e| self.compiler.op_error(module, span, e))?;
        self.add_effect(module, span, emitted.declared_effect);
        self.add_contract_effect(module, span, op.effect);
        self.raw.registers.insert(
            slot,
            Register {
                token: output.token,
                wires: output.wires,
                basis: codomain.clone(),
            },
        );
        Ok(Value::Quantum(slot, Ty::quantum(codomain.clone())))
    }
    pub(super) fn constructed_inverse(
        &mut self,
        module: &str,
        span: Span,
        operation: &StaticOp,
        input: &Expr,
        env: &mut Env,
    ) -> Result<Value, CompileError> {
        let value = self.expr(module, input, env)?;
        let op = self.operation(module, operation, env)?;
        self.apply_operation(module, span, &op, value, Access::Adjoint)
    }

    pub(super) fn controlled_application(
        &mut self,
        module: &str,
        span: Span,
        operation: &StaticOp,
        args: &[Expr],
        env: &mut Env,
    ) -> Result<Value, CompileError> {
        let [control, target] = args else {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "controlled application requires a control and a target",
            ));
        };
        let c = self.expr(module, control, env)?;
        self.quantum(module, control.span, &c, true)?;
        let q = self.expr(module, target, env)?;
        let slot = self.quantum(module, target.span, &q, false)?;
        let op = self.operation(module, operation, env)?;
        if op.basis != self.raw.registers[&slot].basis {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "controlled operation and target have different exact basis trees",
            ));
        }
        let steps = op.steps(module, span, Access::Controlled, self.compiler)?;
        self.add_contract_effect(module, span, op.effect);
        let joined = self.primitive_call(module, span, PrimitiveId::Join, vec![c, q])?;
        let slot = self.quantum(module, span, &joined, false)?;
        self.apply_circuit(slot, steps);
        self.primitive_call(module, span, PrimitiveId::Split, vec![joined])
    }

    pub(super) fn bound_operation(&self, name: &Ident) -> Option<&Operation> {
        let id = self.compiler.locals().usage(name).static_parameter?;
        self.bindings.get(self.compiler.locals().key(id))
    }

    pub(super) fn operation(
        &mut self,
        module: &str,
        expr: &StaticOp,
        _env: &Env,
    ) -> Result<Operation, CompileError> {
        use crate::frontend::check::plans::{
            BodyStaticKind, BodyStaticOriginal, StaticCategory, original_body_static,
        };
        let mut work = self.compiler.work;
        let original = (|| {
            self.compiler
                .charge_at(&mut work, module, expr.span, module.len() + 4)?;
            let lookup = self.compiler.locals();
            let owner = lookup
                .try_node_id_static_op(expr)
                .map(|node| node.definition())
                .ok_or_else(|| {
                    self.error(
                        module,
                        expr.span,
                        ErrorCode::TypeMismatch,
                        "operation is not an original source occurrence",
                    )
                })?;
            let declaration = self.compiler.source.resolution.declaration(owner);
            if declaration.name.0 != module || self.compiler.current_instance_owner() != Some(owner)
            {
                return Err(self.error(
                    module,
                    expr.span,
                    ErrorCode::TypeMismatch,
                    "operation differs from its active original source owner",
                ));
            }
            let plan = original_body_static(
                &self.compiler.source,
                &lookup,
                owner,
                declaration.module,
                BodyStaticOriginal::Operation(expr),
                &mut |span, cells| self.compiler.charge_at(&mut work, module, span, cells),
                &|span, message| self.error(module, span, ErrorCode::TypeMismatch, message),
            )?;
            let BodyStaticKind::Operation { operation, .. } = &plan.kind else {
                return Err(self.error(
                    module,
                    expr.span,
                    ErrorCode::TypeMismatch,
                    "original operation plan has a different kind",
                ));
            };
            self.compiler.charge_at(&mut work, module, expr.span, 2)?;
            Ok((Arc::clone(operation), Arc::clone(&plan.environment)))
        })();
        self.compiler.work = work;
        let (operation, environment) = original?;
        match self.compiler.evaluate_source_static(
            &operation,
            &environment,
            StaticCategory::Operation,
            [false; 3],
            &self.bindings,
            module,
        )? {
            super::super::instances::StaticValue::Operation(operation) => Ok(operation),
            _ => Err(self.error(
                module,
                expr.span,
                ErrorCode::TypeMismatch,
                "operation remains unbound in the concrete instance",
            )),
        }
    }

    pub(super) fn static_name(
        &self,
        module: &str,
        name: &Ident,
        env: &Env,
    ) -> Result<(), CompileError> {
        if self
            .compiler
            .locals()
            .local_key(name)
            .is_some_and(|key| env.contains_key(key))
        {
            return Err(self.error(
                module,
                name.span,
                ErrorCode::TypeMismatch,
                "a local or spent runtime value cannot be a static operation",
            ));
        }
        Ok(())
    }

    pub(super) fn operation_steps(
        &mut self,
        module: &str,
        name: &Ident,
        basis: &Ty,
        env: &Env,
        access: Access,
    ) -> Result<Option<Vec<CircuitStep>>, CompileError> {
        let Some(op) = self.bound_operation(name) else {
            return Ok(None);
        };
        let cost = op.copy_size();
        self.compiler.charge(module, name.span, cost)?;
        let op = self
            .bound_operation(name)
            .expect("retained static binding")
            .clone();
        self.static_name(module, name, env)?;
        if op.basis != *basis {
            return Err(self.error(
                module,
                name.span,
                ErrorCode::TypeMismatch,
                format!("operation and input have different exact basis trees: expected `Q<{}>`, found `Q<{basis}>`", op.basis),
            ));
        }
        self.add_contract_effect(module, name.span, op.effect);
        Ok(Some(op.steps(module, name.span, access, self.compiler)?))
    }

    pub(super) fn call_bound(
        &mut self,
        key: &Key,
        args: Vec<Value>,
        site: Option<CallSite<'_>>,
        bindings: Bindings,
    ) -> Result<Value, CompileError> {
        let declaration = self.compiler.declarations[key];
        let own_module = self.compiler.dormant_module(*key, declaration.span)?;
        let (module, span) = site.map_or((own_module.as_str(), declaration.span), |site| {
            (site.module, site.span)
        });
        let instance = self.compiler.prepare_instance(
            *key,
            BTreeMap::new(),
            BTreeMap::new(),
            bindings,
            module,
            span,
        )?;
        self.call_instance(key, args, site, instance)
    }

    pub(super) fn call_instance(
        &mut self,
        key: &Key,
        args: Vec<Value>,
        site: Option<CallSite<'_>>,
        instance: Arc<super::super::instances::ClosedInstance>,
    ) -> Result<Value, CompileError> {
        let own_module = self
            .compiler
            .dormant_module(*key, self.compiler.declarations[key].span)?;
        let (module, span) = site.map_or(
            (own_module.as_str(), self.compiler.declarations[key].span),
            |site| (site.module, site.span),
        );
        for (key, operation) in &instance.operations {
            self.compiler
                .charge(module, span, key.name.len() + operation.copy_size() + 1)?;
        }
        self.compiler.charge(module, span, 1)?;
        self.compiler
            .check_dormant_instance(Arc::clone(&instance), module, span)?;
        let bindings = instance.operations.clone();
        let frame = self.compiler.enter_instance(instance, module, span)?;
        let previous = std::mem::replace(&mut self.bindings, bindings);
        let result = self.call_user(key, args, site);
        self.bindings = previous;
        self.compiler.leave_instance(frame);
        result
    }
}
