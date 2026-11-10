//! Original direct transforms of complete specialized quantum owner groups.
//! Packing is untrusted structural lowering; native checking still sees the
//! actual body, ordered ports and transformed operations. This is no general
//! source-preservation theorem.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;
use crate::frontend::check::plans::{BodyStaticKind, BodyStaticOriginal};

impl Lowerer<'_, '_> {
    /// A direct declaration may have an ordinary tuple of quantum owners.
    /// Opaque Op constructors keep their separate single-owner contract.
    pub(super) fn runtime_transform(
        &mut self,
        module: &str,
        original: &Expr,
        operation: &StaticOp,
        input: &Expr,
        env: &mut Env,
        access: Access,
    ) -> Result<Option<Value>, CompileError> {
        let mut leaf = operation;
        let mut depth = 0;
        while let StaticOpKind::Repeat(_, child) = &leaf.kind {
            self.compiler.tick(module, leaf.span)?;
            depth += 1;
            if depth >= MAX_DEPTH {
                return Err(self.static_refusal(
                    module,
                    leaf.span,
                    ErrorCode::Limit,
                    "direct transform description exceeds depth 64",
                )?);
            }
            leaf = child;
        }
        let (name, specialized) = match &leaf.kind {
            StaticOpKind::Name(name) => (name, false),
            StaticOpKind::Specialize { name, .. } => (name, true),
            _ => return Ok(None),
        };
        self.static_name(module, name, env)?;
        // Local Op formals use their original operation plan and bindings in
        // the ordinary operation adapter. They are not declaration transforms;
        // an absent formal binding must not be recovered as a global name.
        if matches!(
            self.compiler.locals().usage(name).target,
            ResolvedUse::Local(_)
        ) {
            return Ok(None);
        }
        let Callee::User(target) = self.compiler.resolve(module, name)? else {
            return Ok(None);
        };
        // Keep the established closed unary route (and its nested evidence)
        // for the original bare name. Specialized/grouped calls use the full
        // instance contract below, never a DefId-only provider cache.
        if !specialized
            && depth == 0
            && self.compiler.declarations[&target].static_params.is_empty()
        {
            let (parameters, result) = self.compiler.signature(&target)?;
            if parameters.len() == 1
                && parameters[0].quantum_basis().is_some()
                && result.quantum_basis().is_some()
            {
                return Ok(None);
            }
        }
        let (actuals, environment, mask) = self.static_plan(
            module, BodyStaticOriginal::Operation(operation),
            |compiler, work, root| {
                macro_rules! refuse {
                    ($message:literal) => {{
                        compiler.charge_at(work, module, original.span, $message.len() + 1)?;
                        return Err(compiler.error(module, original.span, ErrorCode::TypeMismatch, $message));
                    }};
                }
                compiler.charge_at(work, module, original.span, module.len() + name.text.len() + 18)?;
                let BodyStaticKind::Operation { expression, requested, .. } = &root.kind else {
                    refuse!("direct transform lacks its original operation root");
                };
                if compiler.current_instance_owner() != Some(root.owner)
                    || !requested[crate::frontend::formals::access_index(access)]
                { refuse!("direct transform differs from its original active operation owner or access"); }
                let operands_match = match (&original.kind, access) {
                    (ExprKind::ApplyStatic { operation: op, input: arg }, Access::Apply)
                    | (ExprKind::Adjoint { operation: op, input: arg }, Access::Adjoint) =>
                        std::ptr::eq(op, operation) && std::ptr::eq(arg.as_ref(), input),
                    (ExprKind::Controlled { operation: op, args }, Access::Controlled) =>
                        std::ptr::eq(op, operation) && args.len() == 2 && std::ptr::eq(&args[1], input),
                    _ => false,
                };
                if !operands_match { refuse!("direct transform operands differ from the original expression"); }
                let lookup = compiler.locals();
                let Some(node) = lookup.try_node_id_expr(original) else { refuse!("direct transform is not an original expression"); };
                let Some(site) = lookup.try_reference_site(name) else { refuse!("direct transform target is not an original reference"); };
                let Some(plan) = compiler.source.static_calls.get(&site) else { refuse!("direct transform lacks its original call plan"); };
                if node != *expression || node.definition() != root.owner || site.definition() != root.owner
                    || plan.owner != root.owner || plan.module != root.environment.module
                    || plan.node != node || plan.target != target || plan.callee.site != site
                    || plan.callee.local.is_some()
                    || plan.callee.target != ResolvedUse::Global(Target::Declaration(target))
                    || plan.environment.owner != root.owner
                    || plan.environment.module != root.environment.module
                    || plan.source_effect != compiler.effect_in_module(module, target)
                { refuse!("direct transform call plan has a different original identity or effect"); }
                let cost = plan.arguments.iter().fold(plan.arguments.len() + 2, |cells, actual| {
                    cells.saturating_add(actual.formal.name.len() + 2)
                });
                compiler.charge_at(work, module, original.span, cost)?;
                Ok((plan.arguments.clone(), Arc::clone(&plan.environment), plan.access))
            },
        )?;
        self.compiler.charge(module, original.span, 4)?;
        if !mask[crate::frontend::formals::access_index(access)]
            || self.compiler.effect_in_module(module, target) != Some(Effect::Unitary)
        {
            return Err(self.static_refusal(module, original.span, ErrorCode::Effect,
                "direct transform requires the original available Unitary effect and requested access")?);
        }
        let instance = self.compiler.bind_source_instance(
            target,
            &actuals,
            &environment,
            &self.bindings,
            module,
            original.span,
        )?;
        self.compiler.charge(
            module,
            original.span,
            instance.operations.len().saturating_mul(3) + 1,
        )?;
        if access != Access::Apply
            && instance.operations.values().any(|operation| {
                !operation.access[0]
                    || !operation.access[1]
                    || (access == Access::Controlled && !operation.access[2])
            })
        {
            return Err(self.static_refusal(
                module,
                original.span,
                ErrorCode::Effect,
                "direct transform actual operations lack the required inverse or control access",
            )?);
        }
        self.compiler.charge(
            module,
            original.span,
            total_size(
                instance
                    .interface
                    .parameters
                    .iter()
                    .map(|ty| ty.tree_size().nodes),
            ) + instance.interface.result.tree_size().nodes
                + instance.interface.parameters.len()
                + 4,
        )?;
        let group = if instance.interface.parameters.len() == 1 {
            instance.interface.parameters[0].clone()
        } else {
            Ty::tuple(instance.interface.parameters.clone())
        };
        if group != instance.interface.result {
            // The existing pure-provider path checks rectangular adjoints,
            // including the actual inverse evidence, instead of flattening.
            return Ok(None);
        }
        let mut copies = 1u32;
        let mut current = operation;
        while let StaticOpKind::Repeat(count, child) = &current.kind {
            let (Count::Natural(natural) | Count::Power(natural)) = count;
            let number = self.static_natural_value(module, natural)?;
            let number = if matches!(count, Count::Power(_)) {
                1u32.checked_shl(number)
            } else {
                Some(number)
            };
            copies = match number
                .filter(|number| *number <= 4096)
                .and_then(|number| copies.checked_mul(number))
                .filter(|number| *number <= 4096)
            {
                Some(number) => number,
                None => {
                    return Err(self.static_refusal(
                        module,
                        natural.span,
                        ErrorCode::Limit,
                        "static repetition exceeds the 4096-count limit",
                    )?);
                }
            };
            current = child;
        }
        let copies = u16::try_from(copies).expect("bounded direct repetition");
        if !specialized
            && depth != 0
            && instance.interface.parameters.len() == 1
            && group.quantum_basis().is_some()
            && access == Access::Apply
        {
            return self
                .named_transform(module, original.span, name, Some(copies), input, env)
                .map(Some);
        }
        // Even zero copies must prepare/check the real original body, including
        // its dormant contracts. No result is admitted by a host cache alone.
        let body = self
            .compiler
            .materialize_instance(instance, module, original.span)?;
        if body.raw().declared_effect != Effect::Unitary {
            return Err(self.static_refusal(
                module,
                original.span,
                ErrorCode::Effect,
                "direct transform body is not independently checked as Unitary",
            )?);
        }
        let mut steps =
            super::super::circuit::flatten(self.compiler, module, original.span, &body)?;
        let control = if access == Access::Controlled {
            let ExprKind::Controlled { args, .. } = &original.kind else {
                unreachable!("original operands checked")
            };
            let control = self.expr(module, &args[0], env)?;
            self.quantum(module, args[0].span, &control, true)?;
            Some(control)
        } else {
            None
        };
        let value = self.expr(module, input, env)?;
        self.compiler.charge(
            module,
            input.span,
            value.tree_size().nodes + group.tree_size().nodes + 1,
        )?;
        if value.ty() != group {
            return Err(self.static_refusal(
                module,
                input.span,
                ErrorCode::TypeMismatch,
                "direct transform changes the complete exact quantum owner group",
            )?);
        }
        let packed = self.pack_runtime_group(module, original.span, value)?;
        let slot = self.quantum(module, original.span, &packed, false)?;
        let basis = &self.raw.registers[&slot].basis;
        let width = self.circuit_width(module, original.span, basis)?;
        let mut expected = if body.raw().quantum_inputs.len() == 1
            && body.raw().quantum_outputs.len() == 1
            && width <= crate::contract::MAX_CONTRACT_BITS
        {
            Some(
                crate::contract::function::verified_meaning(
                    &body,
                    &super::super::operations::contract_basis(basis),
                    &mut self.compiler.exact_work,
                )
                .map_err(|error| self.compiler.op_error(module, original.span, error))?,
            )
        } else {
            None
        };
        self.compiler
            .charge(module, original.span, basis.tree_size().nodes)?;
        let basis = basis.clone();
        self.check_transformed(module, original.span, &basis, &steps, expected.as_ref())?;
        let cost = total_size(steps.iter().map(super::super::circuit::size));
        self.compiler.charge(
            module,
            original.span,
            cost.saturating_add(1).saturating_mul(usize::from(copies)),
        )?;
        let repeated: Vec<_> = (0..copies).flat_map(|_| steps.iter().cloned()).collect();
        transforms::check_repeated_steps(&steps, &repeated, copies)
            .map_err(|error| self.compiler.op_error(module, original.span, error))?;
        steps = repeated;
        if copies != 1 {
            expected = None;
        }
        if access == Access::Adjoint {
            self.compiler.charge(
                module,
                original.span,
                total_size(steps.iter().map(super::super::circuit::size)),
            )?;
            super::super::circuit::invert(&mut steps);
            expected = expected
                .map(|meaning| meaning.adjoint(&mut self.compiler.exact_work))
                .transpose()
                .map_err(|error| self.compiler.op_error(module, original.span, error.into()))?;
        }
        self.check_transformed(module, original.span, &basis, &steps, expected.as_ref())?;
        let output = if let Some(control) = control {
            self.compiler.charge(
                module,
                original.span,
                width + total_size(steps.iter().map(super::super::circuit::size)) + steps.len() * 2,
            )?;
            let axes: Vec<_> = (1..=width).collect();
            for step in &mut steps {
                super::super::circuit::remap(step, &axes);
                step.controls.push(BitControl {
                    index: 0,
                    when_one: true,
                });
            }
            let joined = self.primitive_call(
                module,
                original.span,
                PrimitiveId::Join,
                vec![control, packed],
            )?;
            let joined_slot = self.quantum(module, original.span, &joined, false)?;
            self.apply_circuit(joined_slot, steps);
            let split =
                self.primitive_call(module, original.span, PrimitiveId::Split, vec![joined])?;
            let Value::Pair(control, packed) = split else {
                unreachable!("structural pair split")
            };
            Value::pair(
                *control,
                self.unpack_runtime_group(module, original.span, *packed, &group)?,
            )
        } else {
            self.apply_circuit(slot, steps);
            self.unpack_runtime_group(module, original.span, packed, &group)?
        };
        self.add_contract_effect(module, original.span, Effect::Unitary);
        Ok(Some(output))
    }

    fn pack_runtime_group(
        &mut self,
        module: &str,
        span: Span,
        value: Value,
    ) -> Result<Value, CompileError> {
        self.compiler.tick(module, span)?;
        if matches!(value, Value::Quantum(..)) {
            return Ok(value);
        }
        self.compiler
            .charge(module, span, value.tree_size().nodes + 3)?;
        let Some(fields) = value.into_fields() else {
            return Err(self.static_refusal(
                module,
                span,
                ErrorCode::TypeMismatch,
                "direct transforms require only complete quantum owners",
            )?);
        };
        self.compiler.charge(module, span, fields.len() + 1)?;
        let count = fields.len();
        if count == 0 {
            return Err(self.static_refusal(
                module,
                span,
                ErrorCode::TypeMismatch,
                "direct transforms require a nonempty quantum owner group",
            )?);
        }
        self.pack_runtime_fields(module, span, &mut fields.into_iter(), count)
    }

    fn pack_runtime_fields(
        &mut self,
        module: &str,
        span: Span,
        fields: &mut std::vec::IntoIter<Value>,
        count: usize,
    ) -> Result<Value, CompileError> {
        self.compiler.tick(module, span)?;
        if count == 1 {
            return self.pack_runtime_group(
                module,
                span,
                fields.next().expect("complete group field"),
            );
        }
        let middle = count / 2;
        let left = self.pack_runtime_fields(module, span, fields, middle)?;
        let right = self.pack_runtime_fields(module, span, fields, count - middle)?;
        self.primitive_call(module, span, PrimitiveId::Join, vec![left, right])
    }

    fn unpack_runtime_group(
        &mut self,
        module: &str,
        span: Span,
        packed: Value,
        shape: &Ty,
    ) -> Result<Value, CompileError> {
        self.compiler.tick(module, span)?;
        if shape.quantum_basis().is_some() {
            self.compiler.charge(
                module,
                span,
                packed.tree_size().nodes + shape.tree_size().nodes + 1,
            )?;
            if packed.ty() != *shape {
                return Err(self.static_refusal(
                    module,
                    span,
                    ErrorCode::TypeMismatch,
                    "structural transform unpacking changes an exact owner type",
                )?);
            }
            return Ok(packed);
        }
        let Some(fields) = shape.tuple_fields() else {
            return Err(self.static_refusal(
                module,
                span,
                ErrorCode::TypeMismatch,
                "structural transform unpacking requires a quantum owner group",
            )?);
        };
        self.compiler.charge(module, span, fields.len() * 2 + 1)?;
        let mut output = Vec::with_capacity(fields.len());
        self.unpack_runtime_fields(module, span, packed, fields, &mut output)?;
        Ok(Value::tuple(output))
    }

    fn unpack_runtime_fields(
        &mut self,
        module: &str,
        span: Span,
        packed: Value,
        fields: &[Ty],
        output: &mut Vec<Value>,
    ) -> Result<(), CompileError> {
        self.compiler.tick(module, span)?;
        if fields.len() == 1 {
            output.push(self.unpack_runtime_group(module, span, packed, &fields[0])?);
            return Ok(());
        }
        if fields.is_empty() {
            return Err(self.static_refusal(
                module,
                span,
                ErrorCode::TypeMismatch,
                "structural transform unpacking requires a nonempty owner group",
            )?);
        }
        let split = self.primitive_call(module, span, PrimitiveId::Split, vec![packed])?;
        let Value::Pair(left, right) = split else {
            unreachable!("structural pair split")
        };
        let middle = fields.len() / 2;
        self.unpack_runtime_fields(module, span, *left, &fields[..middle], output)?;
        self.unpack_runtime_fields(module, span, *right, &fields[middle..], output)
    }
}
