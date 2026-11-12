//! Propose labels from original, checked ordinary values for coherent tables.
//! Native source and interval checks independently validate the resulting rows.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;

impl LabelContext<'_, '_> {
    pub(super) fn width(&mut self, span: Span, ty: &Ty) -> Result<usize, CompileError> {
        if let Some(width) = ty.basis_bits() {
            return Ok(width);
        }
        self.compiler
            .charge(self.module, span, ty.tree_size().nodes)?;
        ty.basis_width()
            .filter(|width| *width <= MAX_BITS as u32)
            .map(|width| width as usize)
            .ok_or_else(|| {
                self.compiler.error(
                    self.module,
                    span,
                    ErrorCode::Limit,
                    "nominal basis label exceeds the finite width limit",
                )
            })
    }

    fn same_type(&mut self, span: Span, actual: &Ty, expected: &Ty) -> Result<(), CompileError> {
        if operations::same_port_budgeted(actual, expected, &mut |cells| {
            self.compiler.charge(self.module, span, cells)
        })? {
            Ok(())
        } else {
            Err(self.compiler.error(
                self.module,
                span,
                ErrorCode::TypeMismatch,
                "finite label type differs from its original declared type",
            ))
        }
    }

    pub(super) fn nominal_expression(
        &mut self,
        expr: &BasisExpr,
        env: &BTreeMap<BinderKey, BasisValue>,
        depth: usize,
    ) -> Result<BasisValue, CompileError> {
        let module = self.module;
        let invalid = |compiler: &Compiler<'_>| {
            compiler.error(
                module,
                expr.span,
                ErrorCode::TypeMismatch,
                "invalid original nominal finite label",
            )
        };
        match &expr.kind {
            BasisExprKind::Variant(variant) => {
                let (ty, ordinal) = self.compiler.enum_label(module, variant)?;
                self.width(expr.span, &ty)?;
                Ok(BasisValue {
                    ty,
                    label: ordinal as u16,
                })
            }
            BasisExprKind::Record(record) => {
                let ty = self
                    .compiler
                    .nominal_value_type(module, &record.type_name)?;
                self.width(expr.span, &ty)?;
                let Kind::Nominal(nominal) = &ty.kind else {
                    return Err(invalid(self.compiler));
                };
                let Body::Record(fields) = &nominal.body else {
                    return Err(invalid(self.compiler));
                };
                self.compiler
                    .charge(module, expr.span, fields.len() + record.fields.len() + 1)?;
                let mut values = vec![None; fields.len()];
                for field in &record.fields {
                    let index = self
                        .compiler
                        .record_index(module, nominal, fields, &field.name)?;
                    if values[index].is_some() {
                        return Err(invalid(self.compiler));
                    }
                    let value = finite::evaluate(self, &field.value, env, depth + 1)?;
                    self.same_type(field.span, &value.ty, &fields[index].ty)?;
                    values[index] = Some(value.label);
                }
                let mut label = 0;
                let mut offset = 0;
                for (field, value) in fields.iter().zip(values) {
                    let Some(value) = value else {
                        return Err(invalid(self.compiler));
                    };
                    label |= value << offset;
                    offset += self.width(expr.span, &field.ty)?;
                }
                Ok(BasisValue { ty, label })
            }
            BasisExprKind::Field { receiver, field } => {
                let value = finite::evaluate(self, receiver, env, depth + 1)?;
                let Kind::Nominal(nominal) = &value.ty.kind else {
                    return Err(invalid(self.compiler));
                };
                let Body::Record(fields) = &nominal.body else {
                    return Err(invalid(self.compiler));
                };
                let index = self.compiler.record_index(module, nominal, fields, field)?;
                let mut offset = 0;
                for previous in &fields[..index] {
                    offset += self.width(expr.span, &previous.ty)?;
                }
                let ty = &fields[index].ty;
                let width = self.width(expr.span, ty)?;
                self.compiler
                    .charge(module, expr.span, operations::port_copy_nodes(ty))?;
                Ok(BasisValue {
                    ty: ty.clone(),
                    label: (value.label >> offset) & ((1u16 << width) - 1),
                })
            }
            BasisExprKind::Match(selection) => {
                let value = finite::evaluate(self, &selection.scrutinee, env, depth + 1)?;
                // The complete common judgment already checks exhaustiveness,
                // duplicates, and every arm's type. Select by declaration ordinal.
                for arm in &selection.arms {
                    let (ty, ordinal) = self.compiler.enum_label(module, &arm.label)?;
                    self.same_type(arm.span, &value.ty, &ty)?;
                    if usize::from(value.label) == ordinal {
                        return finite::evaluate(self, &arm.body, env, depth + 1);
                    }
                }
                Err(invalid(self.compiler))
            }
            _ => unreachable!("only ordinary nominal forms dispatch here"),
        }
    }

    pub(super) fn nominal_call(
        &mut self,
        key: Key,
        span: Span,
        args: &[BasisExpr],
        env: &BTreeMap<BinderKey, BasisValue>,
        depth: usize,
    ) -> Result<BasisValue, CompileError> {
        *self
            .nominal_used
            .as_deref_mut()
            .expect("typed nominal evaluation") = true;
        let decl = self.compiler.declarations[&key];
        let FnBody::Basis(body) = &decl.body else {
            unreachable!("only checked classical declarations are deferred");
        };
        self.compiler.charge(self.module, span, args.len() + 1)?;
        let mut values = Vec::with_capacity(args.len());
        for arg in args {
            values.push(finite::evaluate(self, arg, env, depth + 1)?);
        }
        let instance = self.compiler.prepare_instance(
            key,
            BTreeMap::new(),
            BTreeMap::new(),
            BTreeMap::new(),
            self.module,
            span,
        )?;
        let frame = self.compiler.enter_instance(instance, self.module, span)?;
        let module = self
            .compiler
            .source
            .resolution
            .declaration(key)
            .name
            .0
            .clone();
        let result = (|| {
            let (parameters, result_type) = self.compiler.signature(&key)?;
            if values.len() != parameters.len() {
                return Err(self.compiler.error(
                    self.module,
                    span,
                    ErrorCode::Arity,
                    "basis argument count does not match",
                ));
            }
            let mut context = LabelContext {
                compiler: self.compiler,
                module: &module,
                nominal_used: self.nominal_used.as_deref_mut(),
            };
            let mut environment = BTreeMap::new();
            for ((param, expected), actual) in decl.params.iter().zip(&parameters).zip(values) {
                context.same_type(param.span, &actual.ty, expected)?;
                environment.extend(context.compiler.bind_basis_pattern(
                    &module,
                    &param.pattern,
                    expected,
                    actual.label,
                )?);
            }
            let result = finite::evaluate(&mut context, body, &environment, depth + 1)?;
            context.same_type(body.span, &result.ty, &result_type)?;
            Ok(result)
        })();
        self.compiler.leave_instance(frame);
        result
    }
}
