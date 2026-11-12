//! Propose labels from original, checked ordinary values for coherent tables.
//! Native source and interval checks independently validate the resulting rows.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;

impl LabelContext<'_, '_> {
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

impl finite::NominalContext for LabelContext<'_, '_> {
    fn enum_label(
        &mut self,
        value: &crate::frontend::ast::VariantValue,
    ) -> Result<(Ty, usize), CompileError> {
        self.compiler.enum_label(self.module, value)
    }

    fn nominal_type(&mut self, name: &Ident) -> Result<Ty, CompileError> {
        self.compiler.nominal_value_type(self.module, name)
    }

    fn record_index(
        &mut self,
        nominal: &crate::frontend::types::nominal::Nominal<u32>,
        fields: &[crate::frontend::types::nominal::Field<u32>],
        name: &Ident,
    ) -> Result<usize, CompileError> {
        self.compiler
            .record_index(self.module, nominal, fields, name)
    }

    fn charge(&mut self, span: Span, cells: usize) -> Result<(), CompileError> {
        self.compiler.charge(self.module, span, cells)
    }

    fn copy_type(&mut self, span: Span, ty: &Ty) -> Result<Ty, CompileError> {
        self.charge(span, operations::port_copy_nodes(ty))?;
        Ok(ty.clone())
    }

    fn invalid_nominal(&self, span: Span) -> CompileError {
        self.compiler.error(
            self.module,
            span,
            ErrorCode::TypeMismatch,
            "invalid original nominal finite label",
        )
    }

    fn width(&mut self, span: Span, ty: &Ty) -> Result<usize, CompileError> {
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
}
