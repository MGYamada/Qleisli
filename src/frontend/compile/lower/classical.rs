//! Ordinary lowering of the original total classical expression body.
// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
use super::*;
use crate::frontend::ordinary::{self, Boolean, OperandFailure, RuntimeExpression};

impl Lowerer<'_, '_> {
    pub(super) fn read_name(
        &mut self,
        module: &str,
        name: &Ident,
        env: &mut Env,
    ) -> Result<Value, CompileError> {
        let binding = self
            .compiler
            .locals
            .local_key(name)
            .and_then(|key| env.get_mut(key))
            .ok_or_else(|| {
                self.error(
                    module,
                    name.span,
                    ErrorCode::UnknownName,
                    format!("unknown value `{}`", name.text),
                )
            })?;
        let value = match binding {
            Binding::Live(value) => value,
            Binding::Consumed => {
                return Err(self.error(
                    module,
                    name.span,
                    ErrorCode::Ownership,
                    format!(
                        "quantum ownership `{}` has already been consumed",
                        name.text
                    ),
                ));
            }
            Binding::Hidden { quantum } => {
                let repair = if *quantum {
                    "include it in the source data with `join` and access it through the data binder of three-argument `with_computed`, or restructure the body"
                } else {
                    "use a closed classical expression or restructure the body"
                };
                return Err(self.error(
                    module,
                    name.span,
                    ErrorCode::Ownership,
                    format!(
                        "with_computed body cannot capture outer binding `{}`; {repair}",
                        name.text
                    ),
                ));
            }
        };
        self.compiler
            .charge(module, name.span, value.tree_size().nodes)?;
        Ok(if value.owns_quantum() {
            binding.take().expect("live value")
        } else {
            value.clone()
        })
    }

    pub(super) fn boolean<X>(
        &mut self,
        module: &str,
        span: Span,
        operation: Boolean,
        operands: impl ExactSizeIterator<Item = X>,
        env: &mut Env,
        mut evaluate: impl FnMut(&mut Self, X, &mut Env) -> Result<Value, CompileError>,
    ) -> Result<Value, CompileError> {
        let values = ordinary::evaluate(
            operation,
            operands,
            &mut (&mut *self, &mut *env),
            |(lowerer, env), operand| evaluate(lowerer, operand, env),
            Value::ty,
            |(lowerer, _), failure| {
                let message = match failure {
                    OperandFailure::Arity { expected, actual } => {
                        format!("Boolean operation requires {expected} operands, found {actual}")
                    }
                    OperandFailure::Type(ty) if operation == Boolean::Not => format!(
                        "not requires a Bit operand: expected `Bit`, found `{}`",
                        ty.runtime()
                    ),
                    OperandFailure::Type(ty) => format!(
                        "and/xor require Bit operands: expected `Bit`, found `{}`",
                        ty.runtime()
                    ),
                };
                lowerer.error(module, span, ErrorCode::TypeMismatch, message)
            },
        )?;
        let inputs = values
            .into_iter()
            .map(|value| match value {
                Value::Classical(id) => Ok(id),
                _ => Err(self.error(
                    module,
                    span,
                    ErrorCode::InvalidIr,
                    "Boolean operand lost its classical representation",
                )),
            })
            .collect::<Result<Vec<_>, _>>()?;
        let output = self.raw.boolean(operation, &inputs).map_err(|failure| {
            self.error(module, span, ErrorCode::InvalidIr, failure.to_string())
        })?;
        Ok(Value::Classical(output))
    }

    pub(super) fn classical_expr(
        &mut self,
        module: &str,
        expr: &BasisExpr,
        env: &mut Env,
    ) -> Result<Value, CompileError> {
        self.compiler.tick(module, expr.span)?;
        if self.depth >= MAX_DEPTH {
            return Err(self.error(
                module,
                expr.span,
                ErrorCode::Limit,
                "expression expansion exceeds the initial depth limit",
            ));
        }
        self.depth += 1;
        let first_operation = self.raw.operations.len();
        let result = self.classical_inner(module, expr, env);
        self.depth -= 1;
        let value = result?;
        for index in first_operation..self.raw.operations.len() {
            self.operation_sources
                .entry(vec![index])
                .or_insert_with(|| (module.to_owned(), expr.span));
        }
        self.compiler
            .check_tree(module, expr.span, value.tree_size())?;
        Ok(value)
    }

    fn classical_inner(
        &mut self,
        module: &str,
        expr: &BasisExpr,
        env: &mut Env,
    ) -> Result<Value, CompileError> {
        match ordinary::runtime_expression(expr) {
            RuntimeExpression::Name(name) => self.read_name(module, name, env),
            RuntimeExpression::Unit => Ok(Value::Unit),
            RuntimeExpression::Tuple(fields) => {
                self.compiler.charge(module, expr.span, fields.len())?;
                Ok(Value::tuple(
                    fields
                        .iter()
                        .map(|field| self.classical_expr(module, field, env))
                        .collect::<Result<_, _>>()?,
                ))
            }
            RuntimeExpression::Boolean { operation, inputs } => {
                self.compiler.charge(module, expr.span, operation.arity())?;
                let operands: Vec<_> = inputs.into_iter().flatten().collect();
                self.boolean(
                    module,
                    expr.span,
                    operation,
                    operands.into_iter(),
                    env,
                    |lowerer, operand, env| lowerer.classical_expr(module, operand, env),
                )
            }
            RuntimeExpression::Call { callee, args } => {
                self.compiler.charge(module, expr.span, args.len())?;
                let target = self.compiler.resolve(module, callee)?;
                let values = args
                    .iter()
                    .map(|arg| self.classical_expr(module, arg, env))
                    .collect::<Result<Vec<_>, _>>()?;
                let Callee::User(key) = target else {
                    return Err(self.error(
                        module,
                        callee.span,
                        ErrorCode::TypeMismatch,
                        "classical expressions call classical functions only",
                    ));
                };
                self.call_user(
                    &key,
                    values,
                    Some(CallSite {
                        module,
                        span: expr.span,
                        args: CallArguments::Classical(args),
                    }),
                )
            }
        }
    }
}
