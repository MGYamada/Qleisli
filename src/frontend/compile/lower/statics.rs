//! Execute original closed static branches and explicit carry folds.
//! The common judgment still checks every arm and zero-count body. This
//! untrusted emitter selects operations, never replaces their native gates.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.

use super::*;
use crate::frontend::check::plans::{
    BodyStaticKind, BodyStaticOriginal, BodyStaticPlan, original_body_static,
};

fn plan_error(
    compiler: &Compiler<'_>,
    work: &mut usize,
    module: &str,
    span: Span,
    message: &'static str,
) -> Result<CompileError, CompileError> {
    compiler.charge_at(work, module, span, message.len() + 1)?;
    Ok(compiler.error(module, span, ErrorCode::TypeMismatch, message))
}

fn folded_binding(binding: &Binding) -> Binding {
    if binding.as_ref().is_some_and(Value::owns_quantum) {
        binding.hidden()
    } else {
        binding.clone()
    }
}

fn pattern_storage(pattern: &Pattern) -> usize {
    match &pattern.kind {
        PatternKind::Name(name) => name.text.len().saturating_mul(4).saturating_add(8),
        PatternKind::Wildcard => 1,
        PatternKind::Tuple(fields) => fields.iter().fold(fields.len() + 1, |size, field| {
            size.saturating_add(pattern_storage(field))
        }),
    }
}

impl Lowerer<'_, '_> {
    pub(super) fn static_refusal(
        &mut self,
        module: &str,
        span: Span,
        code: ErrorCode,
        message: &'static str,
    ) -> Result<CompileError, CompileError> {
        self.compiler.charge(module, span, message.len() + 1)?;
        Ok(self.error(module, span, code, message))
    }

    /// Copy only charged immutable handles/keys out of the exact original plan.
    /// A current diagnostic owner or an equal-looking AST is not its identity.
    pub(super) fn static_plan<T>(
        &mut self,
        module: &str,
        original: BodyStaticOriginal<'_>,
        capture: impl FnOnce(&Compiler<'_>, &mut usize, &BodyStaticPlan) -> Result<T, CompileError>,
    ) -> Result<T, CompileError> {
        let span = match original {
            BodyStaticOriginal::Expression(value) => value.span,
            BodyStaticOriginal::Natural(value) => value.span,
            BodyStaticOriginal::Operation(value) => value.span,
        };
        let mut work = self.compiler.work;
        let result = (|| {
            self.compiler
                .charge_at(&mut work, module, span, module.len() + 16)?;
            let lookup = self.compiler.locals();
            let node = match original {
                BodyStaticOriginal::Expression(value) => lookup.try_node_id_expr(value),
                BodyStaticOriginal::Natural(value) => lookup.try_node_id_natural(value),
                BodyStaticOriginal::Operation(value) => lookup.try_node_id_static_op(value),
            };
            let owner = node.and_then(|node| {
                self.compiler
                    .source
                    .resolution
                    .try_declaration(node.definition())
                    .filter(|declaration| declaration.name.0 == module)
                    .map(|declaration| (node.definition(), declaration.module))
            });
            let Some((owner, original_module)) = owner else {
                let message = "static body lacks its original owner and module association";
                self.compiler
                    .charge_at(&mut work, module, span, message.len() + 1)?;
                return Err(self.error(module, span, ErrorCode::TypeMismatch, message));
            };
            let plan = original_body_static(
                &self.compiler.source,
                &lookup,
                owner,
                original_module,
                original,
                &mut |at, cells| self.compiler.charge_at(&mut work, module, at, cells),
                &|at, message| self.error(module, at, ErrorCode::TypeMismatch, message),
            )?;
            capture(self.compiler, &mut work, plan)
        })();
        self.compiler.work = work;
        result
    }

    pub(super) fn static_natural_value(
        &mut self,
        module: &str,
        original: &Natural,
    ) -> Result<u32, CompileError> {
        let (environment, value) = self.static_plan(
            module,
            BodyStaticOriginal::Natural(original),
            |compiler, work, plan| {
                compiler.charge_at(work, module, original.span, 2)?;
                let BodyStaticKind::Natural { value } = &plan.kind else {
                    return Err(plan_error(
                        compiler,
                        work,
                        module,
                        original.span,
                        "static count lacks its original natural plan",
                    )?);
                };
                Ok((Arc::clone(&plan.environment), Arc::clone(value)))
            },
        )?;
        self.compiler.evaluate_plan_natural(&value, &environment)
    }

    pub(super) fn static_binding(
        &mut self,
        module: &str,
        name: &Ident,
        original: &Natural,
    ) -> Result<(), CompileError> {
        let (environment, value) = self.static_plan(
            module,
            BodyStaticOriginal::Natural(original),
            |compiler, work, plan| {
                compiler.charge_at(work, module, original.span, name.text.len() + 12)?;
                let BodyStaticKind::Binding { key, value } = &plan.kind else {
                    return Err(plan_error(
                        compiler,
                        work,
                        module,
                        original.span,
                        "static binding lacks its original initializer plan",
                    )?);
                };
                if compiler.locals().try_binder(name) != Some(key.id) {
                    return Err(plan_error(
                        compiler,
                        work,
                        module,
                        name.span,
                        "static binding differs from its original lexical binder",
                    )?);
                }
                Ok((Arc::clone(&plan.environment), Arc::clone(value)))
            },
        )?;
        // An unused initializer is checked too. References deliberately retain
        // the original alias walk rather than trusting a replacement value map.
        self.compiler.evaluate_plan_natural(&value, &environment)?;
        Ok(())
    }

    pub(super) fn static_branch(
        &mut self,
        module: &str,
        original: &Expr,
        env: &mut Env,
    ) -> Result<Value, CompileError> {
        let (environment, left, comparison, right) = self.static_plan(
            module,
            BodyStaticOriginal::Expression(original),
            |compiler, work, plan| {
                compiler.charge_at(work, module, original.span, 4)?;
                let BodyStaticKind::Predicate {
                    left,
                    comparison,
                    right,
                } = &plan.kind
                else {
                    return Err(plan_error(
                        compiler,
                        work,
                        module,
                        original.span,
                        "static branch lacks its original predicate plan",
                    )?);
                };
                Ok((
                    Arc::clone(&plan.environment),
                    Arc::clone(left),
                    *comparison,
                    Arc::clone(right),
                ))
            },
        )?;
        let ExprKind::StaticIf {
            then_branch,
            else_branch,
            ..
        } = &original.kind
        else {
            unreachable!("original predicate accessor checked the expression kind")
        };
        let left = self.compiler.evaluate_plan_natural(&left, &environment)?;
        let right = self.compiler.evaluate_plan_natural(&right, &environment)?;
        let truth = match comparison {
            Compare::Eq => left == right,
            Compare::Ne => left != right,
            Compare::Lt => left < right,
            Compare::Le => left <= right,
            Compare::Gt => left > right,
            Compare::Ge => left >= right,
        };
        let selected = if truth { then_branch } else { else_branch };
        self.block(module, selected, env)
    }

    fn carry_type(
        &mut self,
        module: &str,
        span: Span,
        value: &Value,
        expected: &Ty,
    ) -> Result<(), CompileError> {
        self.compiler.charge(
            module,
            span,
            value
                .tree_size()
                .nodes
                .saturating_add(expected.tree_size().nodes)
                .saturating_add(4),
        )?;
        let actual = value.ty();
        let mut work = self.compiler.work;
        let same = super::super::operations::same_port_budgeted(&actual, expected, &mut |cells| {
            self.compiler.charge_at(&mut work, module, span, cells)
        });
        self.compiler.work = work;
        if !same? {
            return Err(self.static_refusal(
                module,
                span,
                ErrorCode::TypeMismatch,
                "static fold must preserve the complete exact carry type",
            )?);
        }
        Ok(())
    }

    pub(super) fn static_fold(
        &mut self,
        module: &str,
        original: &Expr,
        env: &mut Env,
    ) -> Result<Value, CompileError> {
        let (owner, environment, index, start, end, carry_type) = self.static_plan(
            module,
            BodyStaticOriginal::Expression(original),
            |compiler, work, plan| {
                let BodyStaticKind::Fold {
                    index,
                    start,
                    end,
                    carry_type,
                } = &plan.kind
                else {
                    return Err(plan_error(
                        compiler,
                        work,
                        module,
                        original.span,
                        "static fold lacks its original carry and range plan",
                    )?);
                };
                compiler.charge_at(work, module, original.span, index.name.len() + 6)?;
                Ok((
                    plan.owner,
                    Arc::clone(&plan.environment),
                    index.clone(),
                    Arc::clone(start),
                    Arc::clone(end),
                    Arc::clone(carry_type),
                ))
            },
        )?;
        let ExprKind::StaticFold {
            quantum,
            index: original_index,
            carry,
            initial,
            body,
            ..
        } = &original.kind
        else {
            unreachable!("original fold accessor checked the expression kind")
        };
        self.compiler.charge(module, original.span, 8)?;
        if self.compiler.locals().try_binder(original_index) != Some(index.id) {
            return Err(self.static_refusal(
                module,
                original_index.span,
                ErrorCode::TypeMismatch,
                "static fold differs from its original index binder",
            )?);
        }
        let start = self.compiler.evaluate_plan_natural(&start, &environment)?;
        let end = self.compiler.evaluate_plan_natural(&end, &environment)?;
        let Some(iterations) = end.checked_sub(start) else {
            return Err(self.static_refusal(
                module,
                original.span,
                ErrorCode::Contract,
                "static fold requires start <= end",
            )?);
        };
        let expected = self
            .compiler
            .close_body_type(owner, &carry_type, initial.span)?;
        // The initializer remains an ordinary original expression, evaluated
        // once even for an empty interval. Its consumed owners stay consumed.
        let mut value = self.expr(module, initial, env)?;
        self.carry_type(module, initial.span, &value, &expected)?;
        if value.owns_quantum() != *quantum {
            return Err(self.static_refusal(
                module,
                original.span,
                ErrorCode::TypeMismatch,
                "static fold category differs from its exact carry ownership",
            )?);
        }
        let iterations = match usize::try_from(iterations) {
            Ok(iterations) => iterations,
            Err(_) => {
                return Err(self.static_refusal(
                    module,
                    original.span,
                    ErrorCode::Limit,
                    "static fold range exceeds usize",
                )?);
            }
        };
        self.compiler.charge(module, original.span, iterations)?;
        for current in start..end {
            // The source frame is never replaced by the iteration's scope.
            // Mixed products containing any Q owner are hidden as a whole.
            let frame_storage = env
                .iter()
                .fold(env_size(env) + env.len() + 1, |size, (key, _)| {
                    size.saturating_add(key.name.len())
                });
            self.compiler.charge(module, body.span, frame_storage)?;
            let mut local: Env = env
                .iter()
                .map(|(key, binding)| (key.clone(), folded_binding(binding)))
                .collect();
            self.compiler.charge(
                module,
                carry.span,
                value
                    .tree_size()
                    .nodes
                    .saturating_mul(2)
                    .saturating_add(pattern_storage(carry)),
            )?;
            self.bind(module, carry, value, &mut local, &mut BTreeSet::new())?;
            let frame = self
                .compiler
                .push_natural_binding(&index, current, original_index.span)?;
            let result = self.block(module, body, &mut local);
            self.compiler.restore_natural_binding(frame);
            value = result?;
            self.carry_type(module, body.result.span, &value, &expected)?;
            let local_storage = local
                .iter()
                .fold(env_size(&local) + local.len() + 1, |size, (key, _)| {
                    size.saturating_add(key.name.len())
                });
            self.compiler.charge(module, body.span, local_storage)?;
            self.no_owned_bindings(module, body.result.span, &local, std::iter::empty())?;
        }
        Ok(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn static_fold_frame_hides_zero_width_and_mixed_quantum_owners() {
        for value in [
            Value::quantum(0, Ty::unit()),
            Value::quantum(1, Ty::bits(0)),
            Value::pair(Value::EmptyBits, Value::quantum(2, Ty::unit())),
        ] {
            let original = Binding::Live(value);
            assert_eq!(folded_binding(&original), Binding::Hidden { quantum: true });
            assert!(original.as_ref().unwrap().owns_quantum());
        }
        for binding in [
            Binding::Consumed,
            Binding::Hidden { quantum: false },
            Binding::Live(Value::EmptyBits),
            Binding::Live(Value::bits(vec![ClassicalId(7)])),
        ] {
            assert_eq!(folded_binding(&binding), binding);
        }
    }
}
