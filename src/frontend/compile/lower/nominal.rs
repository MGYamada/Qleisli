//! Untrusted ordinary enum construction and selection behind the source transport gate.
//! No ordinary enum input, native request, or accepted handle is introduced here.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;
use crate::frontend::ast::{MatchArm, VariantValue};
use crate::frontend::ordinary::Boolean;
use crate::frontend::types::nominal::Body;

#[cfg(test)]
mod tests;

impl Lowerer<'_, '_> {
    /// Resolve the original constructor/label occurrence through the common
    /// source table. Spelling, width or a caller-supplied type is not authority.
    pub(super) fn enum_label(
        &mut self,
        module: &str,
        value: &VariantValue,
    ) -> Result<(Ty, usize), CompileError> {
        self.compiler.tick(module, value.type_name.span)?;
        let ResolvedUse::Global(Target::Type(id)) =
            self.compiler.locals().usage(&value.type_name).target
        else {
            return Err(self.error(
                module,
                value.type_name.span,
                ErrorCode::TypeMismatch,
                "enum label requires its original concrete type occurrence",
            ));
        };
        let nominals = std::sync::Arc::clone(&self.compiler.source.nominals);
        let original = nominals.get(&id).ok_or_else(|| {
            self.error(
                module,
                value.type_name.span,
                ErrorCode::TypeMismatch,
                "enum label lost its original nominal declaration",
            )
        })?;
        let owner = self.compiler.current_instance_owner().ok_or_else(|| {
            self.error(
                module,
                value.type_name.span,
                ErrorCode::TypeMismatch,
                "enum label lacks its active original function",
            )
        })?;
        let ty = self
            .compiler
            .close_body_type(owner, original, value.type_name.span)?;
        let Kind::Nominal(nominal) = &ty.kind else {
            return Err(self.error(
                module,
                value.type_name.span,
                ErrorCode::TypeMismatch,
                "enum label requires a nominal type",
            ));
        };
        let Body::Enum(labels) = &nominal.body else {
            return Err(self.error(
                module,
                value.type_name.span,
                ErrorCode::Unsupported,
                "ordinary record execution requires its typed native transport",
            ));
        };
        self.compiler.charge(
            module,
            value.variant.span,
            total_size(labels.iter().map(|name| {
                name.len()
                    .saturating_add(value.variant.text.len())
                    .saturating_add(1)
            })),
        )?;
        let ordinal = labels
            .iter()
            .position(|label| *label == value.variant.text)
            .ok_or_else(|| {
                self.error(
                    module,
                    value.variant.span,
                    ErrorCode::TypeMismatch,
                    "enum label is absent from its original declaration",
                )
            })?;
        Ok((ty, ordinal))
    }

    pub(super) fn variant_value(
        &mut self,
        module: &str,
        span: Span,
        value: &VariantValue,
    ) -> Result<Value, CompileError> {
        let (ty, ordinal) = self.enum_label(module, value)?;
        self.note_nominal(&ty, module, span)?;
        let width = ty
            .basis_width()
            .filter(|width| *width <= MAX_BITS as u32)
            .ok_or_else(|| {
                self.error(
                    module,
                    span,
                    ErrorCode::Limit,
                    "enum tag exceeds finite storage capacity",
                )
            })? as usize;
        // The ordinal comes from the actual nonempty ordered label list. No
        // physical code outside that logical domain is constructed.
        self.compiler
            .charge(module, span, width.saturating_mul(3).saturating_add(1))?;
        let mut ids = Vec::with_capacity(width);
        self.raw.operations.reserve(width);
        for axis in 0..width {
            let output = self.classical();
            self.raw.operations.push(RawOp::ClassicalConst {
                value: ((ordinal >> axis) & 1) != 0,
                output,
            });
            ids.push(output);
        }
        Ok(Value::Enumeration(ty, ids))
    }

    pub(super) fn match_value<A>(
        &mut self,
        module: &str,
        span: Span,
        scrutinee: Value,
        arms: &[MatchArm<A>],
        env: &mut Env,
        evaluate: fn(&mut Self, &str, &A, &mut Env) -> Result<Value, CompileError>,
    ) -> Result<Value, CompileError> {
        let Value::Enumeration(ty, ids) = scrutinee else {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "ordinary match requires an ordinary enum value",
            ));
        };
        let Kind::Nominal(nominal) = &ty.kind else {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "enum storage lost its original type",
            ));
        };
        let Body::Enum(labels) = &nominal.body else {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "ordinary match requires an enum",
            ));
        };
        if labels.is_empty()
            || arms.len() != labels.len()
            || ty.basis_width() != u32::try_from(ids.len()).ok()
        {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "match labels and enum tag coordinates must retain the complete original domain",
            ));
        }
        self.compiler
            .charge(module, span, arms.len().saturating_mul(3).saturating_add(1))?;
        let mut plan = Vec::with_capacity(arms.len());
        let mut seen = BTreeSet::new();
        for arm in arms {
            let (label_ty, ordinal) = self.enum_label(module, &arm.label)?;
            let same =
                super::super::operations::same_port_budgeted(&ty, &label_ty, &mut |cells| {
                    self.compiler.charge(module, arm.span, cells)
                })?;
            if !same || !seen.insert(ordinal) {
                return Err(self.error(
                    module,
                    arm.span,
                    ErrorCode::TypeMismatch,
                    "match labels must name every original enum variant exactly once",
                ));
            }
            plan.push((ordinal, arm));
        }
        self.match_arms(module, span, &ids, &plan, env, evaluate)
    }

    fn match_arms<A>(
        &mut self,
        module: &str,
        span: Span,
        ids: &[ClassicalId],
        plan: &[(usize, &MatchArm<A>)],
        env: &mut Env,
        evaluate: fn(&mut Self, &str, &A, &mut Env) -> Result<Value, CompileError>,
    ) -> Result<Value, CompileError> {
        let ((ordinal, first), rest) = plan.split_first().ok_or_else(|| {
            self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "match requires a nonempty enum",
            )
        })?;
        if rest.is_empty() {
            // All values in this producer originate at constructors, ordinary
            // copies or branches. The last arm is justified only for that
            // valid-ordinal domain; native typed replay is still absent.
            return evaluate(self, module, &first.body, env);
        }
        self.compiler.tick(module, first.span)?;
        self.compiler
            .charge(module, span, ids.len().saturating_mul(4).saturating_add(1))?;
        let mut condition = None;
        for (axis, input) in ids.iter().copied().enumerate() {
            let bit = if (*ordinal >> axis) & 1 != 0 {
                input
            } else {
                self.raw
                    .boolean(Boolean::Not, &[input])
                    .map_err(|failure| {
                        self.error(module, span, ErrorCode::InvalidIr, failure.to_string())
                    })?
            };
            condition = Some(match condition {
                None => bit,
                Some(previous) => {
                    self.raw
                        .boolean(Boolean::And, &[previous, bit])
                        .map_err(|failure| {
                            self.error(module, span, ErrorCode::InvalidIr, failure.to_string())
                        })?
                }
            });
        }
        let condition = condition.ok_or_else(|| {
            self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "multiple enum variants cannot use empty tag storage",
            )
        })?;
        if self.depth >= MAX_DEPTH {
            return Err(self.error(
                module,
                span,
                ErrorCode::Limit,
                "match lowering exceeds the initial depth limit",
            ));
        }
        self.depth += 1;
        let result = self.branch_evaluate(
            module,
            span,
            condition,
            env,
            |lower, env| evaluate(lower, module, &first.body, env),
            |lower, env| lower.match_arms(module, span, ids, rest, env, evaluate),
        );
        self.depth -= 1;
        result
    }
}
