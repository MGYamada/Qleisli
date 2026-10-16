//! Original checked Nat plans evaluated for an untrusted finite proposal.
//!
//! An unresolved formal or fold index remains deferred. Neither that result nor
//! a concrete value supplies source preservation or independent acceptance.
//! Ordinary nodes use checked u32 arithmetic; checked helper templates retain
//! their existing signed i128 arithmetic and nonnegative u32 result contract.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.

use super::{CompileError, ErrorCode, MAX_DEPTH};
use crate::frontend::ast::{Compare, Span};
use crate::frontend::check::Linear;
use crate::frontend::check::plans::{
    NaturalBindingPlan, ResolvedNatural, ResolvedNaturalKind, ResolvedReference, StaticEnvironment,
};
use crate::frontend::resolve::Target;
use crate::frontend::resolve::locals::{BinderKey, ResolvedUse};
use std::collections::BTreeMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum NaturalValue {
    Closed(u32),
    /// No concrete instance has discharged this expression.
    Deferred,
}

/// `original` and `environment` must come from the validated original plan
/// collection. The caller checks the complete actual maps before calling this
/// adapter and supplies its existing shared work accounting to both callbacks.
/// `helper_call` records a real visit, including visits with deferred arguments;
/// it must not import a different adapter's limits or confer acceptance.
pub(super) fn evaluate(
    original: &ResolvedNatural,
    environment: &StaticEnvironment,
    values: &BTreeMap<BinderKey, u32>,
    charge: &mut impl FnMut(Span, usize) -> Result<(), CompileError>,
    helper_call: &mut impl FnMut(Span) -> Result<(), CompileError>,
    error: &impl Fn(Span, ErrorCode, &'static str) -> CompileError,
) -> Result<NaturalValue, CompileError> {
    Evaluator {
        environment,
        values,
        active: Vec::new(),
        charge,
        helper_call,
        error,
    }
    .natural(original, 1)
}

/// Plain static arguments retain their original reference rather than a
/// fabricated natural AST. They use precisely the same original alias walk.
pub(super) fn evaluate_reference(
    reference: &ResolvedReference,
    span: Span,
    environment: &StaticEnvironment,
    values: &BTreeMap<BinderKey, u32>,
    charge: &mut impl FnMut(Span, usize) -> Result<(), CompileError>,
    helper_call: &mut impl FnMut(Span) -> Result<(), CompileError>,
    error: &impl Fn(Span, ErrorCode, &'static str) -> CompileError,
) -> Result<NaturalValue, CompileError> {
    let mut evaluator = Evaluator {
        environment,
        values,
        active: Vec::new(),
        charge,
        helper_call,
        error,
    };
    (evaluator.charge)(span, 1)?;
    evaluator.reference(reference, span, 1)
}

struct Evaluator<'a, C, H, E> {
    environment: &'a StaticEnvironment,
    values: &'a BTreeMap<BinderKey, u32>,
    active: Vec<&'a BinderKey>,
    charge: &'a mut C,
    helper_call: &'a mut H,
    error: &'a E,
}

impl<C, H, E> Evaluator<'_, C, H, E>
where
    C: FnMut(Span, usize) -> Result<(), CompileError>,
    H: FnMut(Span) -> Result<(), CompileError>,
    E: Fn(Span, ErrorCode, &'static str) -> CompileError,
{
    fn fail<T>(
        &mut self,
        span: Span,
        code: ErrorCode,
        message: &'static str,
    ) -> Result<T, CompileError> {
        // Reserve diagnostic storage before the caller constructs its error.
        (self.charge)(span, message.len().saturating_add(1))?;
        Err((self.error)(span, code, message))
    }

    fn same_key(
        &mut self,
        left: &BinderKey,
        right: &BinderKey,
        span: Span,
    ) -> Result<bool, CompileError> {
        (self.charge)(
            span,
            left.name
                .len()
                .saturating_add(right.name.len())
                .saturating_add(1),
        )?;
        Ok(left == right)
    }

    // A borrowed scan charges every comparison before it runs and never clones
    // keys or allocates a name-based replacement map. Exact BinderKey identity
    // includes the original owner and ordinal, even when names are identical.
    fn binding<'b, T>(
        &mut self,
        bindings: &'b BTreeMap<BinderKey, T>,
        key: &BinderKey,
        span: Span,
    ) -> Result<Option<(&'b BinderKey, &'b T)>, CompileError> {
        // Bound the complete borrowed traversal before creating its iterator.
        (self.charge)(span, bindings.len().saturating_add(1))?;
        for (candidate, value) in bindings {
            if self.same_key(candidate, key, span)? {
                return Ok(Some((candidate, value)));
            }
        }
        Ok(None)
    }

    fn natural(
        &mut self,
        original: &ResolvedNatural,
        depth: usize,
    ) -> Result<NaturalValue, CompileError> {
        let span = original.span;
        (self.charge)(span, 1)?;
        if depth > MAX_DEPTH {
            return self.fail(
                span,
                ErrorCode::Limit,
                "concrete natural exceeds finite depth limit",
            );
        }
        if original.node.definition() != self.environment.owner {
            return self.fail(
                span,
                ErrorCode::TypeMismatch,
                "foreign original natural occurrence",
            );
        }
        match &original.kind {
            ResolvedNaturalKind::Number(number) => self.number(*number, span),
            ResolvedNaturalKind::Name(reference) => self.reference(reference, span, depth),
            ResolvedNaturalKind::Helper {
                callee,
                template,
                arguments,
            } => {
                if callee.site.definition() != self.environment.owner || callee.local.is_some() {
                    return self.fail(
                        span,
                        ErrorCode::TypeMismatch,
                        "invalid original Nat helper callee",
                    );
                }
                let ResolvedUse::Global(Target::Declaration(owner)) = callee.target else {
                    return self.fail(
                        span,
                        ErrorCode::TypeMismatch,
                        "Nat helper requires an original declaration",
                    );
                };
                if template.parameters.len() != arguments.len() {
                    return self.fail(
                        span,
                        ErrorCode::Arity,
                        "original Nat helper argument arity mismatch",
                    );
                }
                (self.charge)(span, template.parameters.len().saturating_add(1))?;
                for (ordinal, parameter) in template.parameters.iter().enumerate() {
                    (self.charge)(span, 1)?;
                    if parameter.id.definition() != owner {
                        return self.fail(
                            span,
                            ErrorCode::TypeMismatch,
                            "foreign original Nat helper formal",
                        );
                    }
                    (self.charge)(span, ordinal)?;
                    for previous in &template.parameters[..ordinal] {
                        if self.same_key(previous, parameter, span)? {
                            return self.fail(
                                span,
                                ErrorCode::TypeMismatch,
                                "duplicate original Nat helper formal",
                            );
                        }
                    }
                }
                (self.helper_call)(span)?;
                // Evaluate every actual in original positional order. A later
                // concrete counterexample is retained after an earlier defer.
                (self.charge)(span, arguments.len())?;
                let mut actuals = Vec::with_capacity(arguments.len());
                let mut deferred = false;
                for argument in arguments {
                    let value = self.natural(argument, depth + 1)?;
                    deferred |= value == NaturalValue::Deferred;
                    actuals.push(value);
                }
                (self.charge)(span, template.requirements.len().saturating_add(1))?;
                for (left, comparison, right) in &template.requirements {
                    (self.charge)(span, 1)?;
                    let left = self.linear(left, &template.parameters, &actuals, span)?;
                    let right = self.linear(right, &template.parameters, &actuals, span)?;
                    match (left, right) {
                        (Some(left), Some(right)) => {
                            if !compare(left, *comparison, right) {
                                return self.fail(
                                    span,
                                    ErrorCode::Contract,
                                    "concrete Nat helper premise is false",
                                );
                            }
                        }
                        _ => deferred = true,
                    }
                }
                let result = self.linear(&template.result, &template.parameters, &actuals, span)?;
                // Even a constant normalized result cannot erase a deferred
                // original argument or its still-undischarged premise.
                match result {
                    Some(result) => {
                        let result = self.number(result, span)?;
                        Ok(if deferred {
                            NaturalValue::Deferred
                        } else {
                            result
                        })
                    }
                    None => Ok(NaturalValue::Deferred),
                }
            }
            ResolvedNaturalKind::Add(left, right)
            | ResolvedNaturalKind::Sub(left, right)
            | ResolvedNaturalKind::Mul(left, right) => {
                let left = self.natural(left, depth + 1)?;
                let right = self.natural(right, depth + 1)?;
                let (NaturalValue::Closed(left), NaturalValue::Closed(right)) = (left, right)
                else {
                    return Ok(NaturalValue::Deferred);
                };
                let result = match &original.kind {
                    ResolvedNaturalKind::Add(..) => left.checked_add(right),
                    ResolvedNaturalKind::Sub(..) => left.checked_sub(right),
                    _ => left.checked_mul(right),
                };
                match result {
                    Some(result) => Ok(NaturalValue::Closed(result)),
                    None => self.arithmetic(span),
                }
            }
        }
    }

    fn reference(
        &mut self,
        reference: &ResolvedReference,
        span: Span,
        depth: usize,
    ) -> Result<NaturalValue, CompileError> {
        (self.charge)(span, 1)?;
        let Some(key) = &reference.local else {
            return self.fail(
                span,
                ErrorCode::TypeMismatch,
                "natural name requires an original local binding",
            );
        };
        if reference.site.definition() != self.environment.owner
            || key.id.definition() != self.environment.owner
            || reference.target != ResolvedUse::Local(key.id)
        {
            return self.fail(
                span,
                ErrorCode::TypeMismatch,
                "foreign or mismatched original natural binding",
            );
        }
        let environment = self.environment;
        let Some((original_key, _)) = self.binding(&environment.naturals, key, span)? else {
            return self.fail(
                span,
                ErrorCode::TypeMismatch,
                "original binding is not a natural in this environment",
            );
        };
        let local = self.binding(&environment.local_naturals, original_key, span)?;
        let Some((_, local)) = local else {
            let values = self.values;
            return Ok(match self.binding(values, original_key, span)? {
                Some((_, value)) => NaturalValue::Closed(*value),
                None => NaturalValue::Deferred,
            });
        };
        (self.charge)(span, self.active.len())?;
        for index in 0..self.active.len() {
            let active = self.active[index];
            if self.same_key(active, original_key, span)? {
                return self.fail(
                    span,
                    ErrorCode::RecursiveCall,
                    "cyclic original natural initializer",
                );
            }
        }
        let grow = self.active.len() == self.active.capacity();
        let storage = if grow {
            // Reserve the new buffer, movement of every existing reference,
            // and the pushed cell before any possible reallocation.
            self.active.len().saturating_mul(2).saturating_add(2)
        } else {
            1
        };
        (self.charge)(span, storage)?;
        if grow {
            self.active.reserve_exact(1);
        }
        self.active.push(original_key);
        let result = match local {
            // Actual maps cannot stand in for evaluating an original alias.
            NaturalBindingPlan::Initializer(initializer) => self.natural(initializer, depth + 1),
            NaturalBindingPlan::FoldIndex { start, end } => (|| {
                let start = self.natural(start, depth + 1)?;
                let end = self.natural(end, depth + 1)?;
                let values = self.values;
                let value = self.binding(values, original_key, span)?;
                match (start, end, value) {
                    (NaturalValue::Closed(start), NaturalValue::Closed(end), Some((_, value))) => {
                        if *value < start || *value >= end {
                            self.fail(
                                span,
                                ErrorCode::Contract,
                                "concrete fold index is outside its original bounds",
                            )
                        } else {
                            Ok(NaturalValue::Closed(*value))
                        }
                    }
                    _ => Ok(NaturalValue::Deferred),
                }
            })(),
        };
        self.active.pop();
        result
    }

    fn number(&mut self, number: i128, span: Span) -> Result<NaturalValue, CompileError> {
        match u32::try_from(number) {
            Ok(number) => Ok(NaturalValue::Closed(number)),
            Err(_) => self.arithmetic(span),
        }
    }

    fn arithmetic<T>(&mut self, span: Span) -> Result<T, CompileError> {
        self.fail(
            span,
            ErrorCode::Limit,
            "concrete natural arithmetic exceeds u32 or has negative subtraction",
        )
    }

    /// The same checked affine template evaluation used by the existing source
    /// elaborator, with the checked helper premises retained. No source body is
    /// re-expanded and no normalized value replaces an ordinary original tree.
    fn linear(
        &mut self,
        expression: &Linear,
        parameters: &[BinderKey],
        actuals: &[NaturalValue],
        span: Span,
    ) -> Result<Option<i128>, CompileError> {
        (self.charge)(span, 1)?;
        let mut result = Some(expression.constant);
        (self.charge)(span, expression.terms.len().saturating_add(1))?;
        for (key, coefficient) in &expression.terms {
            (self.charge)(span, 1)?;
            let mut actual = None;
            (self.charge)(span, parameters.len())?;
            for (parameter, value) in parameters.iter().zip(actuals) {
                if self.same_key(parameter, key, span)? {
                    actual = Some(*value);
                    break;
                }
            }
            let Some(actual) = actual else {
                return self.fail(
                    span,
                    ErrorCode::TypeMismatch,
                    "missing original Nat helper template binding",
                );
            };
            match actual {
                NaturalValue::Deferred => result = None,
                NaturalValue::Closed(value) => {
                    let Some(scaled) = coefficient.checked_mul(i128::from(value)) else {
                        return self.arithmetic(span);
                    };
                    if let Some(previous) = result {
                        let Some(next) = previous.checked_add(scaled) else {
                            return self.arithmetic(span);
                        };
                        result = Some(next);
                    }
                }
            }
        }
        Ok(result)
    }
}

fn compare(left: i128, comparison: Compare, right: i128) -> bool {
    match comparison {
        Compare::Eq => left == right,
        Compare::Ne => left != right,
        Compare::Lt => left < right,
        Compare::Le => left <= right,
        Compare::Gt => left > right,
        Compare::Ge => left >= right,
    }
}

#[cfg(test)]
mod tests;
