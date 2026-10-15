//! Borrow a runtime call only through its one original checked collection.
//!
//! This associates already validated metadata with the exact source operands.
//! It evaluates no argument, supplies no evidence and enables no source profile.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.

use super::*;
use crate::frontend::check::plans::{StaticCallPlan, StaticCategory};
use crate::frontend::resolve::ModuleId;
use crate::frontend::resolve::locals::{BindingKind, OriginalNode};

#[cfg(test)]
mod tests;

pub(super) struct OriginalCall<'a> {
    pub owner: DefId,
    pub module: ModuleId,
    pub expression: &'a Expr,
    pub callee: &'a Ident,
    pub static_arguments: &'a [StaticOp],
    pub runtime_arguments: RuntimeArguments<'a>,
}

pub(super) struct CheckedCall<'checked> {
    plan: &'checked StaticCallPlan,
}

impl<'checked> CheckedCall<'checked> {
    pub(super) fn plan(&self) -> &'checked StaticCallPlan {
        self.plan
    }

    /// Every successful result borrows the original plan. Its complete payload
    /// was checked before Index consumption by check::plans::validate_and_finish;
    /// this boundary additionally binds the runtime adapter's actual AST slices.
    pub(super) fn original(
        program: &'checked check::CheckedProgram,
        lookup: &Lookup<'_, '_>,
        call: OriginalCall<'_>,
        charge: &mut impl FnMut(Span, usize) -> Result<(), CompileError>,
        error: &impl Fn(Span, ErrorCode, &'static str) -> CompileError,
    ) -> Result<Self, CompileError> {
        let at = call.expression.span;
        macro_rules! refuse {
            ($message:literal) => {{
                charge(at, $message.len() + 1)?;
                return Err(error(at, ErrorCode::TypeMismatch, $message));
            }};
        }
        // The fallible forward lookups use the existing address maps. No
        // equal-looking cloned node is passed to an infallible occurrence API.
        charge(at, 6)?;
        let Some(node) = lookup.try_node_id_expr(call.expression) else {
            refuse!("runtime call is not an original expression occurrence");
        };
        if node.definition() != call.owner {
            refuse!("runtime call belongs to another original owner");
        }
        let Some(OriginalNode::Expression(original)) =
            lookup.original_node_budgeted(node, &mut *charge)?
        else {
            refuse!("runtime call lacks its original expression association");
        };
        charge(at, 1)?;
        if !std::ptr::eq(original, call.expression) {
            refuse!("runtime call differs from its original expression");
        }
        charge(at, 6)?;
        let Some(site) = lookup.try_reference_site(call.callee) else {
            refuse!("runtime callee is not an original reference occurrence");
        };
        if site.definition() != call.owner {
            refuse!("runtime callee belongs to another original owner");
        }
        charge(at, 2)?;
        let Some(table) = program.lexical.get(&call.owner) else {
            refuse!("runtime call lacks its original checked lexical table");
        };
        let Some(usage) = table.try_usage(site) else {
            refuse!("runtime callee lacks its original checked reference");
        };
        // try_reference_site established this lookup's usage before the
        // infallible borrow. Pointer identity refuses a different judgment's
        // structurally equal table, even for identical numeric occurrence IDs.
        charge(at, 4)?;
        if !std::ptr::eq(lookup.usage(call.callee), usage) {
            refuse!("runtime call and plan belong to different checked collections");
        }
        charge(at, 1)?;
        let operands_match = match (&original.kind, call.runtime_arguments) {
            (
                ExprKind::Call {
                    callee,
                    static_args,
                    args,
                },
                RuntimeArguments::Values(actual),
            ) => {
                std::ptr::eq(callee, call.callee)
                    && std::ptr::eq(static_args.as_slice(), call.static_arguments)
                    && std::ptr::eq(args.as_slice(), actual)
            }
            (
                ExprKind::AccessCall {
                    callee,
                    static_args,
                    args,
                },
                RuntimeArguments::Accesses(actual),
            ) => {
                std::ptr::eq(callee, call.callee)
                    && std::ptr::eq(static_args.as_slice(), call.static_arguments)
                    && std::ptr::eq(args.as_slice(), actual)
            }
            _ => false,
        };
        if !operands_match {
            refuse!("runtime call operands differ from their original AST slices");
        }
        charge(at, 2)?;
        let Some(plan) = program.static_calls.get(&site) else {
            refuse!("runtime call lacks its original static call plan");
        };
        let Some(owner) = program.resolution.try_declaration(call.owner) else {
            refuse!("runtime call lacks its original declaration");
        };
        if plan.owner != call.owner
            || plan.module != call.module
            || owner.module != call.module
            || plan.node != node
            || plan.callee.site != site
            || plan.callee.local.is_some()
            || plan.callee.target != usage.target
            || plan.callee.target != ResolvedUse::Global(Target::Declaration(plan.target))
            || plan.environment.owner != call.owner
            || plan.environment.module != call.module
        {
            refuse!("runtime call plan has a different original identity or environment");
        }
        charge(at, 3)?;
        let Some(target) = program.resolution.try_declaration(plan.target) else {
            refuse!("runtime call plan lacks its original target declaration");
        };
        let Some(interface) = program.interfaces.get(&plan.target) else {
            refuse!("runtime call plan lacks its original target interface");
        };
        charge(at, target.name.0.len() + interface.module.len() + 1)?;
        if matches!(target.kind, FnKind::Meaning | FnKind::Static)
            || target.ast_index != interface.ast_index
            || target.kind != interface.kind
            || target.name.0 != interface.module
            || interface.statics.len() != plan.arguments.len()
            || plan.arguments.len() != call.static_arguments.len()
            || interface.params.len() != plan.parameters.len()
            || plan.parameters.len() != call.runtime_arguments.len()
        {
            refuse!("runtime call plan has a different interface or argument cardinality");
        }
        charge(at, 2)?;
        let effect = crate::frontend::effects::effect_at(
            &program.resolution,
            &program.effects,
            crate::frontend::effects::EffectContext::Module(call.module),
            plan.target,
        );
        if effect.is_none() || plan.source_effect != effect {
            refuse!("runtime call plan differs from its caller-visible source effect");
        }
        charge(at, 1)?;
        let Some(formals) = program.lexical.get(&plan.target) else {
            refuse!("runtime call target lacks its original formal table");
        };
        charge(at, plan.arguments.len())?;
        for ((actual, formal), argument) in plan
            .arguments
            .iter()
            .zip(&interface.statics)
            .zip(call.static_arguments)
        {
            charge(
                argument.span,
                actual.formal.name.len() + formal.key.name.len() + 2,
            )?;
            let (category, binding_kind) = match formal.kind {
                StaticKind::Basis => (StaticCategory::Basis, BindingKind::StaticBasis),
                StaticKind::Natural => (StaticCategory::Natural, BindingKind::StaticNatural),
                StaticKind::Operation { .. } => {
                    (StaticCategory::Operation, BindingKind::StaticOperation)
                }
            };
            if actual.formal != formal.key
                || actual.formal.id.definition() != plan.target
                || actual.category != category
            {
                refuse!("runtime static actual has a different formal identity or category");
            }
            charge(argument.span, 1)?;
            let Some(binding) = formals.try_binder(formal.key.id) else {
                refuse!("runtime static formal lacks its original binding");
            };
            charge(
                argument.span,
                binding.key.name.len() + formal.key.name.len() + 1,
            )?;
            if binding.kind != binding_kind || binding.key != formal.key {
                refuse!("runtime static formal differs from its checked binding category");
            }
            let Some(root) = actual.value.node else {
                refuse!("runtime static actual lacks its original root occurrence");
            };
            if root.definition() != call.owner || actual.value.span != argument.span {
                refuse!("runtime static actual has a different original owner or span");
            }
            let Some(OriginalNode::Operation(original)) =
                lookup.original_node_budgeted(root, &mut *charge)?
            else {
                refuse!("runtime static actual lacks its original operation association");
            };
            charge(argument.span, 1)?;
            if !std::ptr::eq(original, argument) {
                refuse!("runtime static actual differs from its ordered original root");
            }
        }
        Ok(Self { plan })
    }
}
