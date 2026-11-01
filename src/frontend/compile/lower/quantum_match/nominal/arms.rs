//! Original named arm bodies and proposed controls for the typed sector gate.
//! The physical entry is transport data; full nominal types stay in the original
//! signature and enclosing carrier request. No operation capability is issued.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;
use crate::contract::function::RetainedIdentity;
use crate::frontend::compile::{circuit, operations};
use crate::interchange::qmatch::ArmBody;

pub(super) fn prepare(
    lower: &mut Lowerer<'_, '_>,
    module: &str,
    expression: &StaticOp,
    target: &Ty,
    bits: usize,
    env: &Env,
) -> Result<(ArmBody, Arc<ContextSubject>, Vec<CircuitStep>), CompileError> {
    if target.basis_bits().is_some() {
        let operation = lower.operation(module, expression, env)?;
        if operation.basis != *target
            || operation.codomain != *target
            || operation.effect != Effect::Unitary
        {
            return Err(lower.error(
                module,
                expression.span,
                ErrorCode::TypeMismatch,
                "qmatch arm requires the exact Unitary target interface",
            ));
        }
        let operations::Node::Provider(evidence) = operation.node.as_ref() else {
            return Err(lower.error(
                module,
                expression.span,
                ErrorCode::Unsupported,
                "qmatch requires an original named function-evidence entry",
            ));
        };
        let context = evidence.source_context().cloned().ok_or_else(|| {
            lower.error(module, expression.span, ErrorCode::InvalidIr,
                "qmatch arm lacks its actual original lowering context")
        })?;
        let steps = operation.steps(module, expression.span, Access::Controlled, lower.compiler)?;
        return Ok((ArmBody::Evidence(Arc::clone(evidence)), context, steps));
    }

    let StaticOpKind::Name(name) = &expression.kind else {
        return Err(lower.error(module, expression.span, ErrorCode::Unsupported,
            "nominal operation constructors require their independently checked original operation tree"));
    };
    lower.static_name(module, name, env)?;

    let Callee::User(key) = lower.compiler.resolve(module, name)? else {
        return Err(lower.error(
            module,
            name.span,
            ErrorCode::TypeMismatch,
            "nominal qmatch requires an original named arm",
        ));
    };
    if !lower.compiler.declarations[&key].static_params.is_empty() {
        return Err(lower.error(
            module,
            name.span,
            ErrorCode::Unsupported,
            "qmatch named arms must be closed; instantiate in an ordinary wrapper",
        ));
    }
    // The common qmatch judgment already checked the exact target tree. The
    // native source reader independently closes the original arm signature
    // against that same full tree. This proposal is not another type checker
    // and does not re-close each signature to manufacture an Operation handle.
    if lower.compiler.effect_in_module(module, key) != Some(Effect::Unitary) {
        return Err(lower.error(
            module,
            name.span,
            ErrorCode::TypeMismatch,
            "qmatch arm requires the exact Unitary target interface",
        ));
    }
    let program = lower
        .compiler
        .checked
        .get(&key)
        .ok_or_else(|| {
            lower.error(
                module,
                name.span,
                ErrorCode::InvalidIr,
                "qmatch arm lacks its independently checked original body",
            )
        })?
        .clone();
    if program.raw().quantum_inputs.len() != 1
        || program.raw().quantum_inputs[0].wires.len() != bits
        || program.raw().quantum_outputs.len() != 1
    {
        return Err(lower.error(
            module,
            name.span,
            ErrorCode::InvalidIr,
            "qmatch arm physical subject differs from its one-owner target",
        ));
    }
    let mut steps = circuit::flatten(lower.compiler, module, name.span, &program)?;
    let context = program.source_context().cloned().ok_or_else(|| {
        lower.error(module, name.span, ErrorCode::InvalidIr,
            "qmatch arm lacks its actual original lowering context")
    })?;
    lower.compiler.charge(
        module,
        name.span,
        total_size(steps.iter().map(circuit::size)) + steps.len() + bits + 1,
    )?;
    steps = operations::controlled(steps, bits);
    let raw = program.raw();
    lower.compiler.charge(
        module,
        name.span,
        crate::frontend::raw_state::operations_size(&raw.operations)
            + raw
                .quantum_inputs
                .iter()
                .map(|port| port.wires.len() + 3)
                .sum::<usize>()
            + raw.quantum_outputs.len(),
    )?;
    let sources = lower.compiler.retained_sources(
        module,
        name.span,
        &[key],
        &operations::Bindings::new(),
        &[raw],
    )?;
    let path = lower.compiler.source.resolution.path(key);
    lower.compiler.charge(
        module,
        name.span,
        path.len().saturating_mul(2).saturating_add(1),
    )?;
    Ok((
        ArmBody::Physical {
            bits: bits as u32,
            raw: raw.clone(),
            identity: Box::new(RetainedIdentity::interned(path.clone(), path, sources)),
        },
        context,
        steps,
    ))
}
