//! Original arm bodies and proposed controls for the typed sector gate.
//! The physical entry is transport data; full nominal types stay in the original
//! signature and enclosing carrier request. No operation capability is issued.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;
use crate::contract::function::RetainedIdentity;
use crate::frontend::compile::{circuit, operations};
use crate::interchange::qmatch::ArmBody;
#[cfg(test)]
mod tests;

pub(super) fn inline_arm(
    lower: &mut Lowerer<'_, '_>,
    module: &str,
    block: &Block,
    target: &Expr,
    basis: &Ty,
    bits: usize,
) -> Result<(ArmSubject, Vec<CircuitStep>), CompileError> {
    let ExprKind::Name(name) = &target.kind else {
        return Err(lower.error(
            module,
            target.span,
            ErrorCode::Ownership,
            "bind the target owner to a name before using it in an inline coherent arm",
        ));
    };
    let target_key = lower
        .compiler
        .locals()
        .local_key(name)
        .ok_or_else(|| {
            lower.error(
                module,
                name.span,
                ErrorCode::Ownership,
                "inline coherent arm requires a target owner",
            )
        })?
        .clone();
    let parent = lower.nominal_qmatch.as_ref().ok_or_else(|| {
        lower.error(
            module,
            block.span,
            ErrorCode::InvalidIr,
            "missing original coherent arm context",
        )
    })?;
    let frame = parent.branch_frame();
    lower.compiler.charge(
        module,
        block.span,
        basis.tree_size().nodes.saturating_mul(3)
            + total_size(
                lower
                    .bindings
                    .iter()
                    .map(|(key, operation)| key.name.len() + operation.copy_size() + 1),
            ),
    )?;
    let expected = Ty::quantum(basis.clone());
    let mut inner = Lowerer {
        nominal_modules: std::rc::Rc::clone(&lower.nominal_modules),
        nominal_basis_used: Some(false),
        source_planned: true,
        compiler: lower.compiler,
        raw: RawState::new(),
        operation_sources: BTreeMap::new(),
        instrument_calls: Vec::new(),
        nominal_qmatch: Some(frame),
        source_context: None,
        tuple_binding_origins: Vec::new(),
        access_updates: Vec::new(),
        effect: Effect::Unitary,
        contract_effect: Effect::Unitary,
        effect_source: None,
        depth: lower.depth,
        bindings: lower.bindings.clone(),
    };
    let mut quantum_inputs = Vec::new();
    let mut classical_inputs = Vec::new();
    let input = inner.input(
        &expected,
        module,
        name.span,
        &mut quantum_inputs,
        &mut classical_inputs,
    )?;
    let mut isolated = BTreeMap::from([(target_key, Binding::Live(input))]);
    let result = inner.block(module, block, &mut isolated)?;
    inner.no_owned_bindings(module, block.span, &isolated, [name])?;
    if result.ty() != expected {
        return Err(inner.error(
            module,
            block.result.span,
            ErrorCode::TypeMismatch,
            "inline coherent arm must return a single owner of the exact target type",
        ));
    }
    if inner.effect != Effect::Unitary || inner.contract_effect != Effect::Unitary {
        return Err(inner.error(
            module,
            block.span,
            ErrorCode::Effect,
            "inline coherent arm body must be unitary",
        ));
    }
    let slot = inner.quantum(module, block.result.span, &result, false)?;
    let raw = RawProgram {
        quantum_inputs,
        classical_inputs,
        operations: std::mem::take(&mut inner.raw.operations),
        quantum_outputs: vec![inner.raw.registers[&slot].token],
        classical_outputs: vec![],
        declared_effect: Effect::Unitary,
    };
    let context = inner
        .nominal_qmatch
        .take()
        .expect("original arm frame")
        .branch_subject(&mut inner, module)?;
    let checked = inner
        .compiler
        .kernel
        .accept_raw_with_budget(raw, &mut inner.compiler.exact_work)
        .map_err(|failure| {
            let limit = failure.code == "limit";
            verification_error(
                inner.compiler,
                &inner.operation_sources,
                module,
                block.span,
                failure,
                limit,
            )
        })?;
    let flat = circuit::flatten(inner.compiler, module, block.span, &checked)?;
    inner.compiler.charge(
        module,
        block.span,
        crate::frontend::raw_state::operations_size(&checked.program().operations)
            + total_size(flat.iter().map(circuit::size)).saturating_mul(2)
            + 4 * bits
            + 8,
    )?;
    let controlled_steps = operations::controlled(flat, bits);
    Ok((
        ArmSubject {
            body: ArmBody::Inline {
                raw: checked.program().clone(),
                context,
            },
            controlled: super::controlled(controlled_steps.clone(), bits),
            operation: None,
        },
        controlled_steps,
    ))
}

pub(in crate::frontend::compile::lower::quantum_match) enum BuiltinArmOrigin<'a> {
    Named(&'a Ident),
    Constructed(&'a operations::Operation, Span),
}

/// Retain each written Bit/Unit/Bits arm before lifting its controls to the
/// enclosing selector. Even equal provider occurrences keep their own slots.
pub(in crate::frontend::compile::lower::quantum_match) fn builtin_arm(
    lower: &mut Lowerer<'_, '_>,
    module: &str,
    origin: BuiltinArmOrigin<'_>,
    target: &Ty,
    steps: &[CircuitStep],
    already_controlled: bool,
) -> Result<ArmSubject, CompileError> {
    let (span, subject) = match origin {
        BuiltinArmOrigin::Named(name) => (
            name.span,
            builtin_named_origin(lower, module, name, target)?,
        ),
        BuiltinArmOrigin::Constructed(operation, span) => (
            span,
            lower
                .compiler
                .qmatch_operation_subject(operation, module, span)?,
        ),
    };
    let bits = target.basis_bits().expect("built-in qmatch target");
    lower.compiler.charge(
        module,
        span,
        total_size(steps.iter().map(circuit::size)).saturating_mul(4) + 4 * bits + 24,
    )?;
    let mut forward = steps.to_vec();
    if already_controlled {
        // Fix the synthetic positive control to one. Uncontrolled scaffolding
        // (including conjugation) and conditional scalar phases remain present.
        lift_arm(&mut forward, 0, bits, 0, true)
            .map_err(|error| lower.compiler.op_error(module, span, error))?;
    }
    let controlled_steps = if already_controlled {
        steps.to_vec()
    } else {
        operations::controlled(steps.to_vec(), bits)
    };
    let raw = RawProgram {
        quantum_inputs: vec![QuantumPort {
            token: TokenId(0),
            wires: (0..bits as u32).map(WireId).collect(),
            shape: BasisShape { bits: bits as u8 },
        }],
        classical_inputs: vec![],
        operations: vec![RawOp::ApplyUnitary {
            input: TokenId(0),
            output: TokenId(1),
            steps: forward,
        }],
        quantum_outputs: vec![TokenId(1)],
        classical_outputs: vec![],
        declared_effect: Effect::Unitary,
    };
    Ok(ArmSubject {
        body: ArmBody::Program(raw),
        controlled: super::controlled(controlled_steps, bits),
        operation: Some(Arc::new(subject)),
    })
}

fn builtin_named_origin(
    lower: &mut Lowerer<'_, '_>,
    module: &str,
    name: &Ident,
    target: &Ty,
) -> Result<crate::interchange::qmatch::OperationSubject, CompileError> {
    use crate::interchange::qmatch::{
        Description, OperationNode, OperationPrimitive, OperationSubject,
    };
    if let Some(operation) = lower.retained_bound_operation(module, name)? {
        return lower
            .compiler
            .qmatch_operation_subject(&operation, module, name.span);
    }
    let (node, bodies) = match lower.compiler.resolve(module, name)? {
        Callee::User(key) => {
            let name_bytes = &lower.compiler.source.resolution.declaration(key).name;
            lower.compiler.charge(
                module,
                name.span,
                name_bytes.0.len() + name_bytes.1.len() + 1,
            )?;
            let (module_name, function) = lower
                .compiler
                .source
                .resolution
                .declaration(key)
                .name
                .clone();
            let body = lower.compiler.original_pure_body(key, module, name.span)?;
            (
                OperationNode::Provider {
                    module: module_name,
                    function,
                    bases: vec![],
                    naturals: vec![],
                    operations: vec![],
                },
                vec![body],
            )
        }
        Callee::Primitive(primitive) => {
            let kind = match primitive {
                PrimitiveId::H => OperationPrimitive::H,
                PrimitiveId::GlobalPhaseEighth => OperationPrimitive::GlobalPhaseEighth,
                _ => {
                    return Err(lower.error(
                        module,
                        name.span,
                        ErrorCode::TypeMismatch,
                        "unsupported qmatch primitive",
                    ));
                }
            };
            lower
                .compiler
                .charge(module, name.span, 2 * target.tree_size().nodes + 1)?;
            (
                OperationNode::Primitive {
                    kind,
                    target: super::builtin_basis_description(target),
                },
                vec![],
            )
        }
    };
    Ok(OperationSubject {
        description: Description {
            nodes: vec![node],
            root: 0,
        },
        bodies,
        meaning_references: vec![],
    })
}

/// Direct application primitives remain distinct from ordinary source
/// providers. This proposal retains their exact one-owner target and scalar
/// phase; it grants no static/host Op binding or accepted execution.
fn primitive(
    lower: &mut Lowerer<'_, '_>,
    module: &str,
    name: &Ident,
    primitive: PrimitiveId,
    target: &Ty,
    bits: usize,
    operand_span: Span,
) -> Result<
    (
        ArmBody,
        Vec<CircuitStep>,
        Arc<crate::interchange::qmatch::OperationSubject>,
    ),
    CompileError,
> {
    use crate::interchange::qmatch::{
        Description, OperationNode, OperationPrimitive, OperationSubject,
    };
    if primitive == PrimitiveId::H && *target != Ty::bit() {
        return Err(lower.error(
            module,
            operand_span,
            ErrorCode::TypeMismatch,
            static_operand_mismatch(&Ty::bit(), target, true),
        ));
    }
    lower
        .compiler
        .charge(module, name.span, bits + target.tree_size().nodes * 2 + 24)?;
    let target = if target.basis_bits().is_some() {
        super::builtin_basis_description(target)
    } else {
        lower
            .compiler
            .carrier_description(module, name.span, target)?
    };
    let (kind, step) = match primitive {
        PrimitiveId::H => (OperationPrimitive::H, circuit::gate(SingleGate::H, 0)),
        PrimitiveId::GlobalPhaseEighth => (
            OperationPrimitive::GlobalPhaseEighth,
            CircuitStep {
                controls: vec![],
                action: CircuitAction::Monomial {
                    indices: vec![],
                    permutation: vec![0],
                    phases: vec![1],
                },
            },
        ),
        _ => unreachable!("only direct unary unitary primitives enter this preparation"),
    };
    let operations = if primitive == PrimitiveId::H {
        vec![RawOp::Gate {
            gate: SingleGate::H,
            input: TokenId(0),
            output: TokenId(1),
        }]
    } else {
        vec![RawOp::ApplyUnitary {
            input: TokenId(0),
            output: TokenId(1),
            steps: vec![step.clone()],
        }]
    };
    let raw = RawProgram {
        quantum_inputs: vec![QuantumPort {
            token: TokenId(0),
            shape: BasisShape {
                bits: lower.compiler.narrow_u8(
                    module,
                    name.span,
                    bits,
                    "primitive target width",
                )?,
            },
            wires: (0..bits as u32).map(WireId).collect(),
        }],
        classical_inputs: vec![],
        operations,
        quantum_outputs: vec![TokenId(1)],
        classical_outputs: vec![],
        declared_effect: Effect::Unitary,
    };
    Ok((
        ArmBody::Program(raw),
        operations::controlled(vec![step], bits),
        Arc::new(OperationSubject {
            description: Description {
                nodes: vec![OperationNode::Primitive { kind, target }],
                root: 0,
            },
            bodies: vec![],
            meaning_references: vec![],
        }),
    ))
}

pub(super) fn prepare(
    lower: &mut Lowerer<'_, '_>,
    module: &str,
    expression: &StaticOp,
    target: &Ty,
    bits: usize,
    env: &Env,
    operand_span: Span,
) -> Result<
    (
        ArmBody,
        Vec<CircuitStep>,
        Arc<crate::interchange::qmatch::OperationSubject>,
    ),
    CompileError,
> {
    if let StaticOpKind::Name(name) = &expression.kind {
        lower.static_name(module, name, env)?;
        if lower
            .compiler
            .locals()
            .usage(name)
            .static_parameter
            .is_none()
            && lower.bound_operation(name).is_none()
        {
            if let Callee::Primitive(id @ (PrimitiveId::H | PrimitiveId::GlobalPhaseEighth)) =
                lower.compiler.resolve(module, name)?
            {
                return primitive(lower, module, name, id, target, bits, operand_span);
            }
        }
    }
    if target.basis_bits().is_some() {
        // Bare arm names get their interface from the original target. Only
        // constructed arm expressions have an independent body-static plan.
        let operation = match &expression.kind {
            StaticOpKind::Name(name) => match lower.retained_bound_operation(module, name)? {
                Some(bound) => bound,
                None if lower
                    .compiler
                    .locals()
                    .usage(name)
                    .static_parameter
                    .is_some() =>
                {
                    return Err(lower.error(
                        module,
                        name.span,
                        ErrorCode::TypeMismatch,
                        "qmatch arm requires the bound operation for its original static parameter",
                    ));
                }
                None => lower.compiler.provider(module, name, None)?,
            },
            _ => lower.operation(module, expression, env)?,
        };
        if operation.basis != *target
            || operation.codomain != *target
            || operation.effect != Effect::Unitary
        {
            if operation.basis == operation.codomain && operation.effect == Effect::Unitary {
                return Err(lower.error(
                    module,
                    operand_span,
                    ErrorCode::TypeMismatch,
                    static_operand_mismatch(&operation.basis, target, true),
                ));
            }
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
        let steps = operation.steps(module, expression.span, Access::Controlled, lower.compiler)?;
        let original =
            lower
                .compiler
                .qmatch_operation_subject(&operation, module, expression.span)?;
        return Ok((
            ArmBody::Evidence(Arc::clone(evidence)),
            steps,
            Arc::new(original),
        ));
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
        lower.error(
            module,
            name.span,
            ErrorCode::InvalidIr,
            "qmatch arm lacks its actual original lowering context",
        )
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
    let original_name = &lower.compiler.source.resolution.declaration(key).name;
    lower.compiler.charge(
        module,
        name.span,
        original_name.0.len() + original_name.1.len() + 24,
    )?;
    Ok((
        ArmBody::Physical {
            bits: bits as u32,
            raw: raw.clone(),
            identity: Box::new(RetainedIdentity::interned(path.clone(), path, sources)),
        },
        steps,
        Arc::new(crate::interchange::qmatch::OperationSubject {
            description: crate::interchange::qmatch::Description {
                nodes: vec![crate::interchange::qmatch::OperationNode::Provider {
                    module: lower
                        .compiler
                        .source
                        .resolution
                        .declaration(key)
                        .name
                        .0
                        .clone(),
                    function: lower
                        .compiler
                        .source
                        .resolution
                        .declaration(key)
                        .name
                        .1
                        .clone(),
                    bases: vec![],
                    naturals: vec![],
                    operations: vec![],
                }],
                root: 0,
            },
            bodies: vec![crate::interchange::qmatch::OriginalBody::Pure { program, context }],
            meaning_references: vec![],
        }),
    ))
}
