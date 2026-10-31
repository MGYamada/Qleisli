//! Propose actual call fragments to the existing original-source qmatch gate.
//! The source reader checks the complete structural body, not a synthetic site.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;
use crate::frontend::types::nominal::Body;
use crate::interchange::carrier::{Interface, Owner};
use crate::interchange::qmatch::{ArmSubject, SourceSite};

mod arms;

pub(in crate::frontend::compile::lower) struct Frame {
    key: Key,
    inputs: Vec<Owner>,
    start: usize,
    selection: Option<(Span, Vec<ArmSubject>)>,
}

fn owner(
    lower: &mut Lowerer<'_, '_>,
    module: &str,
    span: Span,
    value: &Value,
) -> Result<Owner, CompileError> {
    let slot = lower.quantum(module, span, value, false)?;
    let register = &lower.raw.registers[&slot];
    let cost =
        register
            .size()
            .saturating_add(crate::frontend::compile::operations::port_copy_nodes(
                &register.basis,
            ));
    lower.compiler.charge(module, span, cost)?;
    let register = lower.raw.registers[&slot].clone();
    let basis = lower
        .compiler
        .carrier_description(module, span, &register.basis)?;
    Ok(Owner {
        port: QuantumPort {
            token: register.token,
            shape: BasisShape {
                bits: register.wires.len() as u8,
            },
            wires: register.wires,
        },
        basis,
    })
}

impl Frame {
    pub(in crate::frontend::compile::lower) fn start(
        lower: &mut Lowerer<'_, '_>,
        key: Key,
        args: &[Value],
    ) -> Result<Option<Self>, CompileError> {
        let [Value::Quantum(selector, _), Value::Quantum(target, _)] = args else {
            return Ok(None);
        };
        if lower.raw.registers[selector].basis.basis_bits().is_some()
            && lower.raw.registers[target].basis.basis_bits().is_some()
        {
            return Ok(None);
        }
        let name = lower
            .compiler
            .source
            .resolution
            .declaration(key)
            .name
            .clone();
        let span = lower.compiler.declarations[&key].span;
        Ok(Some(Self {
            key,
            inputs: args
                .iter()
                .map(|arg| owner(lower, &name.0, span, arg))
                .collect::<Result<_, _>>()?,
            start: lower.raw.operations.len(),
            selection: None,
        }))
    }

    pub(in crate::frontend::compile::lower) fn finish(
        self,
        lower: &mut Lowerer<'_, '_>,
        value: &Value,
    ) -> Result<(), CompileError> {
        let Some((span, arms)) = self.selection else {
            return Ok(());
        };
        let name = lower
            .compiler
            .source
            .resolution
            .declaration(self.key)
            .name
            .clone();
        let Value::Pair(left, right) = value else {
            return Err(lower.error(
                &name.0,
                span,
                ErrorCode::Unsupported,
                "nominal qmatch requires the original two-owner result",
            ));
        };
        let outputs = vec![
            owner(lower, &name.0, span, left)?,
            owner(lower, &name.0, span, right)?,
        ];
        lower.compiler.charge(
            &name.0,
            span,
            crate::frontend::raw_state::operations_size(&lower.raw.operations[self.start..]),
        )?;
        let raw = RawProgram {
            quantum_inputs: self.inputs.iter().map(|owner| owner.port.clone()).collect(),
            classical_inputs: vec![],
            operations: lower.raw.operations[self.start..].to_vec(),
            quantum_outputs: outputs.iter().map(|owner| owner.port.token).collect(),
            classical_outputs: vec![],
            declared_effect: Effect::Unitary,
        };
        let rows = lower
            .compiler
            .retained_ordinary_type_sources(self.key, &name.0, span)?;
        lower.compiler.charge(
            &name.0,
            span,
            rows.iter().map(|row| row.0.len() + row.1.len()).sum(),
        )?;
        let sources = rows
            .iter()
            .map(|row| row.as_ref().clone())
            .collect::<Vec<_>>();
        let offset = u32::try_from(span.start).map_err(|_| {
            lower.error(
                &name.0,
                span,
                ErrorCode::Limit,
                "qmatch source offset exceeds u32",
            )
        })?;
        let proposal = crate::interchange::qmatch::proposal(
            &raw,
            Interface {
                inputs: self.inputs,
                outputs,
                public_effect: Effect::Unitary,
            },
            SourceSite {
                module: name.0.clone(),
                function: name.1,
                offset,
            },
            &arms,
            &sources,
        )
        .and_then(|(artifact, request)| {
            lower
                .compiler
                .kernel
                .check_qmatch_source(&artifact, &request)
        });
        let checked = proposal.map_err(|error| {
            let limit = error.code == "limit";
            verification_error(
                lower.compiler,
                &lower.operation_sources,
                &name.0,
                span,
                error,
                limit,
            )
        })?;
        lower
            .compiler
            .exact_work
            .charge(checked.native().exact_work())
            .map_err(|e| lower.compiler.op_error(&name.0, span, e.into()))?;
        Ok(())
    }
}

fn controlled(steps: Vec<CircuitStep>, bits: usize) -> RawProgram {
    RawProgram {
        quantum_inputs: vec![
            QuantumPort {
                token: TokenId(0),
                wires: vec![WireId(0)],
                shape: BasisShape { bits: 1 },
            },
            QuantumPort {
                token: TokenId(1),
                wires: (1..=bits as u32).map(WireId).collect(),
                shape: BasisShape { bits: bits as u8 },
            },
        ],
        classical_inputs: vec![],
        operations: vec![
            RawOp::Join {
                left: TokenId(0),
                right: TokenId(1),
                output: TokenId(2),
            },
            RawOp::ApplyUnitary {
                input: TokenId(2),
                output: TokenId(3),
                steps,
            },
            RawOp::Split {
                input: TokenId(3),
                left: TokenId(4),
                right: TokenId(5),
                left_bits: 1,
            },
        ],
        quantum_outputs: vec![TokenId(4), TokenId(5)],
        classical_outputs: vec![],
        declared_effect: Effect::Unitary,
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn emit(
    lower: &mut Lowerer<'_, '_>,
    module: &str,
    span: Span,
    selection: &QuantumMatch,
    env: &mut Env,
    selector: Value,
    selector_slot: Slot,
    target: Value,
    target_slot: Slot,
) -> Result<Value, CompileError> {
    if lower
        .nominal_qmatch
        .as_ref()
        .is_none_or(|frame| frame.selection.is_some())
    {
        return Err(lower.error(module, span, ErrorCode::Unsupported, "nominal qmatch requires one original structural function with selector and target parameters"));
    }
    let basis = &lower.raw.registers[&selector_slot].basis;
    let count = match &basis.kind {
        Kind::Nominal(nominal) => match &nominal.body {
            Body::Enum(labels) => labels.len(),
            _ => {
                return Err(lower.error(
                    module,
                    span,
                    ErrorCode::TypeMismatch,
                    "qmatch requires a fieldless enum or built-in ordinal selector",
                ));
            }
        },
        Kind::Unit => 1,
        Kind::Bit => 2,
        Kind::Bits(bits) if *bits <= 6 => 1usize << *bits,
        _ => {
            return Err(lower.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "qmatch requires a fieldless enum or built-in ordinal selector",
            ));
        }
    };
    let selector_bits = lower.raw.registers[&selector_slot].wires.len();
    lower
        .compiler
        .charge(module, span, Value::nominal_type_work(basis) + count)?;
    let basis = lower.raw.registers[&selector_slot].basis.clone();
    lower.compiler.charge(
        module,
        span,
        Value::nominal_type_work(&lower.raw.registers[&target_slot].basis),
    )?;
    let target_basis = lower.raw.registers[&target_slot].basis.clone();
    let target_bits = lower.raw.registers[&target_slot].wires.len();
    if count == 0 || count > 64 || selector_bits + target_bits > MAX_CONTRACT_BITS {
        return Err(lower.error(
            module,
            span,
            ErrorCode::Limit,
            "nominal qmatch currently requires at most six joined bits and 64 labels",
        ));
    }
    let mut seen = BTreeSet::new();
    let mut steps = Vec::new();
    let mut arms = Vec::new();
    for arm in &selection.arms {
        let (label_basis, ordinal) = match (&basis.kind, &arm.label) {
            (Kind::Nominal(_), QuantumLabel::Variant(label)) => lower.enum_label(module, label)?,
            (Kind::Unit | Kind::Bit | Kind::Bits(_), QuantumLabel::Ordinal(label)) => {
                (basis.clone(), *label as usize)
            }
            _ => {
                return Err(lower.error(
                    module,
                    arm.span,
                    ErrorCode::TypeMismatch,
                    "qmatch requires labels from the exact original selector type",
                ));
            }
        };
        if label_basis != basis || ordinal >= count || !seen.insert(ordinal) {
            return Err(lower.error(
                module,
                arm.span,
                ErrorCode::TypeMismatch,
                "qmatch labels must cover the exact selector declaration once",
            ));
        }
        let (subject, mut body) = arms::prepare(
            lower,
            module,
            &arm.operation,
            &target_basis,
            target_bits,
            env,
        )?;
        lower.compiler.charge(
            module,
            span,
            total_size(body.iter().map(super::super::super::circuit::size)).saturating_mul(2)
                + body.len() * (selector_bits + 1),
        )?;
        arms.push(ArmSubject {
            body: subject,
            controlled: controlled(body.clone(), target_bits),
        });
        lift_arm(&mut body, selector_bits, target_bits, ordinal, true)
            .map_err(|e| lower.compiler.op_error(module, arm.span, e))?;
        if steps.len().saturating_add(body.len()) > crate::contract::MAX_CONTRACT_STEPS {
            return Err(lower.error(
                module,
                span,
                ErrorCode::Limit,
                "qmatch exceeds the existing circuit step bound",
            ));
        }
        steps.extend(body);
    }
    if seen.len() != count {
        return Err(lower.error(
            module,
            span,
            ErrorCode::TypeMismatch,
            "qmatch requires every exact enum label",
        ));
    }
    lower
        .nominal_qmatch
        .as_mut()
        .expect("checked original frame")
        .selection = Some((span, arms));
    let joined = lower.primitive_call(module, span, PrimitiveId::Join, vec![selector, target])?;
    let slot = lower.quantum(module, span, &joined, false)?;
    lower.apply_circuit(slot, steps);
    lower.primitive_call(module, span, PrimitiveId::Split, vec![joined])
}
