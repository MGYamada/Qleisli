//! Propose actual call fragments to the existing original-source qmatch gate.
//! The source reader checks all supported original events and their literal IR.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;
use crate::frontend::types::nominal::Body;
use crate::interchange::carrier::{Interface, Owner};
use crate::interchange::qmatch::{ArmSubject, Position, SelectionSubject, SourceSite};

mod arms;

pub(in crate::frontend::compile::lower) struct Frame {
    key: Key,
    inputs: Vec<Owner>,
    start: usize,
    positions: Vec<Position>,
    primitive_prelude: bool,
    selections: Vec<Selection>,
}

struct Selection {
    span: Span,
    offset: usize,
    arms: Vec<ArmSubject>,
    inputs: Vec<Owner>,
    outputs: Vec<Owner>,
    start: usize,
    count: usize,
}

fn outputs(
    lower: &mut Lowerer<'_, '_>,
    module: &str,
    span: Span,
    value: &Value,
) -> Result<Vec<Owner>, CompileError> {
    // The native structural rule reads an atomic Q owner or a flat tuple of
    // such owners. Preserve source order and every zero-width owner.
    match value {
        Value::Quantum(..) => Ok(vec![owner(lower, module, span, value)?]),
        Value::Pair(left, right) => Ok(vec![
            owner(lower, module, span, left)?,
            owner(lower, module, span, right)?,
        ]),
        Value::Tuple(fields) => fields
            .iter()
            .map(|field| owner(lower, module, span, field))
            .collect(),
        _ => Err(lower.error(
            module,
            span,
            ErrorCode::Unsupported,
            "qmatch source context currently requires a flat quantum-owner result",
        )),
    }
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
        if args.len() < 2 || !args.iter().all(|arg| matches!(arg, Value::Quantum(..))) {
            return Ok(None);
        }
        if !args.iter().any(|arg| match arg {
            Value::Quantum(slot, _) => lower.raw.registers[slot].basis.basis_bits().is_none(),
            _ => false,
        }) {
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
            positions: Vec::new(),
            primitive_prelude: false,
            selections: Vec::new(),
        }))
    }

    pub(in crate::frontend::compile::lower) fn finish(
        self,
        lower: &mut Lowerer<'_, '_>,
        value: &Value,
    ) -> Result<(), CompileError> {
        let selections = self.selections;
        let Some(first) = selections.first() else {
            return Ok(());
        };
        let span = first.span;
        let name = lower
            .compiler
            .source
            .resolution
            .declaration(self.key)
            .name
            .clone();
        let outputs = outputs(lower, &name.0, span, value)?;
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
            declared_effect: lower.compiler.source.effects[&self.key]
                .asserted()
                .unwrap_or_else(|| lower.compiler.source.effects[&self.key].inferred()),
        };
        let mut rows = lower
            .compiler
            .retained_ordinary_type_sources(self.key, &name.0, span)?;
        if self.primitive_prelude {
            lower
                .compiler
                .charge(&name.0, span, rows.iter().map(|row| row.0.len() + 1).sum())?;
            let mut modules = rows.iter().map(|row| row.0.clone()).collect::<Vec<_>>();
            modules.push("std::prelude".to_owned());
            modules.sort_unstable();
            modules.dedup();
            rows = lower
                .compiler
                .retain_source_modules(&name.0, span, modules)?;
        }
        lower.compiler.charge(
            &name.0,
            span,
            rows.iter().map(|row| row.0.len() + row.1.len()).sum(),
        )?;
        let sources = rows
            .iter()
            .map(|row| row.as_ref().clone())
            .collect::<Vec<_>>();
        let copies = selections
            .iter()
            .flat_map(|selected| selected.inputs.iter().chain(&selected.outputs))
            .map(|owner| {
                owner.port.wires.len()
                    + owner
                        .basis
                        .iter()
                        .map(|atom| {
                            1 + match atom {
                                crate::interchange::carrier::Atom::Enum(_, names)
                                | crate::interchange::carrier::Atom::Record(_, names) => {
                                    names.iter().map(|name| name.len() + 1).sum::<usize>()
                                }
                                _ => 0,
                            }
                        })
                        .sum::<usize>()
                    + 1
            })
            .sum::<usize>();
        lower.compiler.charge(&name.0, span, copies)?;
        let interfaces = selections
            .iter()
            .map(|selected| Interface {
                inputs: selected.inputs.clone(),
                outputs: selected.outputs.clone(),
                public_effect: Effect::Unitary,
            })
            .collect::<Vec<_>>();
        let subjects = selections
            .iter()
            .zip(&interfaces)
            .map(|(selected, interface)| {
                Ok(SelectionSubject {
                    interface,
                    arms: &selected.arms,
                    position: position(
                        lower,
                        &name.0,
                        selected.span,
                        selected.offset,
                        selected.start,
                        selected.count,
                    )?,
                })
            })
            .collect::<Result<Vec<_>, CompileError>>()?;
        let proposal = crate::interchange::qmatch::proposal(
            &raw,
            SourceSite {
                module: name.0.clone(),
                function: name.1,
            },
            &self.positions,
            &subjects,
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

/// Record only a real source dispatch, after its argument expressions have run.
/// Synthetic primitive calls made while lowering qmatch are not source events.
pub(in crate::frontend::compile::lower) fn record_primitive(
    lower: &mut Lowerer<'_, '_>,
    module: &str,
    callee: &Ident,
    start: usize,
) -> Result<(), CompileError> {
    let Some(frame) = lower.nominal_qmatch.as_ref() else {
        return Ok(());
    };
    let relative = start.checked_sub(frame.start).ok_or_else(|| {
        lower.error(
            module,
            callee.span,
            ErrorCode::InvalidIr,
            "primitive precedes its original qmatch context",
        )
    })?;
    let count = lower
        .raw
        .operations
        .len()
        .checked_sub(start)
        .ok_or_else(|| {
            lower.error(
                module,
                callee.span,
                ErrorCode::InvalidIr,
                "primitive removed its original operation prefix",
            )
        })?;
    let original = lower.compiler.originals.module(module).ok_or_else(|| {
        lower.error(
            module,
            callee.span,
            ErrorCode::InvalidIr,
            "qmatch primitive context lacks its original source module",
        )
    })?;
    let prelude = !original.ast.no_implicit_prelude;
    let position = position(
        lower,
        module,
        callee.span,
        callee.span.start,
        relative,
        count,
    )?;
    lower.compiler.charge(module, callee.span, 4)?;
    let frame = lower.nominal_qmatch.as_mut().expect("original context");
    frame.positions.push(position);
    frame.primitive_prelude |= prelude;
    Ok(())
}

fn position(
    lower: &Lowerer<'_, '_>,
    module: &str,
    span: Span,
    offset: usize,
    start: usize,
    count: usize,
) -> Result<Position, CompileError> {
    let number = |value| {
        u32::try_from(value).map_err(|_| {
            lower.error(
                module,
                span,
                ErrorCode::Limit,
                "qmatch source/interval position exceeds u32",
            )
        })
    };
    Ok(Position {
        offset: number(offset)?,
        start: number(start)?,
        count: number(count)?,
    })
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
        .is_none_or(|frame| frame.selections.len() >= 128)
    {
        return Err(lower.error(module, span, ErrorCode::Unsupported, "nominal qmatch requires an original structural function with quantum parameters and at most 128 selections"));
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
    let inputs = vec![
        owner(lower, module, span, &selector)?,
        owner(lower, module, span, &target)?,
    ];
    let start = lower.raw.operations.len();
    let joined = lower.primitive_call(module, span, PrimitiveId::Join, vec![selector, target])?;
    let slot = lower.quantum(module, span, &joined, false)?;
    lower.apply_circuit(slot, steps);
    let result = lower.primitive_call(module, span, PrimitiveId::Split, vec![joined])?;
    let selected_outputs = outputs(lower, module, span, &result)?;
    let count = lower.raw.operations.len() - start;
    let relative = start
        - lower
            .nominal_qmatch
            .as_ref()
            .expect("checked original frame")
            .start;
    let position = position(
        lower,
        module,
        span,
        selection.keyword.start,
        relative,
        count,
    )?;
    lower.compiler.charge(module, span, 4)?;
    let frame = lower
        .nominal_qmatch
        .as_mut()
        .expect("checked original frame");
    frame.selections.push(Selection {
        span,
        offset: selection.keyword.start,
        arms,
        inputs,
        outputs: selected_outputs,
        start: relative,
        count,
    });
    frame.positions.push(position);
    Ok(result)
}
