//! Language primitive signatures, ownership transitions, effects, and raw IR.
//!
//! This is the source-side check. The independent verifier rechecks emitted IR
//! without calling these methods or trusting frontend ownership bookkeeping.

use super::super::{CompileError, ErrorCode, MAX_BITS, PrimitiveId, Ty};
use super::{Lowerer, Slot, Value};
use crate::frontend::ast::{Expr, ExprKind, RuntimeArguments, Span};
use crate::ir::{RawOp, SingleGate};

impl Lowerer<'_, '_> {
    pub(super) fn quantum(
        &self,
        module: &str,
        span: Span,
        value: &Value,
        bit_only: bool,
    ) -> Result<Slot, CompileError> {
        let Value::Quantum(slot, ty) = value else {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                format!(
                    "operation requires quantum ownership: expected `{}`, found `{}`",
                    if bit_only { "Q<Bit>" } else { "Q<A>" },
                    value.ty().runtime()
                ),
            ));
        };
        if bit_only && *ty != Ty::quantum(Ty::bit()) {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                format!(
                    "operation requires Q<Bit>: expected `Q<Bit>`, found `{}`",
                    value.ty().runtime()
                ),
            ));
        }
        Ok(*slot)
    }

    fn quantum_argument(
        &self,
        module: &str,
        span: Span,
        value: &Value,
        bit_only: bool,
        argument: Option<&Expr>,
    ) -> Result<Slot, CompileError> {
        // Only a directly named tuple in the current lexical frame can carry
        // binding-specific help. Equal slots in returned/reconstructed tuples
        // do not establish the identity of a still-visible source binding.
        if !matches!(value, Value::Quantum(..)) && value.owns_quantum() {
            if let Some(Expr {
                kind: ExprKind::Name(name),
                ..
            }) = argument
            {
                if let Some(origin) = self
                    .tuple_binding_origins
                    .iter()
                    .rev()
                    .find_map(|scope| scope.get(&name.text))
                    .and_then(Option::as_ref)
                {
                    return Err(self.error(&origin.module, origin.span, ErrorCode::TypeMismatch,
                        format!("binding `{}` contains a tuple of owners: expected `{}`, found `{}`; help: destructure the tuple at this binding (for cnot, `let (a, b) = cnot(a, b);`); a single name binds the whole returned tuple",
                            origin.name, if bit_only {"Q<Bit>"} else {"Q<A>"}, value.ty().runtime())));
                }
            }
        }
        self.quantum(module, span, value, bit_only)
    }

    pub(super) fn primitive_call(
        &mut self,
        module: &str,
        span: Span,
        primitive: PrimitiveId,
        args: Vec<Value>,
    ) -> Result<Value, CompileError> {
        self.primitive_with_source(module, span, primitive, args, RuntimeArguments::Values(&[]))
    }

    pub(super) fn primitive_with_source(
        &mut self,
        module: &str,
        span: Span,
        primitive: PrimitiveId,
        mut args: Vec<Value>,
        source_args: RuntimeArguments<'_>,
    ) -> Result<Value, CompileError> {
        if args.len() != primitive.runtime_arity() {
            return Err(self.error(
                module,
                span,
                ErrorCode::Arity,
                format!(
                    "{} requires {} arguments",
                    primitive.spelling(),
                    primitive.runtime_arity()
                ),
            ));
        }
        self.add_effect(module, span, primitive.effect());
        match primitive {
            PrimitiveId::EmptyBits => Ok(Value::EmptyBits),
            PrimitiveId::Unit => {
                if args.pop() != Some(Value::Unit) {
                    return Err(self.error(
                        module,
                        span,
                        ErrorCode::TypeMismatch,
                        "unit requires ordinary Unit",
                    ));
                }
                let value = self.register(Ty::unit(), vec![]);
                let slot = self.quantum(module, span, &value, false)?;
                self.raw.operations.push(RawOp::PackUnit {
                    output: self.raw.registers[&slot].token,
                });
                Ok(value)
            }
            PrimitiveId::Finish => {
                let value = args.pop().expect("one input");
                if value.ty() != Ty::quantum(Ty::unit()) {
                    return Err(self.error(
                        module,
                        span,
                        ErrorCode::TypeMismatch,
                        "finish requires Q<Unit>",
                    ));
                }
                let slot =
                    self.quantum_argument(module, span, &value, false, source_args.first())?;
                let owner = self.raw.registers.remove(&slot).expect("owned register");
                self.raw
                    .operations
                    .push(RawOp::UnpackUnit { input: owner.token });
                Ok(Value::Unit)
            }

            PrimitiveId::H => {
                let value = args.pop().expect("one argument");
                let slot =
                    self.quantum_argument(module, span, &value, true, source_args.first())?;
                self.raw.gate_bit(SingleGate::H, slot).map_err(|failure| {
                    self.error(module, span, ErrorCode::InvalidIr, failure.to_string())
                })?;
                Ok(value)
            }
            PrimitiveId::GlobalPhaseEighth => {
                let value = args.pop().expect("one argument");
                let slot =
                    self.quantum_argument(module, span, &value, false, source_args.first())?;
                self.raw.scalar_eighth(slot).map_err(|failure| {
                    self.error(module, span, ErrorCode::InvalidIr, failure.to_string())
                })?;
                Ok(value)
            }
            PrimitiveId::Split => {
                let value = args.pop().expect("one input");
                let slot =
                    self.quantum_argument(module, span, &value, false, source_args.first())?;
                let reg = self.raw.registers.remove(&slot).expect("owned register");
                let Some(mut fields) = reg.basis.into_pair() else {
                    return Err(self.error(
                        module,
                        span,
                        ErrorCode::TypeMismatch,
                        "split requires Q<(A, B)>",
                    ));
                };
                let b = fields.pop().expect("second field");
                let a = fields.pop().expect("first field");
                let width = a.basis_bits().expect("basis type");
                let left = self.register(a, reg.wires[..width].to_vec());
                let right = self.register(b, reg.wires[width..].to_vec());
                let left_slot = self.quantum(module, span, &left, false)?;
                let right_slot = self.quantum(module, span, &right, false)?;
                self.raw.operations.push(RawOp::Split {
                    input: reg.token,
                    left: self.raw.registers[&left_slot].token,
                    right: self.raw.registers[&right_slot].token,
                    left_bits: self
                        .compiler
                        .narrow_u8(module, span, width, "split width")?,
                });
                Ok(Value::pair(left, right))
            }
            PrimitiveId::Join => {
                let a =
                    self.quantum_argument(module, span, &args[0], false, source_args.first())?;
                let b =
                    self.quantum_argument(module, span, &args[1], false, source_args.optional(1))?;
                if a == b {
                    return Err(self.error(
                        module,
                        span,
                        ErrorCode::Ownership,
                        "join operands alias",
                    ));
                }
                let a = self.raw.registers.remove(&a).expect("owned register");
                let b = self.raw.registers.remove(&b).expect("owned register");
                if a.wires.len() + b.wires.len() > MAX_BITS {
                    return Err(self.error(
                        module,
                        span,
                        ErrorCode::Limit,
                        "joined register exceeds 12 bits",
                    ));
                }
                let mut wires = a.wires;
                wires.extend(b.wires);
                let value = self.register(Ty::pair(a.basis, b.basis), wires);
                let slot = self.quantum(module, span, &value, false)?;
                self.raw.operations.push(RawOp::Join {
                    left: a.token,
                    right: b.token,
                    output: self.raw.registers[&slot].token,
                });
                Ok(value)
            }

            PrimitiveId::MeasureZ | PrimitiveId::Discard => {
                let value = args.pop().expect("one input");
                let slot = self.quantum_argument(
                    module,
                    span,
                    &value,
                    primitive == PrimitiveId::MeasureZ,
                    source_args.first(),
                )?;
                if primitive == PrimitiveId::MeasureZ {
                    let output = self.raw.measure_z(slot).map_err(|failure| {
                        self.error(module, span, ErrorCode::InvalidIr, failure.to_string())
                    })?;
                    Ok(Value::Classical(output))
                } else {
                    let reg = self.raw.registers.remove(&slot).expect("owned register");
                    self.raw
                        .operations
                        .push(RawOp::Discard { input: reg.token });
                    Ok(Value::Unit)
                }
            }
            PrimitiveId::Phase
            | PrimitiveId::TakeBit
            | PrimitiveId::PutBit
            | PrimitiveId::PrependBit => Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "primitive requires its original checked natural arguments",
            )),
        }
    }
}
