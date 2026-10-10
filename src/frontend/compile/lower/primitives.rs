//! Sealed primitive signatures, ownership transitions, effects, and raw IR.
//!
//! This is the source-side check. The independent verifier rechecks emitted IR
//! without calling these methods or trusting frontend ownership bookkeeping.

use super::super::{CompileError, ErrorCode, MAX_BITS, Ty};
use super::{Lowerer, Slot, Value};
use crate::frontend::ast::{Expr, ExprKind, RuntimeArguments, Span};
use crate::ir::{Effect, RawOp, SingleGate};
use std::collections::BTreeSet;

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

    pub(super) fn sealed(
        &mut self,
        module: &str,
        span: Span,
        namespace: &str,
        name: &str,
        args: Vec<Value>,
    ) -> Result<Value, CompileError> {
        self.sealed_with_source(
            module,
            span,
            namespace,
            name,
            args,
            RuntimeArguments::Values(&[]),
        )
    }

    pub(super) fn sealed_with_source(
        &mut self,
        module: &str,
        span: Span,
        namespace: &str,
        name: &str,
        mut args: Vec<Value>,
        source_args: RuntimeArguments<'_>,
    ) -> Result<Value, CompileError> {
        let declaration = crate::frontend::core::primitive(namespace, name).ok_or_else(|| {
            if crate::frontend::check::primitive::Primitive::lookup(&format!("{namespace}::{name}"))
                .is_some()
            {
                self.error(
                    module,
                    span,
                    ErrorCode::Unsupported,
                    format!("finite lowering profile does not support `{namespace}::{name}`"),
                )
            } else {
                self.error(
                    module,
                    span,
                    ErrorCode::UnknownName,
                    "unknown sealed primitive",
                )
            }
        })?;
        let arity = declaration.arity;
        if args.len() != arity {
            return Err(self.error(
                module,
                span,
                ErrorCode::Arity,
                format!("{name} requires {arity} arguments"),
            ));
        }
        self.add_effect(
            module,
            span,
            match declaration.kind {
                crate::frontend::ast::FnKind::Unitary => Effect::Unitary,
                crate::frontend::ast::FnKind::Iso => Effect::Iso,
                crate::frontend::ast::FnKind::Observe => Effect::Observe,
                _ => unreachable!("sealed quantum declaration"),
            },
        );
        match name {
            "unit" => {
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
            "finish" => {
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
            "init0" => {
                let slot = self.raw.init0();
                Ok(Value::quantum(slot, Ty::bit()))
            }
            "h" | "x" | "z" | "t" | "s" | "sdg" | "tdg" => {
                let value = args.pop().expect("one argument");
                let slot =
                    self.quantum_argument(module, span, &value, true, source_args.first())?;
                let gate = match name {
                    "h" => SingleGate::H,
                    "x" => SingleGate::X,
                    "z" => SingleGate::Z,
                    _ => SingleGate::T,
                };
                // These source aliases introduce no gate kind or acceptance rule.
                let repetitions = match name {
                    "s" => 2,
                    "sdg" => 6,
                    "tdg" => 7,
                    _ => 1,
                };
                for _ in 0..repetitions {
                    self.raw.gate_bit(gate, slot).map_err(|failure| {
                        self.error(module, span, ErrorCode::InvalidIr, failure.to_string())
                    })?;
                }
                Ok(value)
            }
            "id" | "phase_eighth" => {
                let value = args.pop().expect("one argument");
                let slot =
                    self.quantum_argument(module, span, &value, false, source_args.first())?;
                if name == "phase_eighth" {
                    self.raw.scalar_eighth(slot).map_err(|failure| {
                        self.error(module, span, ErrorCode::InvalidIr, failure.to_string())
                    })?;
                }
                Ok(value)
            }
            "cnot" | "toffoli" => {
                let slots = args
                    .iter()
                    .enumerate()
                    .map(|(index, arg)| {
                        self.quantum_argument(module, span, arg, true, source_args.optional(index))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                if slots.iter().collect::<BTreeSet<_>>().len() != slots.len() {
                    return Err(self.error(
                        module,
                        span,
                        ErrorCode::Ownership,
                        "gate operands alias one quantum register",
                    ));
                }
                if name == "cnot" {
                    self.raw.cnot(slots[0], slots[1]).map_err(|failure| {
                        self.error(module, span, ErrorCode::InvalidIr, failure.to_string())
                    })?;
                } else {
                    let inputs: Vec<_> = slots
                        .iter()
                        .map(|slot| self.raw.registers[slot].token)
                        .collect();
                    let outputs: Vec<_> = slots.iter().map(|_| self.token()).collect();
                    self.raw.operations.push(RawOp::Toffoli {
                        control_a: inputs[0],
                        control_b: inputs[1],
                        target: inputs[2],
                        control_a_out: outputs[0],
                        control_b_out: outputs[1],
                        target_out: outputs[2],
                    });
                    for (slot, output) in slots.iter().zip(outputs) {
                        self.raw
                            .registers
                            .get_mut(slot)
                            .expect("owned register")
                            .token = output;
                    }
                }
                let mut args = args.into_iter();
                let a = args.next().expect("first input");
                let b = args.next().expect("second input");
                let pair = Value::pair(a, b);
                Ok(if let Some(target) = args.next() {
                    Value::pair(pair, target)
                } else {
                    pair
                })
            }
            "split" => {
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
            "join" => {
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
            "measure_z" | "reset" | "discard" => {
                let value = args.pop().expect("one input");
                let slot = self.quantum_argument(
                    module,
                    span,
                    &value,
                    name != "discard",
                    source_args.first(),
                )?;
                if name == "measure_z" {
                    let output = self.raw.measure_z(slot).map_err(|failure| {
                        self.error(module, span, ErrorCode::InvalidIr, failure.to_string())
                    })?;
                    Ok(Value::Classical(output))
                } else if name == "discard" {
                    let reg = self.raw.registers.remove(&slot).expect("owned register");
                    self.raw
                        .operations
                        .push(RawOp::Discard { input: reg.token });
                    Ok(Value::Unit)
                } else {
                    let reg = self.raw.registers.remove(&slot).expect("owned register");
                    let wire = self.wire();
                    let value = self.register(Ty::bit(), vec![wire]);
                    let slot = self.quantum(module, span, &value, true)?;
                    self.raw.operations.push(RawOp::Reset {
                        input: reg.token,
                        output: self.raw.registers[&slot].token,
                        fresh_wire: wire,
                    });
                    Ok(value)
                }
            }
            _ => Err(self.error(
                module,
                span,
                ErrorCode::Unsupported,
                "unsupported sealed operation",
            )),
        }
    }
}
