//! Sealed primitive signatures, ownership transitions, effects, and raw IR.
//!
//! This is the source-side check. The independent verifier rechecks emitted IR
//! without calling these methods or trusting frontend ownership bookkeeping.

use super::super::{CompileError, ErrorCode, MAX_BITS, Ty};
use super::{Lowerer, Slot, Value};
use crate::frontend::ast::Span;
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
        let Value::Quantum(slot, basis) = value else {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                format!(
                    "operation requires quantum ownership: expected `{}`, found `{}`",
                    if bit_only { "Q<Bit>" } else { "Q<A>" },
                    value.ty()
                ),
            ));
        };
        if bit_only && *basis != Ty::Bit {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                format!(
                    "operation requires Q<Bit>: expected `Q<Bit>`, found `{}`",
                    value.ty()
                ),
            ));
        }
        Ok(*slot)
    }

    pub(super) fn sealed(
        &mut self,
        module: &str,
        span: Span,
        namespace: &str,
        name: &str,
        mut args: Vec<Value>,
    ) -> Result<Value, CompileError> {
        let arity = match name {
            "init0" => 0,
            "cnot" | "join" => 2,
            "toffoli" => 3,
            _ => 1,
        };
        if args.len() != arity {
            return Err(self.error(
                module,
                span,
                ErrorCode::Arity,
                format!("{name} requires {arity} arguments"),
            ));
        }
        if namespace == "std::observe" {
            self.add_effect(module, span, Effect::Observe);
        }
        match name {
            "init0" => {
                self.add_effect(module, span, Effect::Iso);
                let wire = self.wire();
                let value = self.register(Ty::Bit, vec![wire]);
                let slot = self.quantum(module, span, &value, true)?;
                self.operations.push(RawOp::Init0 {
                    output: self.registers[&slot].token,
                    wire,
                });
                Ok(value)
            }
            "h" | "x" | "z" | "t" => {
                let value = args.pop().expect("one argument");
                let slot = self.quantum(module, span, &value, true)?;
                let gate = match name {
                    "h" => SingleGate::H,
                    "x" => SingleGate::X,
                    "z" => SingleGate::Z,
                    _ => SingleGate::T,
                };
                let output = self.token();
                let reg = self.registers.get_mut(&slot).expect("owned register");
                self.operations.push(RawOp::Gate {
                    gate,
                    input: reg.token,
                    output,
                });
                reg.token = output;
                Ok(value)
            }
            "cnot" | "toffoli" => {
                let slots = args
                    .iter()
                    .map(|arg| self.quantum(module, span, arg, true))
                    .collect::<Result<Vec<_>, _>>()?;
                if slots.iter().collect::<BTreeSet<_>>().len() != slots.len() {
                    return Err(self.error(
                        module,
                        span,
                        ErrorCode::Ownership,
                        "gate operands alias one quantum register",
                    ));
                }
                let inputs: Vec<_> = slots
                    .iter()
                    .map(|slot| self.registers[slot].token)
                    .collect();
                let outputs: Vec<_> = slots.iter().map(|_| self.token()).collect();
                self.operations.push(if name == "cnot" {
                    RawOp::Cnot {
                        control: inputs[0],
                        target: inputs[1],
                        control_out: outputs[0],
                        target_out: outputs[1],
                    }
                } else {
                    RawOp::Toffoli {
                        control_a: inputs[0],
                        control_b: inputs[1],
                        target: inputs[2],
                        control_a_out: outputs[0],
                        control_b_out: outputs[1],
                        target_out: outputs[2],
                    }
                });
                for (slot, output) in slots.iter().zip(outputs) {
                    self.registers.get_mut(slot).expect("owned register").token = output;
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
                let slot = self.quantum(module, span, &value, false)?;
                let reg = self.registers.remove(&slot).expect("owned register");
                let Ty::Pair(a, b) = reg.basis else {
                    return Err(self.error(
                        module,
                        span,
                        ErrorCode::TypeMismatch,
                        "split requires Q<(A, B)>",
                    ));
                };
                let width = a.basis_bits().expect("basis type");
                let left = self.register(*a, reg.wires[..width].to_vec());
                let right = self.register(*b, reg.wires[width..].to_vec());
                let left_slot = self.quantum(module, span, &left, false)?;
                let right_slot = self.quantum(module, span, &right, false)?;
                self.operations.push(RawOp::Split {
                    input: reg.token,
                    left: self.registers[&left_slot].token,
                    right: self.registers[&right_slot].token,
                    left_bits: width as u8,
                });
                Ok(Value::pair(left, right))
            }
            "join" => {
                let a = self.quantum(module, span, &args[0], false)?;
                let b = self.quantum(module, span, &args[1], false)?;
                if a == b {
                    return Err(self.error(
                        module,
                        span,
                        ErrorCode::Ownership,
                        "join operands alias",
                    ));
                }
                let a = self.registers.remove(&a).expect("owned register");
                let b = self.registers.remove(&b).expect("owned register");
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
                self.operations.push(RawOp::Join {
                    left: a.token,
                    right: b.token,
                    output: self.registers[&slot].token,
                });
                Ok(value)
            }
            "measure_z" | "reset" | "discard" => {
                let value = args.pop().expect("one input");
                let slot = self.quantum(module, span, &value, name != "discard")?;
                let reg = self.registers.remove(&slot).expect("owned register");
                if name == "measure_z" {
                    let output = self.classical();
                    self.operations.push(RawOp::MeasureZ {
                        input: reg.token,
                        output,
                    });
                    Ok(Value::Classical(output))
                } else if name == "discard" {
                    self.operations.push(RawOp::Discard { input: reg.token });
                    Ok(Value::Unit)
                } else {
                    let wire = self.wire();
                    let value = self.register(Ty::Bit, vec![wire]);
                    let slot = self.quantum(module, span, &value, true)?;
                    self.operations.push(RawOp::Reset {
                        input: reg.token,
                        output: self.registers[&slot].token,
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
