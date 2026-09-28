//! Classical branch snapshots and complete result/frame phi interfaces.
//!
//! Merge returned quantum leaves by result position, then every surviving
//! caller or pending-argument slot. Keep globally fresh IDs across both arms.
//! Renaming a wire at a phi preserves its correlations; it prepares no state.

use super::super::{CompileError, ErrorCode, total_size};
use super::{Env, Lowerer, Register, Slot, Value, env_size};
use crate::frontend::ast::{Block, Span};
use crate::ir::{ClassicalId, ClassicalPhi, QuantumPhi, RawOp};
use std::collections::BTreeMap;

impl Lowerer<'_, '_> {
    pub(super) fn branch(
        &mut self,
        module: &str,
        span: Span,
        condition: ClassicalId,
        then_block: &Block,
        else_block: &Block,
        env: &mut Env,
    ) -> Result<Value, CompileError> {
        self.compiler.charge(
            module,
            span,
            env_size(env)
                .saturating_add(total_size(self.registers.values().map(Register::size)))
                .saturating_mul(2),
        )?;
        let entry_registers = self.registers.clone();
        let outer_ops = std::mem::take(&mut self.operations);
        let outer_sources = std::mem::take(&mut self.operation_sources);
        let entry_effect = self.effect;
        let mut then_env = env.clone();
        let then_result = self.block(module, then_block, &mut then_env)?;
        let then_ops = std::mem::take(&mut self.operations);
        let then_sources = std::mem::take(&mut self.operation_sources);
        let mut then_registers = std::mem::replace(&mut self.registers, entry_registers.clone());
        let then_effect = self.effect;
        self.effect = entry_effect;
        let mut else_env = env.clone();
        let else_result = self.block(module, else_block, &mut else_env)?;
        let else_ops = std::mem::replace(&mut self.operations, outer_ops);
        let else_sources = std::mem::replace(&mut self.operation_sources, outer_sources);
        let mut else_registers = std::mem::take(&mut self.registers);
        self.effect = self.effect.max(then_effect);
        if then_env != else_env {
            return Err(self.error(
                module,
                span,
                ErrorCode::Ownership,
                "if arms consume different outer quantum bindings",
            ));
        }
        *env = then_env;
        self.compiler.charge(
            module,
            span,
            then_result
                .tree_size()
                .nodes
                .saturating_add(else_result.tree_size().nodes),
        )?;
        if then_result.ty() != else_result.ty() {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                format!("if arms must return the same type: expected `{}` from the then arm, found `{}` in the else arm", then_result.ty(), else_result.ty()),
            ));
        }
        let mut quantum_phis = Vec::new();
        let mut classical_phis = Vec::new();
        let result = self.merge_results(
            module,
            span,
            then_result,
            else_result,
            &mut then_registers,
            &mut else_registers,
            &mut quantum_phis,
            &mut classical_phis,
        )?;
        if then_registers.len() != else_registers.len() {
            return Err(self.error(
                module,
                span,
                ErrorCode::Ownership,
                "if arms leave incompatible quantum frames",
            ));
        }
        for (slot, then_reg) in then_registers {
            if !entry_registers.contains_key(&slot) {
                return Err(self.error(
                    module,
                    span,
                    ErrorCode::Ownership,
                    "branch-local ownership was not returned",
                ));
            }
            let else_reg = else_registers.remove(&slot).ok_or_else(|| {
                self.error(
                    module,
                    span,
                    ErrorCode::Ownership,
                    "if arms leave incompatible quantum frames",
                )
            })?;
            self.merge_register(module, span, slot, then_reg, else_reg, &mut quantum_phis)?;
        }
        let branch_index = self.operations.len();
        for (arm, sources) in [(0, then_sources), (1, else_sources)] {
            for (path, source) in sources {
                let mut nested_path = vec![branch_index, arm];
                nested_path.extend(path);
                self.operation_sources.insert(nested_path, source);
            }
        }
        self.operations.push(RawOp::ClassicalBranch {
            condition,
            then_ops,
            else_ops,
            quantum_phis,
            classical_phis,
        });
        Ok(result)
    }

    fn merge_register(
        &mut self,
        module: &str,
        span: Span,
        slot: Slot,
        a: Register,
        b: Register,
        phis: &mut Vec<QuantumPhi>,
    ) -> Result<(), CompileError> {
        self.compiler.tick(module, span)?;
        if a.basis != b.basis {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                format!(
                    "branch quantum shapes differ: expected `Q<{}>`, found `Q<{}>`",
                    a.basis, b.basis
                ),
            ));
        }
        let token = self.token();
        let wires: Vec<_> = (0..a.wires.len()).map(|_| self.wire()).collect();
        phis.push(QuantumPhi {
            then_token: a.token,
            else_token: b.token,
            output: token,
            output_wires: wires.clone(),
        });
        self.registers.insert(
            slot,
            Register {
                token,
                wires,
                basis: a.basis,
            },
        );
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn merge_results(
        &mut self,
        module: &str,
        span: Span,
        a: Value,
        b: Value,
        a_regs: &mut BTreeMap<Slot, Register>,
        b_regs: &mut BTreeMap<Slot, Register>,
        quantum: &mut Vec<QuantumPhi>,
        classical: &mut Vec<ClassicalPhi>,
    ) -> Result<Value, CompileError> {
        match (a, b) {
            (Value::Unit, Value::Unit) => Ok(Value::Unit),
            (Value::Classical(a), Value::Classical(b)) => {
                if a == b {
                    return Ok(Value::Classical(a));
                }
                let output = self.classical();
                classical.push(ClassicalPhi {
                    then_id: a,
                    else_id: b,
                    output,
                });
                Ok(Value::Classical(output))
            }
            (Value::Quantum(a, basis), Value::Quantum(b, _)) => {
                let a = a_regs.remove(&a).ok_or_else(|| {
                    self.error(
                        module,
                        span,
                        ErrorCode::Ownership,
                        "then result duplicates quantum ownership",
                    )
                })?;
                let b = b_regs.remove(&b).ok_or_else(|| {
                    self.error(
                        module,
                        span,
                        ErrorCode::Ownership,
                        "else result duplicates quantum ownership",
                    )
                })?;
                let slot = self.slot();
                self.merge_register(module, span, slot, a, b, quantum)?;
                Ok(Value::Quantum(slot, basis))
            }
            (Value::Pair(a1, a2), Value::Pair(b1, b2)) => {
                let a =
                    self.merge_results(module, span, *a1, *b1, a_regs, b_regs, quantum, classical)?;
                let b =
                    self.merge_results(module, span, *a2, *b2, a_regs, b_regs, quantum, classical)?;
                Ok(Value::pair(a, b))
            }
            _ => Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "incompatible branch result types",
            )),
        }
    }
}
