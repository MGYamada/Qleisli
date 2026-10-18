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
                .saturating_add(total_size(self.raw.registers.values().map(Register::size)))
                .saturating_mul(2),
        )?;
        let entry_registers = self.raw.registers.clone();
        let outer_ops = std::mem::take(&mut self.raw.operations);
        let outer_sources = std::mem::take(&mut self.operation_sources);
        let entry_effect = self.effect;
        let entry_contract_effect = self.contract_effect;
        let entry_effect_source = self.effect_source.clone();
        let mut then_env = env.clone();
        let then_result = self.block(module, then_block, &mut then_env)?;
        let then_ops = std::mem::take(&mut self.raw.operations);
        let then_sources = std::mem::take(&mut self.operation_sources);
        let mut then_registers =
            std::mem::replace(&mut self.raw.registers, entry_registers.clone());
        let then_effect = self.effect;
        let then_contract_effect = self.contract_effect;
        let then_effect_source = self.effect_source.take();
        self.effect = entry_effect;
        self.contract_effect = entry_contract_effect;
        self.effect_source = entry_effect_source;
        let mut else_env = env.clone();
        let else_result = self.block(module, else_block, &mut else_env)?;
        let else_ops = std::mem::replace(&mut self.raw.operations, outer_ops);
        let else_sources = std::mem::replace(&mut self.operation_sources, outer_sources);
        let mut else_registers = std::mem::take(&mut self.raw.registers);
        if then_contract_effect >= self.contract_effect {
            self.effect_source = then_effect_source;
        }
        self.effect = self.effect.max(then_effect);
        self.contract_effect = self.contract_effect.max(then_contract_effect);
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
                format!("if arms must return the same type: expected `{}` from the then arm, found `{}` in the else arm", then_result.ty().runtime(), else_result.ty().runtime()),
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
        let branch_index = self.raw.operations.len();
        for (arm, sources) in [(0, then_sources), (1, else_sources)] {
            for (path, source) in sources {
                let mut nested_path = vec![branch_index, arm];
                nested_path.extend(path);
                self.operation_sources.insert(nested_path, source);
            }
        }
        self.raw.operations.push(RawOp::ClassicalBranch {
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
        self.raw.registers.insert(
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
            (Value::EmptyBits, Value::EmptyBits) => Ok(Value::EmptyBits),
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
            (Value::Bits(a), Value::Bits(b)) if a.len() == b.len() => {
                // Retain the word constructor and original bit order. Its
                // component phis remain simultaneous Raw classical outputs.
                let growth = if classical.len().saturating_add(a.len()) > classical.capacity() {
                    classical.len().saturating_mul(3)
                } else {
                    0
                };
                self.compiler.charge(
                    module,
                    span,
                    a.len()
                        .saturating_mul(6)
                        .saturating_add(growth)
                        .saturating_add(1),
                )?;
                classical.reserve_exact(a.len());
                let mut outputs = Vec::with_capacity(a.len());
                for (a, b) in a.into_iter().zip(b) {
                    let output = if a == b {
                        a
                    } else {
                        let output = self.classical();
                        classical.push(ClassicalPhi {
                            then_id: a,
                            else_id: b,
                            output,
                        });
                        output
                    };
                    outputs.push(output);
                }
                Ok(Value::bits(outputs))
            }
            (Value::Quantum(a, ty), Value::Quantum(b, _)) => {
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
                Ok(Value::Quantum(slot, ty))
            }
            (Value::Pair(a1, a2), Value::Pair(b1, b2)) => {
                let a =
                    self.merge_results(module, span, *a1, *b1, a_regs, b_regs, quantum, classical)?;
                let b =
                    self.merge_results(module, span, *a2, *b2, a_regs, b_regs, quantum, classical)?;
                Ok(Value::pair(a, b))
            }
            (Value::Tuple(a), Value::Tuple(b)) if a.len() == b.len() => {
                let fields = a
                    .into_iter()
                    .zip(b)
                    .map(|(a, b)| {
                        self.merge_results(module, span, a, b, a_regs, b_regs, quantum, classical)
                    })
                    .collect::<Result<_, _>>()?;
                Ok(Value::Tuple(fields))
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

#[cfg(test)]
mod tests {
    use super::super::{call_state_tests::checked_compiler, *};
    use super::*;
    use crate::frontend::project::{ModuleOrigin, SourceModule};

    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    #[test]
    fn word_phis_keep_order_reuse_inherited_bits_and_reserve_before_issuing_ids() {
        let text = "unitary fn unused()->Unit{()}";
        let project = Project {
            edition_context: crate::frontend::project::ProjectEdition::Explicit(
                crate::edition::Edition::E2026,
            ),
            root: PathBuf::from("main.qli"),
            modules: BTreeMap::from([(
                "main".into(),
                SourceModule {
                    name: "main".into(),
                    path: PathBuf::from("main.qli"),
                    source: text.into(),
                    ast: crate::frontend::parser::parse_module(text).unwrap(),
                    imports: BTreeMap::new(),
                    origin: ModuleOrigin::Local,
                },
            )]),
        };
        let mut compiler = checked_compiler(&project);
        for remaining in [0, MAX_WORK] {
            compiler.work = MAX_WORK - remaining;
            let mut lower = Lowerer {
                compiler: &mut compiler,
                raw: RawState::new(),
                operation_sources: BTreeMap::new(),
                instrument_calls: Vec::new(),
                tuple_binding_origins: Vec::new(),
                access_updates: Vec::new(),
                effect: Effect::Unitary,
                contract_effect: Effect::Unitary,
                effect_source: None,
                depth: 0,
                bindings: BTreeMap::new(),
            };
            let ids: Vec<_> = (0..5).map(|_| lower.classical()).collect();
            let mut phis = Vec::new();
            let result = lower.merge_results(
                "main",
                Span::default(),
                Value::Bits(vec![ids[0], ids[1], ids[2]]),
                Value::Bits(vec![ids[0], ids[3], ids[4]]),
                &mut BTreeMap::new(),
                &mut BTreeMap::new(),
                &mut Vec::new(),
                &mut phis,
            );
            if remaining == 0 {
                assert_eq!(result.unwrap_err().code, ErrorCode::Limit);
                assert!(phis.is_empty());
                assert_eq!(lower.classical(), ClassicalId(5));
            } else {
                assert_eq!(
                    result.unwrap(),
                    Value::Bits(vec![ids[0], ClassicalId(5), ClassicalId(6)])
                );
                assert_eq!(
                    phis,
                    vec![
                        ClassicalPhi {
                            then_id: ids[1],
                            else_id: ids[3],
                            output: ClassicalId(5)
                        },
                        ClassicalPhi {
                            then_id: ids[2],
                            else_id: ids[4],
                            output: ClassicalId(6)
                        },
                    ]
                );
                assert_eq!(lower.classical(), ClassicalId(7));
            }
        }
    }
}
