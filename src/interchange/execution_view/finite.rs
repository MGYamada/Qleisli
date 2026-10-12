//! Read actual typed finite data without the QIRF encoder or decoder.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::{MAX_BYTES, Writer};
use crate::contract::exact::Matrix;
use crate::contract::{BasisType, FunctionEvidence};
use crate::interchange::{Error, Result};
use crate::ir::*;
use std::collections::BTreeMap;
use std::sync::Arc;

struct View<'a> {
    writer: Writer,
    dependencies: &'a BTreeMap<usize, usize>,
}

impl View<'_> {
    fn n(&mut self, n: usize) -> Result<()> {
        self.writer.natural(n)
    }

    fn record(
        &mut self,
        tag: &str,
        fields: usize,
        body: impl FnOnce(&mut Self) -> Result<()>,
    ) -> Result<()> {
        self.writer.sized(5, fields + 1)?;
        self.writer.depth += 1;
        let result = self.writer.text(tag).and_then(|_| body(self));
        self.writer.depth -= 1;
        result
    }

    fn list<T>(
        &mut self,
        values: &[T],
        mut body: impl FnMut(&mut Self, &T) -> Result<()>,
    ) -> Result<()> {
        self.writer.sized(5, values.len())?;
        self.writer.depth += 1;
        let result = (|| {
            for value in values {
                body(self, value)?;
            }
            Ok(())
        })();
        self.writer.depth -= 1;
        result
    }

    fn numbers<T: Copy + Into<u64>>(&mut self, values: &[T]) -> Result<()> {
        self.list(values, |w, n| {
            w.writer.append(&[3])?;
            w.writer.append(&(*n).into().to_le_bytes())
        })
    }

    fn axes(&mut self, axes: &[usize]) -> Result<()> {
        self.list(axes, |w, n| w.n(*n))
    }
    fn wires(&mut self, wires: &[WireId]) -> Result<()> {
        self.list(wires, |w, n| w.n(n.0 as usize))
    }

    fn effect(&mut self, effect: Effect) -> Result<()> {
        self.n(match effect {
            Effect::Unitary => 0,
            Effect::Isometry => 1,
            Effect::Observe => 2,
        })
    }

    fn port(&mut self, port: &QuantumPort) -> Result<()> {
        self.record("port", 3, |w| {
            w.n(port.token.0 as usize)?;
            w.wires(&port.wires)?;
            w.n(port.shape.bits as usize)
        })
    }

    fn basis(&mut self, basis: &BasisType) -> Result<()> {
        let mut pending = vec![basis];
        let mut prefix = vec![];
        while let Some(basis) = pending.pop() {
            prefix.push(basis);
            match basis {
                BasisType::Pair(a, b) => {
                    pending.push(b);
                    pending.push(a);
                }
                BasisType::Tuple(fields) => pending.extend(fields.iter().rev()),
                _ => {}
            }
        }
        self.list(&prefix, |w, atom| match atom {
            BasisType::Unit => w.record("unit", 0, |_| Ok(())),
            BasisType::Bit => w.record("bit", 0, |_| Ok(())),
            BasisType::Bits(width) => w.record("bits", 1, |w| w.n(*width as usize)),
            BasisType::Pair(..) => w.record("pair", 0, |_| Ok(())),
            BasisType::Tuple(fields) => w.record("tuple", 1, |w| w.n(fields.len())),
        })
    }

    fn gate(&mut self, gate: SingleGate) -> Result<()> {
        self.n(match gate {
            SingleGate::H => 0,
            SingleGate::X => 1,
            SingleGate::Z => 2,
            SingleGate::T => 3,
        })
    }

    fn phase(&mut self, phase: ScalarPhase) -> Result<()> {
        self.n(match phase {
            ScalarPhase::MinusOne => 0,
            ScalarPhase::EighthTurn => 1,
        })
    }

    fn unitary(&mut self, step: &UnitaryStep) -> Result<()> {
        match step {
            UnitaryStep::Gate {
                gate,
                target_index: target,
            } => self.record("gate", 2, |w| {
                w.gate(*gate)?;
                w.n(*target)
            }),
            UnitaryStep::Cnot {
                control_index: control,
                target_index: target,
            } => self.record("cnot", 2, |w| {
                w.n(*control)?;
                w.n(*target)
            }),
            UnitaryStep::Toffoli {
                control_a_index: control_a,
                control_b_index: control_b,
                target_index: target,
            } => self.record("toffoli", 3, |w| {
                w.n(*control_a)?;
                w.n(*control_b)?;
                w.n(*target)
            }),
            UnitaryStep::ScalarPhase(phase) => self.record("phase", 1, |w| w.phase(*phase)),
        }
    }

    fn step(&mut self, step: &CircuitStep) -> Result<()> {
        self.record("step", 2, |w| {
            w.list(&step.controls, |w, c| {
                w.record("control", 2, |w| {
                    w.n(c.index)?;
                    w.writer.append(&[if c.when_one { 2 } else { 1 }])
                })
            })?;
            match &step.action {
                CircuitAction::Hadamard { target } => w.record("hadamard", 1, |w| w.n(*target)),
                CircuitAction::Monomial {
                    indices,
                    permutation,
                    phases,
                } => w.record("monomial", 3, |w| {
                    w.axes(indices)?;
                    w.numbers(permutation)?;
                    w.numbers(phases)
                }),
                CircuitAction::Contract {
                    indices,
                    evidence,
                    adjoint,
                } => w.record("contract", 3, |w| {
                    w.axes(indices)?;
                    let id = w
                        .dependencies
                        .get(&(Arc::as_ptr(evidence) as usize))
                        .ok_or_else(|| {
                            Error::format(
                                "execution view references evidence outside its decoded graph",
                            )
                        })?;
                    w.n(*id)?;
                    w.writer.append(&[if *adjoint { 2 } else { 1 }])
                }),
            }
        })
    }

    fn protected_bit(&mut self, bit: ProtectedBit) -> Result<()> {
        self.record("protected-bit", 2, |w| {
            w.n(match bit.region {
                ProtectedRegion::Source => 0,
                ProtectedRegion::Ancilla => 1,
            })?;
            w.n(bit.index as usize)
        })
    }

    fn protected_controls(&mut self, controls: &[Control]) -> Result<()> {
        self.list(controls, |w, c| {
            w.record("protected-control", 2, |w| {
                w.protected_bit(c.bit)?;
                w.writer.append(&[if c.when_one { 2 } else { 1 }])
            })
        })
    }

    fn usage(&mut self, usage: &ProtectedUse) -> Result<()> {
        match usage {
            ProtectedUse::ProtectedGate { bit, gate } => self.record("protected-gate", 2, |w| {
                w.protected_bit(*bit)?;
                w.gate(*gate)
            }),
            ProtectedUse::ControlledTargetGate {
                controls,
                target_index,
                gate,
            } => self.record("target-gate", 3, |w| {
                w.protected_controls(controls)?;
                w.n(*target_index)?;
                w.gate(*gate)
            }),
            ProtectedUse::ControlledPhase { controls, phase } => {
                self.record("protected-phase", 2, |w| {
                    w.protected_controls(controls)?;
                    w.phase(*phase)
                })
            }
        }
    }

    fn operation(&mut self, op: &RawOp) -> Result<()> {
        match op {
            RawOp::PackUnit { output } => self.record("pack-unit", 1, |w| w.n(output.0 as usize)),
            RawOp::UnpackUnit { input } => self.record("unpack-unit", 1, |w| w.n(input.0 as usize)),
            RawOp::Init0 { output, wire } => self.record("init0", 2, |w| {
                w.n(output.0 as usize)?;
                w.n(wire.0 as usize)
            }),
            RawOp::Gate {
                gate,
                input,
                output,
            } => self.record("gate", 3, |w| {
                w.gate(*gate)?;
                w.n(input.0 as usize)?;
                w.n(output.0 as usize)
            }),
            RawOp::Cnot {
                control,
                target,
                control_out,
                target_out,
            } => self.record("cnot", 4, |w| {
                for x in [control, target, control_out, target_out] {
                    w.n(x.0 as usize)?;
                }
                Ok(())
            }),
            RawOp::Toffoli {
                control_a,
                control_b,
                target,
                control_a_out,
                control_b_out,
                target_out,
            } => self.record("toffoli", 6, |w| {
                for x in [
                    control_a,
                    control_b,
                    target,
                    control_a_out,
                    control_b_out,
                    target_out,
                ] {
                    w.n(x.0 as usize)?;
                }
                Ok(())
            }),
            RawOp::QuantumIf {
                control,
                target,
                control_out,
                target_out,
                zero_ops,
                one_ops,
            } => self.record("quantum-if", 6, |w| {
                for x in [control, target, control_out, target_out] {
                    w.n(x.0 as usize)?;
                }
                w.list(zero_ops, Self::unitary)?;
                w.list(one_ops, Self::unitary)
            }),
            RawOp::Split {
                input,
                left,
                right,
                left_bits,
            } => self.record("split", 4, |w| {
                for x in [input, left, right] {
                    w.n(x.0 as usize)?;
                }
                w.n(*left_bits as usize)
            }),
            RawOp::Join {
                left,
                right,
                output,
            } => self.record("join", 3, |w| {
                for x in [left, right, output] {
                    w.n(x.0 as usize)?;
                }
                Ok(())
            }),
            RawOp::LiftBasis {
                input,
                output,
                output_wires,
                table,
            } => self.record("lift-basis", 4, |w| {
                w.n(input.0 as usize)?;
                w.n(output.0 as usize)?;
                w.wires(output_wires)?;
                w.numbers(table)
            }),
            RawOp::ApplyUnitary {
                input,
                output,
                steps,
            } => self.record("apply-unitary", 3, |w| {
                w.n(input.0 as usize)?;
                w.n(output.0 as usize)?;
                w.list(steps, Self::step)
            }),
            RawOp::CertifiedCompute {
                source,
                source_out,
                ancilla_wires,
                function,
                use_steps,
                logical_steps,
            } => self.record("certified-compute", 6, |w| {
                w.n(source.0 as usize)?;
                w.n(source_out.0 as usize)?;
                w.wires(ancilla_wires)?;
                w.numbers(function)?;
                w.list(use_steps, Self::step)?;
                w.list(logical_steps, Self::step)
            }),
            RawOp::ComputeUseUncompute {
                source,
                source_out,
                targets,
                ancilla_wires,
                function,
                use_ops,
            } => self.record("compute-use-uncompute", 6, |w| {
                w.n(source.0 as usize)?;
                w.n(source_out.0 as usize)?;
                w.list(targets, |w, t| {
                    w.record("target", 2, |w| {
                        w.n(t.input.0 as usize)?;
                        w.n(t.output.0 as usize)
                    })
                })?;
                w.wires(ancilla_wires)?;
                w.numbers(function)?;
                w.list(use_ops, Self::usage)
            }),
            RawOp::MeasureZ { input, output } => self.record("measure", 2, |w| {
                w.n(input.0 as usize)?;
                w.n(output.0 as usize)
            }),
            RawOp::Reset {
                input,
                output,
                fresh_wire,
            } => self.record("reset", 3, |w| {
                w.n(input.0 as usize)?;
                w.n(output.0 as usize)?;
                w.n(fresh_wire.0 as usize)
            }),
            RawOp::Discard { input } => self.record("discard", 1, |w| w.n(input.0 as usize)),
            RawOp::ClassicalConst { value, output } => self.record("constant", 2, |w| {
                w.writer.append(&[if *value { 2 } else { 1 }])?;
                w.n(output.0 as usize)
            }),
            RawOp::ClassicalNot { input, output } => self.record("not", 2, |w| {
                w.n(input.0 as usize)?;
                w.n(output.0 as usize)
            }),
            RawOp::ClassicalXor {
                left,
                right,
                output,
            } => self.record("xor", 3, |w| {
                for x in [left, right, output] {
                    w.n(x.0 as usize)?;
                }
                Ok(())
            }),
            RawOp::ClassicalAnd {
                left,
                right,
                output,
            } => self.record("and", 3, |w| {
                for x in [left, right, output] {
                    w.n(x.0 as usize)?;
                }
                Ok(())
            }),
            RawOp::ClassicalBranch {
                condition,
                then_ops,
                else_ops,
                quantum_phis,
                classical_phis,
            } => self.record("branch", 5, |w| {
                w.n(condition.0 as usize)?;
                w.list(then_ops, Self::operation)?;
                w.list(else_ops, Self::operation)?;
                w.list(quantum_phis, |w, p| {
                    w.record("quantum-phi", 4, |w| {
                        for t in [p.then_token, p.else_token, p.output] {
                            w.n(t.0 as usize)?;
                        }
                        w.wires(&p.output_wires)
                    })
                })?;
                w.list(classical_phis, |w, p| {
                    w.record("classical-phi", 3, |w| {
                        for t in [p.then_id, p.else_id, p.output] {
                            w.n(t.0 as usize)?;
                        }
                        Ok(())
                    })
                })
            }),
        }
    }

    fn program(&mut self, program: &RawProgram) -> Result<()> {
        self.record("program", 6, |w| {
            w.list(&program.quantum_inputs, Self::port)?;
            w.list(&program.classical_inputs, |w, id| w.n(id.0 as usize))?;
            w.list(&program.operations, Self::operation)?;
            w.list(&program.quantum_outputs, |w, id| w.n(id.0 as usize))?;
            w.list(&program.classical_outputs, |w, id| w.n(id.0 as usize))?;
            w.effect(program.declared_effect)
        })
    }

    fn matrix(&mut self, matrix: &Matrix) -> Result<()> {
        self.record("matrix", 3, |w| {
            w.n(matrix.rows())?;
            w.n(matrix.cols())?;
            w.list(matrix.entries(), |w, scalar| {
                w.list(&scalar.dyadics(), |w, (n, e)| {
                    w.record("dyadic", 2, |w| {
                        w.writer.text(&n.to_string())?;
                        w.n(*e as usize)
                    })
                })
            })
        })
    }

    fn evidence(&mut self, evidence: &FunctionEvidence) -> Result<()> {
        self.record("function-evidence", 8, |w| {
            w.basis(evidence.signature())?;
            w.program(evidence.implementation())?;
            w.program(evidence.specification())?;
            let (implementation, specification, sources) = evidence.identity_parts();
            w.record("identity", 3, |w| {
                w.writer.text(implementation)?;
                w.writer.text(specification)?;
                w.list(sources, |w, (path, text)| {
                    w.record("source", 2, |w| {
                        w.writer.text(path)?;
                        w.writer.text(text)
                    })
                })
            })?;
            w.record("circuit", 2, |w| {
                w.basis(evidence.circuit().basis())?;
                w.list(evidence.circuit().steps(), Self::step)
            })?;
            w.matrix(evidence.meaning())?;
            w.n(evidence.depth())?;
            w.n(evidence.expanded_steps())
        })
    }
}

pub(super) fn raw(program: &RawProgram, dependencies: &[Arc<FunctionEvidence>]) -> Result<Vec<u8>> {
    let mut indices = BTreeMap::new();
    for (i, evidence) in dependencies.iter().enumerate() {
        if indices.insert(Arc::as_ptr(evidence) as usize, i).is_some() {
            return Err(Error::format("ambiguous execution-view evidence index"));
        }
    }
    let mut view = View {
        writer: Writer {
            bytes: b"QDV1".to_vec(),
            limit: MAX_BYTES,
            depth: 0,
        },
        dependencies: &indices,
    };
    view.program(program)?;
    Ok(view.writer.bytes)
}

#[cfg(test)]
mod tests;
