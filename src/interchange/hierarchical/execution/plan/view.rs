//! Describe the actual retained plan, without reading the artifact or bridge.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::interchange::execution_view::finite::{View, without_dependencies};

impl Program {
    fn write_view(&self, w: &mut View<'_>) -> Result<()> {
        w.record("hierarchy-program", 4, |w| {
            w.list(&self.nodes, |w, node| {
                w.record("node", 2, |w| {
                    w.n(node.width)?;
                    match &node.op {
                        Op::Leaf(matrix) => w.record("leaf", 1, |w| w.matrix(matrix)),
                        Op::Sequence(children) => w.record("sequence", 1, |w| w.axes(children)),
                        Op::Tensor(left, right) => w.record("tensor", 2, |w| {
                            w.n(*left)?;
                            w.n(*right)
                        }),
                        Op::Repeat(child, count) => w.record("repeat", 2, |w| {
                            w.n(*child)?;
                            w.n(*count)
                        }),
                        Op::Inverse(child) => w.record("inverse", 1, |w| w.n(*child)),
                        Op::Control(child, polarity) => w.record("control", 2, |w| {
                            w.n(*child)?;
                            w.boolean(*polarity)
                        }),
                        Op::Permutation(axes) => w.record("permutation", 1, |w| w.axes(axes)),
                        Op::Phase { target, j, k } => w.record("phase", 3, |w| {
                            w.n(*target)?;
                            w.n(*j)?;
                            w.n(*k)
                        }),
                    }
                })
            })?;
            w.n(self.root)?;
            w.axes(&self.inputs)?;
            w.axes(&self.outputs)
        })
    }
}

impl Plan {
    pub(super) fn view(&self) -> Result<Vec<u8>> {
        without_dependencies(|w| {
            w.record("hierarchy-plan", 1, |w| match &self.inner {
                Executable::Pure(program) => w.record("pure", 1, |w| program.write_view(w)),
                Executable::Instrument(plan) => w.record("instrument", 9, |w| {
                    plan.program.write_view(w)?;
                    w.axes(&plan.input_axes)?;
                    w.axes(&plan.fresh_axes)?;
                    w.axes(&plan.input_positions)?;
                    w.list(&plan.measurements, |w, (value, axis)| {
                        w.record("measurement", 2, |w| {
                            w.n(*value)?;
                            w.n(*axis)
                        })
                    })?;
                    w.axes(&plan.pack)?;
                    w.axes(&plan.outcome_positions)?;
                    w.axes(&plan.residual_axes)?;
                    w.axes(&plan.residual_positions)
                }),
            })
        })
    }
}
