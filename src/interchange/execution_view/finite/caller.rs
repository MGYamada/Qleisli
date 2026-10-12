//! Untrusted descriptions of every actual caller evidence Arc, including aliases.
//! Original indices are proposed bindings; only the native comparison may validate them.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::interchange::{MAX_NODES, RootInterface};

pub(in crate::interchange) struct Origin<'a> {
    root: &'a RawProgram,
    interface: Option<&'a RootInterface>,
    aliases: Vec<(usize, Arc<FunctionEvidence>)>,
    indices: BTreeMap<usize, usize>,
}

fn charge(remaining: &mut usize) -> Result<()> {
    *remaining = remaining
        .checked_sub(1)
        .ok_or_else(|| Error::limit("caller evidence closure exceeds node capacity"))?;
    Ok(())
}

fn steps(
    body: &[CircuitStep],
    found: &mut Vec<Arc<FunctionEvidence>>,
    remaining: &mut usize,
) -> Result<()> {
    for step in body {
        charge(remaining)?;
        match &step.action {
            CircuitAction::Contract { evidence, .. } => found.push(evidence.clone()),
            CircuitAction::Hadamard { .. } | CircuitAction::Monomial { .. } => {}
        }
    }
    Ok(())
}

fn raw(
    body: &RawProgram,
    found: &mut Vec<Arc<FunctionEvidence>>,
    remaining: &mut usize,
) -> Result<()> {
    let mut pending: Vec<_> = body.operations.iter().rev().collect();
    while let Some(operation) = pending.pop() {
        charge(remaining)?;
        match operation {
            RawOp::ApplyUnitary { steps: body, .. } => steps(body, found, remaining)?,
            RawOp::CertifiedCompute {
                use_steps,
                logical_steps,
                ..
            } => {
                steps(use_steps, found, remaining)?;
                steps(logical_steps, found, remaining)?;
            }
            RawOp::ClassicalBranch {
                then_ops, else_ops, ..
            } => {
                pending.extend(else_ops.iter().rev());
                pending.extend(then_ops.iter().rev());
            }
            RawOp::PackUnit { .. }
            | RawOp::UnpackUnit { .. }
            | RawOp::Init0 { .. }
            | RawOp::Gate { .. }
            | RawOp::Cnot { .. }
            | RawOp::Toffoli { .. }
            | RawOp::QuantumIf { .. }
            | RawOp::Split { .. }
            | RawOp::Join { .. }
            | RawOp::LiftBasis { .. }
            | RawOp::MeasureZ { .. }
            | RawOp::Reset { .. }
            | RawOp::Discard { .. }
            | RawOp::ClassicalConst { .. }
            | RawOp::ClassicalNot { .. }
            | RawOp::ClassicalXor { .. }
            | RawOp::ClassicalAnd { .. }
            | RawOp::ComputeUseUncompute { .. } => {}
        }
    }
    Ok(())
}

impl<'a> Origin<'a> {
    /// Canonical snapshot lookup proposes an original index, never equality of
    /// the actual body or caches. Every distinct actual Arc is still retained,
    /// and its implementation/specification/cached-circuit children are visited.
    pub(in crate::interchange) fn collect(
        root: &'a RawProgram,
        interface: Option<&'a RootInterface>,
        canonical: &BTreeMap<Arc<[u8]>, usize>,
    ) -> Result<Self> {
        let mut remaining = MAX_NODES;
        let mut found = vec![];
        raw(root, &mut found, &mut remaining)?;
        let mut pending: Vec<_> = found.into_iter().rev().collect();
        let mut aliases = vec![];
        let mut indices = BTreeMap::new();
        while let Some(evidence) = pending.pop() {
            let pointer = Arc::as_ptr(&evidence) as usize;
            if indices.contains_key(&pointer) {
                continue;
            }
            charge(&mut remaining)?;
            let index = *canonical.get(evidence.snapshot_key()).ok_or_else(|| {
                Error::format("caller cache references evidence absent from original artifact")
            })?;
            indices.insert(pointer, index);
            let mut children = vec![];
            raw(evidence.implementation(), &mut children, &mut remaining)?;
            raw(evidence.specification(), &mut children, &mut remaining)?;
            steps(evidence.circuit().steps(), &mut children, &mut remaining)?;
            pending.extend(children.into_iter().rev());
            aliases.push((index, evidence));
        }
        Ok(Self {
            root,
            interface,
            aliases,
            indices,
        })
    }

    pub(in crate::interchange) fn describe(&self) -> Result<Vec<u8>> {
        let mut writer = Writer {
            bytes: b"QDV1".to_vec(),
            limit: MAX_BYTES,
            depth: 0,
        };
        let mut view = View {
            writer: &mut writer,
            dependencies: &self.indices,
        };
        view.record("caller-origin", 3, |w| {
            if let Some(interface) = self.interface {
                w.record("root-interface", 2, |w| {
                    w.basis(&interface.input)?;
                    w.basis(&interface.output)
                })?;
            } else {
                w.writer.append(&[0])?;
            }
            w.program(self.root)?;
            w.list(&self.aliases, |w, (index, evidence)| {
                w.record("evidence-alias", 2, |w| {
                    w.n(*index)?;
                    w.evidence(evidence)
                })
            })
        })?;
        Ok(writer.bytes)
    }
}

#[cfg(test)]
mod tests;
