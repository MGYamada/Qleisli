//! Retain original Raw source obligations behind an executed native provider leaf.
//! The zero-repeat hierarchy dependency retains dormant original children only;
//! it does not prove equality between the source graph and the executed leaf.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;
use crate::contract::{DEFAULT_EXACT_WORK, exact::Budget};
use crate::frontend::specialize::raw::SourceOperationWitness;
use std::sync::Arc;

/// Private linkage to an original checked Raw proposal, never a serialized authority.
#[derive(Clone, Debug)]
pub(in crate::frontend::specialize::lower) struct NativeSourceTrace {
    pub(super) node: usize,
    pub(super) original: usize,
    pub(super) actual: usize,
    pub(super) witness: Arc<SourceOperationWitness>,
}

impl Lower<'_> {
    /// Keep the actual checked leaf and the original source's dormant dependencies.
    pub(in crate::frontend::specialize::lower) fn native_source_operation(
        &mut self,
        operation: &SourceOperation,
        leaf: &crate::interchange::finite_leaf::CheckedUnitaryLeaf,
        witness: Arc<SourceOperationWitness>,
    ) -> Result<usize> {
        if self.native_sources.len() >= 10_000 {
            return Err(limit(
                "native source witnesses exceed original operation capacity",
            ));
        }
        // Only these index/Arc cells are new here. The shared Raw witness owns
        // and charges its retained bytes once when the original check is made.
        let cells = self
            .pure_trace_cells
            .checked_add(8)
            .ok_or_else(|| limit("native source metadata accounting overflow"))?;
        if cells > 100_000 {
            return Err(limit("native source metadata exceeds retained cell budget"));
        }
        self.pure_trace_cells = cells;
        self.graph.charge(64)?;
        let original = self.operation_source(operation)?;
        let actual = self.native_operation(leaf)?;
        let input = self.graph.nodes[actual].before.clone();
        let (bound, output) = self.bind_operation(original, input.clone())?;
        let rename = self.graph.rename(output, input.clone())?;
        let closed = self.graph.sequence(vec![bound, rename])?;
        let retained = self.graph.add(
            input.clone(),
            input,
            tagged(
                "repeat",
                &[("definition", closed.to_string()), ("count", "0".into())],
            ),
            tagged(
                "power",
                &[("child", closed.to_string()), ("count", "0".into())],
            ),
            "repeat",
            vec![closed],
        )?;
        let node = self.graph.sequence(vec![retained, actual])?;
        self.native_sources.push(NativeSourceTrace {
            node,
            original,
            actual,
            witness,
        });
        Ok(node)
    }
}

/// Preserve both retained node references under the existing graph compaction.
pub(super) fn remap(
    traces: &mut [NativeSourceTrace],
    mapping: &BTreeMap<usize, usize>,
) -> Result<()> {
    for trace in traces {
        trace.node = *mapping
            .get(&trace.node)
            .ok_or_else(|| p::invalid("compaction omitted an actual native source operation"))?;
        trace.actual = *mapping
            .get(&trace.actual)
            .ok_or_else(|| p::invalid("compaction omitted the actual checked native provider"))?;
        trace.original = *mapping
            .get(&trace.original)
            .ok_or_else(|| p::invalid("compaction omitted original native source dependencies"))?;
    }
    Ok(())
}

/// Replay each immutable original Raw witness once under one shared exact budget.
pub(super) fn validate(
    proposal: &HierarchyProposal,
    graph: &Value,
    reachable: &BTreeSet<usize>,
) -> Result<()> {
    let defs = p::array(p::field(graph, "definitions")?)?;
    let meanings = p::array(p::field(graph, "meanings")?)?;
    let proofs = p::array(p::field(graph, "proofs")?)?;
    let mut nodes = BTreeSet::new();
    let mut witnesses = BTreeSet::new();
    let mut budget = Budget::new(DEFAULT_EXACT_WORK);
    if proposal.native_sources.len() > 10_000 {
        return Err(p::invalid(
            "native source witnesses exceed original operation capacity",
        ));
    }
    for trace in &proposal.native_sources {
        if !nodes.insert(trace.node)
            || !reachable.contains(&trace.node)
            || !reachable.contains(&trace.original)
        {
            return Err(p::invalid(
                "native source witness is duplicated or detached from the actual root",
            ));
        }
        let leaf = operations::validate_native_trace(proposal, trace, defs)?;
        let actual = definition(defs, leaf)?;
        let payload = p::text(p::field(p::field(actual, "body")?, "program")?)?;
        let meaning = meanings
            .get(leaf)
            .ok_or_else(|| p::invalid("missing native source finite meaning"))?;
        let body = p::field(meaning, "body")?;
        let proof = proofs
            .get(leaf)
            .ok_or_else(|| p::invalid("missing native source finite equation"))?;
        if p::tag(body)? != "finite"
            || p::field(actual, "interface")? != p::field(meaning, "interface")?
            || p::number(p::field(proof, "implementation")?)? != leaf
            || p::number(p::field(proof, "meaning")?)? != leaf
            || p::tag(p::field(proof, "rule")?)? != "finite"
            || !p::array(p::field(proof, "premises")?)?.is_empty()
        {
            return Err(p::invalid(
                "native source leaf changes its actual required matrix equation",
            ));
        }
        let meaning = p::text(p::field(body, "description")?)?;
        // Pointer identity only deduplicates immutable source replay. Actual
        // leaf bytes and requested matrix are checked at every occurrence.
        if witnesses.insert(Arc::as_ptr(&trace.witness) as usize) {
            trace.witness.validate(
                &proposal.source,
                trace.witness.operation(),
                payload.as_bytes(),
                meaning.as_bytes(),
                &mut budget,
            )?;
        } else {
            trace
                .witness
                .check_leaf_bytes(payload.as_bytes(), meaning.as_bytes(), &mut budget)?;
        }
    }
    Ok(())
}
