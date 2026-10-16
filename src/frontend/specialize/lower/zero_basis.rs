//! Existing native structural/preparation proposals for exact zero-basis maps.
//! This source interval check is not a source-preservation theorem or IR seal.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::preservation::{self as p, SourceEvent};
use super::*;
use crate::interchange::json::{self, Value};

#[cfg(test)]
mod tests;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Kind {
    Structural,
    Prepare,
}

fn zero(ty: &SourceType) -> bool {
    ty.kind() == "unit" || ty.kind() == "bits" && ty.width() == Some(0)
}

/// Exact constructor/type/table classification, never width-only equivalence.
pub(super) fn classify(step: &SourceStep) -> Option<Kind> {
    if step.kind() != "lift_basis" || step.basis_table() != Some(&[0][..]) {
        return None;
    }
    let [input] = step.inputs() else {
        return None;
    };
    let input = input.ty().quantum_basis()?;
    let output = step.output().ty().quantum_basis()?;
    if !zero(input) {
        return None;
    }
    if zero(output) && step.effect() == "unitary" {
        Some(Kind::Structural)
    } else if output.kind() == "bit" && step.effect() == "iso" {
        Some(Kind::Prepare)
    } else {
        None
    }
}

pub(super) fn needs_replay(proposal: &HierarchyProposal) -> bool {
    proposal
        .source
        .definitions()
        .iter()
        .flat_map(|definition| definition.steps())
        .any(|step| step.basis_table().is_some())
}

pub(super) fn operation_uses_table(
    source: &ElaboratedProgram,
    operation: &SourceOperation,
) -> Result<bool> {
    let mut operations = vec![operation];
    let mut definitions = vec![];
    let mut seen = BTreeSet::new();
    let mut visits = 0usize;
    loop {
        while let Some(operation) = operations.pop() {
            visits += 1;
            if visits > 10_000 {
                return Err(limit(
                    "zero-basis source operation traversal exceeds definition capacity",
                ));
            }
            if let Some(id) = operation.definition() {
                definitions.push(id);
            }
            operations.extend(operation.children());
        }
        let Some(id) = definitions.pop() else {
            return Ok(false);
        };
        if !seen.insert(id) {
            continue;
        }
        let definition = source.definitions().get(id).ok_or_else(|| {
            p::invalid("source operation references an absent original definition")
        })?;
        for step in definition.steps() {
            if step.basis_table().is_some() {
                return Ok(true);
            }
            if let Some(id) = step.called_definition() {
                definitions.push(id);
            }
            if let Some(operation) = step.operation() {
                operations.push(operation);
            }
        }
    }
}

fn unpack(ty: &SourceType) -> Result<&'static str> {
    match ty.kind() {
        "unit" => Ok("unpack_unit"),
        "bits" if ty.width() == Some(0) => Ok("unpack_empty_bits"),
        _ => Err(p::invalid(
            "basis interval does not have an exact zero-basis atom",
        )),
    }
}
fn pack(ty: &SourceType) -> Result<&'static str> {
    match unpack(ty)? {
        "unpack_unit" => Ok("pack_unit"),
        _ => Ok("pack_empty_bits"),
    }
}

#[derive(Clone, Debug)]
pub(super) struct Interval {
    definition: usize,
    step: usize,
    node: usize,
    input: Port,
    output: Port,
    pub(super) prepared: Option<Port>,
}

#[derive(Clone, Debug)]
pub(super) struct DefinitionTrace {
    pub(super) definition: usize,
    pub(super) root: usize,
    pub(super) inputs: Vec<Port>,
    pub(super) outputs: Vec<Port>,
    pub(super) events: Vec<SourceEvent>,
}
impl Interval {
    pub(super) fn matches_event(&self, event: &SourceEvent) -> bool {
        let ([Item::Quantum(input)], [Item::Quantum(output)]) =
            (event.inputs.as_slice(), event.outputs.as_slice())
        else {
            return false;
        };
        self.definition == event.definition
            && self.step == event.step
            && Some(self.node) == event.node
            && self.input == *input
            && self.output == *output
            && self.prepared == event.preparation
    }
}

impl Lower<'_> {
    fn remember_zero_basis(
        &mut self,
        origin: (usize, usize),
        node: usize,
        input: &Port,
        output: &Port,
        prepared: Option<&Port>,
    ) -> Result<()> {
        // Each admitted endpoint is one exact Unit/Bits0/Bit atom. Charge the
        // bounded retained metadata before growing the table, under the same
        // proposal byte and definition caps; no selected bound is raised.
        if self.zero_basis.len() >= 10_000 {
            return Err(limit("zero-basis intervals exceed source event capacity"));
        }
        self.graph.charge(128)?;
        self.zero_basis.push(Interval {
            definition: origin.0,
            step: origin.1,
            node,
            input: input.clone(),
            output: output.clone(),
            prepared: prepared.cloned(),
        });
        Ok(())
    }

    pub(super) fn zero_basis_structural(
        &mut self,
        step: &SourceStep,
        before: Vec<Port>,
        origin: (usize, usize),
    ) -> Result<(usize, Vec<Port>)> {
        if classify(step) != Some(Kind::Structural) || before.len() != 1 {
            return Err(Error::new(
                "unsupported",
                step.span(),
                "hierarchy coherent-basis adapter requires an exact Unit/Bits<0> zero map",
            )
            .in_module(step.module()));
        }
        let after = self.output_ports(step.output(), vec![vec![]])?;
        let first =
            self.graph
                .structural(before.clone(), vec![], unpack(&before[0].basis)?, &[])?;
        let last = self
            .graph
            .structural(vec![], after.clone(), pack(&after[0].basis)?, &[])?;
        let node = self.graph.sequence(vec![first, last])?;
        self.remember_zero_basis(origin, node, &before[0], &after[0], None)?;
        Ok((node, after))
    }

    pub(super) fn zero_basis_preparation(
        &mut self,
        step: &SourceStep,
        items: Vec<Item>,
        state: &mut Instrument,
        origin: (usize, usize),
    ) -> Result<(Vec<Item>, usize, Port)> {
        if classify(step) != Some(Kind::Prepare) || !state.measured.is_empty() {
            return Err(Error::new(
                "unsupported",
                step.span(),
                "zero-basis preparation after observation requires a preservation proof",
            )
            .in_module(step.module()));
        }
        let [Item::Quantum(input)] = items.as_slice() else {
            return Err(fail(
                "zero-basis preparation requires its original one quantum owner",
            ));
        };
        if !zero(&input.basis) || !input.axes.is_empty() {
            return Err(fail(
                "zero-basis preparation input differs from its exact source type",
            ));
        }
        if state.next_axis >= 16 {
            return Err(limit("instrument exceeds 16 allocated axes"));
        }
        let fresh = self.fresh_basis(&SourceType::bit(), vec![state.next_axis])?;
        state.next_axis += 1;
        let before = [state.inputs.clone(), state.fresh.clone()].concat();
        let after = [before.clone(), vec![fresh.clone()]].concat();
        state.initializations.push(object(&[
            ("interface", header(&before, &after)),
            ("effect", quote("iso")),
            (
                "body",
                tagged("init0", &[("output", fresh.owner.to_string())]),
            ),
        ]));
        state.fresh.push(fresh.clone());
        let output = self.output_ports(step.output(), vec![fresh.axes.clone()])?;
        let consume =
            self.graph
                .structural(vec![input.clone()], vec![], unpack(&input.basis)?, &[])?;
        let retained = self.graph.identity(vec![fresh.clone()])?;
        let consume = self.graph.tensor(consume, retained)?;
        let rename = self.graph.rename(vec![fresh.clone()], output.clone())?;
        let node = self.graph.sequence(vec![consume, rename])?;
        self.remember_zero_basis(origin, node, input, &output[0], Some(&fresh))?;
        state.pure_steps.push(node);
        Ok((output.into_iter().map(Item::Quantum).collect(), node, fresh))
    }
}

pub(super) fn remap(intervals: &mut [Interval], mapping: &BTreeMap<usize, usize>) -> Result<()> {
    for interval in &mut *intervals {
        interval.node = *mapping
            .get(&interval.node)
            .ok_or_else(|| p::invalid("compaction lost an original zero-basis interval"))?;
    }
    intervals.sort_unstable_by_key(|interval| (interval.definition, interval.step, interval.node));
    Ok(())
}

pub(super) fn remap_traces(
    traces: &mut [DefinitionTrace],
    mapping: &BTreeMap<usize, usize>,
) -> Result<()> {
    for trace in traces {
        trace.root = *mapping
            .get(&trace.root)
            .ok_or_else(|| p::invalid("compaction lost an original pure source root"))?;
        p::remap_events(&mut trace.events, mapping)?;
    }
    Ok(())
}

fn definition(defs: &[Value], id: usize) -> Result<&Value> {
    defs.get(id)
        .ok_or_else(|| p::invalid("zero-basis interval references an absent actual definition"))
}
fn structural(
    defs: &[Value],
    id: usize,
    before: &[Port],
    after: &[Port],
    operation: &str,
) -> Result<()> {
    let node = definition(defs, id)?;
    if p::endpoints(node)? != (before.to_vec(), after.to_vec()) {
        return Err(p::invalid(
            "zero-basis structural interval changes exact owners/types/axes",
        ));
    }
    let body = p::field(node, "body")?;
    if p::tag(body)? != "structural" || p::tag(p::field(body, "operation")?)? != operation {
        return Err(p::invalid(
            "zero-basis interval substitutes its coefficient-+1 structural operation",
        ));
    }
    Ok(())
}
fn identity(defs: &[Value], id: usize, before: &[Port], after: &[Port]) -> Result<()> {
    let node = definition(defs, id)?;
    if p::endpoints(node)? != (before.to_vec(), after.to_vec()) {
        return Err(p::invalid(
            "zero-basis owner rename changes exact endpoints",
        ));
    }
    let body = p::field(node, "body")?;
    if p::tag(body)? != "rewire" {
        return Err(p::invalid(
            "zero-basis identity interval contains an extra phase/action",
        ));
    }
    let permutation = p::field(body, "permutation")?;
    if p::indices(p::field(permutation, "owners")?)? != vec![0]
        || p::indices(p::field(permutation, "axes")?)?
            != (0..axes(before).len()).collect::<Vec<_>>()
        || !p::array(p::field(permutation, "classical")?)?.is_empty()
    {
        return Err(p::invalid(
            "zero-basis interval changes original coordinate order",
        ));
    }
    Ok(())
}

pub(super) fn validate(proposal: &HierarchyProposal) -> Result<()> {
    if !needs_replay(proposal) {
        return if proposal.zero_basis.is_empty() && proposal.pure_traces.is_empty() {
            Ok(())
        } else {
            Err(p::invalid(
                "zero-basis replay contains metadata absent from the original source",
            ))
        };
    }
    if proposal.zero_basis.windows(2).any(|pair| {
        (pair[0].definition, pair[0].step, pair[0].node)
            >= (pair[1].definition, pair[1].step, pair[1].node)
    }) {
        return Err(p::invalid(
            "zero-basis source interval identity table is duplicated or unordered",
        ));
    }
    let graph = json::parse(&proposal.graph).map_err(|e| p::invalid(e.to_string()))?;
    let actual = json::parse(&proposal.payload).map_err(|e| p::invalid(e.to_string()))?;
    let actual_graph = if proposal.instrument {
        p::field(&actual, "circuit")?
    } else {
        &actual
    };
    if actual_graph != &graph {
        return Err(p::invalid(
            "zero-basis intervals differ from the actual immutable payload",
        ));
    }
    let defs = p::array(p::field(&graph, "definitions")?)?;
    for event in &proposal.events {
        let step = proposal
            .source
            .definitions()
            .get(event.definition)
            .and_then(|definition| definition.steps().get(event.step))
            .ok_or_else(|| p::invalid("source event lacks its original source step"))?;
        validate_call_event(proposal, event, step, defs, true)?;
        if step.basis_table().is_some() {
            validate_event(proposal, event)?;
        }
    }
    let root = p::number(p::field(p::field(&graph, "entry")?, "implementation")?)?;
    if !proposal.instrument
        && !proposal
            .pure_traces
            .iter()
            .any(|trace| trace.definition == proposal.source.root() && trace.root == root)
    {
        return Err(p::invalid(
            "actual pure entry differs from its original source-bound root",
        ));
    }
    let reachable = reachable(defs, root)?;
    for trace in &proposal.pure_traces {
        if !reachable.contains(&trace.root) {
            return Err(p::invalid(
                "original pure source root is not linked from the actual entry",
            ));
        }
        p::validate_pure_definition(proposal, trace, defs)?;
    }
    for interval in &proposal.zero_basis {
        if !reachable.contains(&interval.node) {
            return Err(p::invalid(
                "original zero-basis interval is unreachable from the actual entry",
            ));
        }
        let step = proposal
            .source
            .definitions()
            .get(interval.definition)
            .and_then(|definition| definition.steps().get(interval.step))
            .ok_or_else(|| p::invalid("zero-basis interval lacks its original source step"))?;
        let kind = classify(step).ok_or_else(|| {
            p::invalid("zero-basis interval changes its original table/types/effect")
        })?;
        if step.inputs()[0].ty().quantum_basis() != Some(&interval.input.basis)
            || step.output().ty().quantum_basis() != Some(&interval.output.basis)
            || !interval.input.axes.is_empty()
            || interval.input.owner == interval.output.owner
        {
            return Err(p::invalid(
                "zero-basis interval differs from original exact source ports",
            ));
        }
        let node = definition(defs, interval.node)?;
        let body = p::field(node, "body")?;
        if p::tag(body)? != "sequence" {
            return Err(p::invalid(
                "zero-basis interval is not the complete source sequence",
            ));
        }
        let children = p::indices(p::field(body, "children")?)?;
        let [first, last] = children.as_slice() else {
            return Err(p::invalid(
                "zero-basis interval adds or omits a source action",
            ));
        };
        match (kind, &interval.prepared) {
            (Kind::Structural, None) => {
                if p::endpoints(node)?
                    != (vec![interval.input.clone()], vec![interval.output.clone()])
                    || !interval.output.axes.is_empty()
                {
                    return Err(p::invalid("zero-basis map changes exact endpoints"));
                }
                structural(
                    defs,
                    *first,
                    std::slice::from_ref(&interval.input),
                    &[],
                    unpack(&interval.input.basis)?,
                )?;
                structural(
                    defs,
                    *last,
                    &[],
                    std::slice::from_ref(&interval.output),
                    pack(&interval.output.basis)?,
                )?;
            }
            (Kind::Prepare, Some(fresh)) => {
                if fresh.basis != SourceType::bit()
                    || fresh.axes.len() != 1
                    || fresh.axes != interval.output.axes
                    || fresh.owner == interval.input.owner
                    || fresh.owner == interval.output.owner
                    || p::endpoints(node)?
                        != (
                            vec![interval.input.clone(), fresh.clone()],
                            vec![interval.output.clone()],
                        )
                {
                    return Err(p::invalid(
                        "zero-basis preparation changes its fresh Bit/owner/axis",
                    ));
                }
                let tensor = definition(defs, *first)?;
                let body = p::field(tensor, "body")?;
                if p::tag(body)? != "tensor"
                    || p::endpoints(tensor)?
                        != (
                            vec![interval.input.clone(), fresh.clone()],
                            vec![fresh.clone()],
                        )
                {
                    return Err(p::invalid(
                        "zero-basis preparation omits its actual framed owner consumption",
                    ));
                }
                structural(
                    defs,
                    p::number(p::field(body, "left")?)?,
                    std::slice::from_ref(&interval.input),
                    &[],
                    unpack(&interval.input.basis)?,
                )?;
                identity(
                    defs,
                    p::number(p::field(body, "right")?)?,
                    std::slice::from_ref(fresh),
                    std::slice::from_ref(fresh),
                )?;
                identity(
                    defs,
                    *last,
                    std::slice::from_ref(fresh),
                    std::slice::from_ref(&interval.output),
                )?;
            }
            _ => {
                return Err(p::invalid(
                    "zero-basis interval changes whether physical preparation is required",
                ));
            }
        }
    }
    Ok(())
}

fn reachable(defs: &[Value], root: usize) -> Result<BTreeSet<usize>> {
    if defs.len() > 10_000 {
        return Err(p::invalid(
            "zero-basis graph exceeds existing definition capacity",
        ));
    }
    let mut pending = vec![root];
    let mut seen = BTreeSet::new();
    while let Some(id) = pending.pop() {
        if !seen.insert(id) {
            continue;
        }
        let body = p::field(definition(defs, id)?, "body")?;
        let children = match p::tag(body)? {
            "sequence" => p::indices(p::field(body, "children")?)?,
            "tensor" => vec![
                p::number(p::field(body, "left")?)?,
                p::number(p::field(body, "right")?)?,
            ],
            "inverse" | "control" | "repeat" => vec![p::number(p::field(body, "definition")?)?],
            "leaf" | "rewire" | "structural" | "dyadic_phase" => vec![],
            _ => {
                return Err(p::invalid(
                    "zero-basis reachability encountered an unsupported actual graph action",
                ));
            }
        };
        if children.len() > 10_000 || pending.len().saturating_add(children.len()) > 100_000 {
            return Err(p::invalid(
                "zero-basis graph exceeds existing traversal capacity",
            ));
        }
        pending.extend(children);
    }
    Ok(seen)
}

/// Ordinary pure calls retain the exact source child root inside their three
/// ordered rename/body/rename actions; endpoints alone cannot supply that link.
pub(super) fn validate_call_event(
    proposal: &HierarchyProposal,
    event: &SourceEvent,
    step: &SourceStep,
    defs: &[Value],
    enabled: bool,
) -> Result<()> {
    if !enabled {
        return Ok(());
    }
    let Some(child) = step.called_definition() else {
        return Ok(());
    };
    let Some(trace) = proposal
        .pure_traces
        .iter()
        .find(|trace| trace.definition == child)
    else {
        // Effectful transparent calls are replayed by entering the original
        // body, and never arrive here as an atomic pure event.
        return Err(p::invalid(
            "atomic pure source call lacks its original child root",
        ));
    };
    let node = definition(
        defs,
        event
            .node
            .ok_or_else(|| p::invalid("pure call omits its actual interval"))?,
    )?;
    let body = p::field(node, "body")?;
    if p::tag(body)? != "sequence" {
        return Err(p::invalid(
            "pure source call substitutes its original child/root link",
        ));
    }
    let children = p::indices(p::field(body, "children")?)?;
    let [enter, actual, leave] = children.as_slice() else {
        return Err(p::invalid(
            "pure source call changes its complete ordered interval",
        ));
    };
    if *actual != trace.root {
        return Err(p::invalid(
            "pure source call substitutes a different child root",
        ));
    }
    rename(defs, *enter, &quantum(&event.inputs), &trace.inputs)?;
    rename(defs, *leave, &trace.outputs, &quantum(&event.outputs))
}

fn rename(defs: &[Value], id: usize, before: &[Port], after: &[Port]) -> Result<()> {
    let node = definition(defs, id)?;
    let body = p::field(node, "body")?;
    if p::endpoints(node)? != (before.to_vec(), after.to_vec())
        || before.len() != after.len()
        || before
            .iter()
            .zip(after)
            .any(|(a, b)| a.basis != b.basis || a.axes.len() != b.axes.len())
        || p::tag(body)? != "rewire"
    {
        return Err(p::invalid("pure source call changes exact child ports"));
    }
    let permutation = p::field(body, "permutation")?;
    if p::indices(p::field(permutation, "owners")?)? != (0..before.len()).collect::<Vec<_>>()
        || p::indices(p::field(permutation, "axes")?)?
            != (0..axes(before).len()).collect::<Vec<_>>()
        || !p::array(p::field(permutation, "classical")?)?.is_empty()
    {
        return Err(p::invalid(
            "pure source call changes ordered child coordinates",
        ));
    }
    Ok(())
}

pub(super) fn validate_event(proposal: &HierarchyProposal, event: &SourceEvent) -> Result<()> {
    let key = (
        event.definition,
        event.step,
        event
            .node
            .ok_or_else(|| p::invalid("zero-basis source event omits its actual interval"))?,
    );
    let index = proposal.zero_basis.binary_search_by_key(&key, |interval| {
        (interval.definition, interval.step, interval.node)
    });
    if !index.is_ok_and(|index| proposal.zero_basis[index].matches_event(event)) {
        return Err(p::invalid(
            "source event substitutes its original zero-basis interval",
        ));
    }
    Ok(())
}
