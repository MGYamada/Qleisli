//! Exact source/transport links for existing pure operation constructors.
//! This does not decide semantic equality or issue an accepted handle. The
//! immutable payload still requires the unchanged independent Lean checker.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;

mod constructed;
mod native_source;

/// Bounded matcher for original source constructors and their concrete graph links.
struct Match<'a> {
    proposal: &'a HierarchyProposal,
    defs: &'a [Value],
    visits: usize,
    cells: usize,
}
impl Match<'_> {
    /// Resolve an actual graph node while charging each traversal visit.
    fn node(&mut self, id: usize) -> Result<&Value> {
        self.charge_visits(1)?;
        definition(self.defs, id)
    }
    /// Charge source-metadata scans as well as actual graph traversal.
    fn charge_visits(&mut self, count: usize) -> Result<()> {
        self.visits = self.visits.saturating_add(count);
        if self.visits > 10_000 {
            return Err(p::invalid(
                "zero-basis operation links exceed graph visit capacity",
            ));
        }
        Ok(())
    }
    /// Charge immutable interface cells before decoding exact ordered ports.
    fn ports(&mut self, id: usize) -> Result<(Vec<Port>, Vec<Port>)> {
        let node = definition(self.defs, id)?;
        let header = p::field(node, "interface")?;
        let mut cells = 1usize;
        for side in ["inputs", "outputs"] {
            let side = p::field(header, side)?;
            let ports = p::array(p::field(side, "quantum")?)?;
            for port in ports {
                cells = cells
                    .saturating_add(1)
                    .saturating_add(p::array(p::field(port, "basis")?)?.len())
                    .saturating_add(p::array(p::field(port, "axes")?)?.len());
            }
        }
        self.cells = self.cells.saturating_add(cells);
        if self.cells > 100_000 {
            return Err(p::invalid(
                "zero-basis operation links exceed retained cell capacity",
            ));
        }
        p::endpoints(self.node(id)?)
    }
    /// Require the expected short sequence and exact chaining of every child.
    fn sequence(&mut self, id: usize, count: usize) -> Result<Vec<usize>> {
        let body = p::field(self.node(id)?, "body")?;
        if p::tag(body)? != "sequence" {
            return Err(p::invalid(
                "zero-basis operation substitutes its ordered sequence",
            ));
        }
        let children = p::field(body, "children")?;
        if p::array(children)?.len() != count {
            return Err(p::invalid("zero-basis operation adds or omits an action"));
        }
        let children = p::indices(children)?;
        let (before, after) = self.ports(id)?;
        let mut current = before;
        for &child in &children {
            let (first, last) = self.ports(child)?;
            if first != current {
                return Err(p::invalid(
                    "zero-basis operation sequence changes its exact ports",
                ));
            }
            current = last;
        }
        if current != after {
            return Err(p::invalid(
                "zero-basis operation sequence changes its return ports",
            ));
        }
        Ok(children)
    }
    /// Match a pure owner rename without changing type trees or coordinate order.
    fn rename(&mut self, id: usize, before: &[Port], after: &[Port]) -> Result<()> {
        if self.ports(id)? != (before.to_vec(), after.to_vec())
            || before.len() != after.len()
            || before
                .iter()
                .zip(after)
                .any(|(a, b)| a.basis != b.basis || a.axes.len() != b.axes.len())
        {
            return Err(p::invalid(
                "zero-basis operation changes exact source owner ports",
            ));
        }
        let body = p::field(self.node(id)?, "body")?;
        if p::tag(body)? != "rewire" {
            return Err(p::invalid(
                "zero-basis operation replaces a rename with an action",
            ));
        }
        let permutation = p::field(body, "permutation")?;
        let owners = p::array(p::field(permutation, "owners")?)?;
        let wires = p::array(p::field(permutation, "axes")?)?;
        let width: usize = before.iter().map(|port| port.axes.len()).sum();
        if owners.len() != before.len()
            || wires.len() != width
            || !p::array(p::field(permutation, "classical")?)?.is_empty()
        {
            return Err(p::invalid(
                "zero-basis operation changes ordered source coordinates",
            ));
        }
        // Inspect borrowed entries only after bounding both arrays by exact ports.
        for indices in [owners, wires] {
            for (expected, actual) in indices.iter().enumerate() {
                if p::number(actual)? != expected {
                    return Err(p::invalid(
                        "zero-basis operation changes ordered source coordinates",
                    ));
                }
            }
        }
        Ok(())
    }
    /// Bind an actual inverse node to its child and exchanged exact interfaces.
    fn inverse(&mut self, id: usize) -> Result<usize> {
        let body = p::field(self.node(id)?, "body")?;
        if p::tag(body)? != "inverse" {
            return Err(p::invalid(
                "zero-basis adjoint substitutes its original inverse",
            ));
        }
        let child = p::number(p::field(body, "definition")?)?;
        let (before, after) = self.ports(child)?;
        if self.ports(id)? != (after, before) {
            return Err(p::invalid(
                "zero-basis adjoint changes the exchanged source ports",
            ));
        }
        Ok(child)
    }
    /// Precharge the complete retained operation key before expanding its tree.
    fn operation_key(
        &mut self,
        operation: &SourceOperation,
    ) -> Result<crate::frontend::specialize::elaborate::OperationKey> {
        self.cells = self.cells.saturating_add(operation.expanded_key_cells());
        if self.cells > 100_000 {
            return Err(p::invalid(
                "zero-basis operation key exceeds retained cell capacity",
            ));
        }
        Ok(operation.key())
    }
    /// Match a named original root or each retained repeat constructor and count.
    fn operation(&mut self, operation: &SourceOperation, id: usize, depth: usize) -> Result<()> {
        if depth > 64 {
            return Err(p::invalid(
                "zero-basis operation links exceed source depth capacity",
            ));
        }
        let key = self.operation_key(operation)?;
        self.charge_visits(self.proposal.native_sources.len().saturating_mul(2))?;
        if let Some(index) = self
            .proposal
            .native_sources
            .iter()
            .position(|trace| trace.node == id && trace.witness.key() == &key)
        {
            let trace = self.proposal.native_sources[index].clone();
            self.native_source(&trace, operation, depth)?;
            return Ok(());
        }
        if self
            .proposal
            .native_sources
            .iter()
            .any(|trace| trace.witness.key() == &key)
        {
            return Err(p::invalid(
                "operation substitutes an original checked native source binding",
            ));
        }
        self.original_operation(operation, id, depth)
    }
    /// Match the original source root behind a retained native override.
    fn original_operation(
        &mut self,
        operation: &SourceOperation,
        id: usize,
        depth: usize,
    ) -> Result<()> {
        if depth > 64 {
            return Err(p::invalid(
                "zero-basis operation links exceed source depth capacity",
            ));
        }
        if operation.constructed().is_some() {
            return self.constructed_operation(operation, id, depth);
        }
        if let Some(original) = operation.definition() {
            self.charge_visits(self.proposal.pure_traces.len())?;
            let trace = self
                .proposal
                .pure_traces
                .iter()
                .position(|trace| trace.definition == original)
                .ok_or_else(|| p::invalid("zero-basis provider lacks its original pure root"))?;
            let root = self.proposal.pure_traces[trace].root;
            // Charge/parse actual immutable ports before retaining a copy.
            let (input, output) = self.ports(root)?;
            if input != self.proposal.pure_traces[trace].inputs
                || output != self.proposal.pure_traces[trace].outputs
            {
                return Err(p::invalid(
                    "zero-basis provider changes its original root boundary",
                ));
            }
            if input
                .iter()
                .map(|port| &port.basis)
                .eq(output.iter().map(|port| &port.basis))
            {
                let children = self.sequence(id, 3)?;
                if children[1] != root {
                    return Err(p::invalid(
                        "zero-basis provider substitutes another original root",
                    ));
                }
                self.rename(children[0], &input, &input)?;
                self.rename(children[2], &output, &input)?;
                if self.ports(root)? != (input, output) {
                    return Err(p::invalid(
                        "zero-basis provider changes its original root boundary",
                    ));
                }
            } else if id != root || self.ports(id)? != (input, output) {
                return Err(p::invalid(
                    "zero-basis arrow substitutes its original root or type tree",
                ));
            }
            return Ok(());
        }
        let child = operation
            .child()
            .ok_or_else(|| p::invalid("missing original repeat child"))?;
        let count = operation
            .repeat_count()
            .ok_or_else(|| p::invalid("missing original repeat count"))?;
        let body = p::field(self.node(id)?, "body")?;
        if p::tag(body)? != "repeat" || p::number(p::field(body, "count")?)? != count as usize {
            return Err(p::invalid(
                "zero-basis repeat changes its original count or constructor",
            ));
        }
        let child_id = p::number(p::field(body, "definition")?)?;
        let ports = self.ports(child_id)?;
        if ports.0 != ports.1 || self.ports(id)? != ports {
            return Err(p::invalid(
                "zero-basis repeat changes its exact endomorphism ports",
            ));
        }
        // Zero repetitions never bypass the original child/root obligation.
        self.operation(child, child_id, depth + 1)
    }
    /// Match argument binding and return axes around an original operation.
    fn bound(
        &mut self,
        operation: &SourceOperation,
        id: usize,
        before: &[Port],
        after: &[Port],
        adjoint: bool,
        depth: usize,
    ) -> Result<()> {
        let child = self.bound_links(id, before, after, adjoint)?;
        self.operation(operation, child, depth)
    }
    /// Match exact argument/result bindings without selecting a child authority route.
    fn bound_links(
        &mut self,
        id: usize,
        before: &[Port],
        after: &[Port],
        adjoint: bool,
    ) -> Result<usize> {
        let children = self.sequence(id, 3)?;
        let (first, last) = self.ports(children[1])?;
        self.rename(children[0], before, &first)?;
        self.rename(children[2], &last, after)?;
        let bindings: BTreeMap<_, _> = axes(&first).into_iter().zip(axes(before)).collect();
        for (original, actual) in last.iter().zip(after) {
            let expected = original
                .axes
                .iter()
                .map(|axis| {
                    bindings.get(axis).copied().ok_or_else(|| {
                        p::invalid("zero-basis operation introduces an unbound source axis")
                    })
                })
                .collect::<Result<Vec<_>>>()?;
            if actual.axes != expected {
                return Err(p::invalid(
                    "zero-basis operation changes its source output axis mapping",
                ));
            }
        }
        let child = if adjoint {
            self.inverse(children[1])?
        } else {
            children[1]
        };
        Ok(child)
    }
}

/// Bind the source apply/adjoint/control event to its complete actual interval.
pub(super) fn validate(
    proposal: &HierarchyProposal,
    event: &SourceEvent,
    step: &SourceStep,
    operation: &SourceOperation,
    defs: &[Value],
) -> Result<()> {
    let mut matcher = Match {
        proposal,
        defs,
        visits: 0,
        cells: 0,
    };
    let id = event
        .node
        .ok_or_else(|| p::invalid("zero-basis operation omits its actual interval"))?;
    let before = quantum(&event.inputs);
    let after = quantum(&event.outputs);
    if matcher.ports(id)? != (before.clone(), after.clone()) {
        return Err(p::invalid(
            "zero-basis operation changes its complete source event boundary",
        ));
    }
    match step.kind() {
        "apply" | "adjoint" => {
            matcher.bound(operation, id, &before, &after, step.kind() == "adjoint", 0)
        }
        "controlled" => {
            let children = matcher.sequence(id, 2)?;
            let body = p::field(matcher.node(children[0])?, "body")?;
            if p::tag(body)? != "control" || p::field(body, "polarity")? != &Value::Bool(true) {
                return Err(p::invalid(
                    "zero-basis control changes its original polarity or constructor",
                ));
            }
            let child = p::number(p::field(body, "definition")?)?;
            if before
                .first()
                .is_none_or(|port| port.basis != SourceType::bit() || port.axes.len() != 1)
                || matcher.ports(children[0])? != (before.clone(), before.clone())
            {
                return Err(p::invalid(
                    "zero-basis control changes its original control owner",
                ));
            }
            matcher.bound(operation, child, &before[1..], &before[1..], false, 0)?;
            matcher.rename(children[1], &before, &after)?;
            if before.iter().zip(&after).any(|(a, b)| a.axes != b.axes) {
                return Err(p::invalid(
                    "zero-basis control changes the original returned axes",
                ));
            }
            Ok(())
        }
        _ => Err(p::invalid(
            "zero-basis operation event has an unsupported original step",
        )),
    }
}

/// Validate one retained actual override shape and return its exact leaf index.
pub(super) fn validate_native_trace(
    proposal: &HierarchyProposal,
    trace: &NativeSourceTrace,
    defs: &[Value],
) -> Result<usize> {
    Match {
        proposal,
        defs,
        visits: 0,
        cells: 0,
    }
    .native_source(trace, trace.witness.operation(), 0)
}
