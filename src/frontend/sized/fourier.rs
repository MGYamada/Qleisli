// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
//! Bounded, untrusted Fourier factoring from complete actual-body traces.
//! Original nodes and source remain retained. Fresh native Fourier checking is
//! still required; this producer comparison does not issue semantic evidence.
use super::*;
use crate::interchange::json::{self, Value};

// This is a producer optimization budget, not an acceptance capacity. Exceeding
// it leaves the original graph unchanged. Repetition is never expanded.
const TRACE_WORK: usize = 1_000_000;
const TRACE_EVENTS: usize = 4096;

#[derive(Clone, Debug, PartialEq, Eq)]
enum Event {
    H(usize),
    Phase(usize, u64, u32),
    Controlled(usize, usize, u64, u32),
}
impl Event {
    fn map(&self, route: &[usize]) -> Option<Self> {
        Some(match *self {
            Self::H(a) => Self::H(*route.get(a)?),
            Self::Phase(a, j, k) => Self::Phase(*route.get(a)?, j, k),
            Self::Controlled(a, b, j, k) => Self::Controlled(*route.get(a)?, *route.get(b)?, j, k),
        })
    }
    fn canonical(&self) -> Self {
        match *self {
            Self::H(a) => Self::H(a),
            Self::Phase(a, j, k) => {
                let (j, k) = fraction(j, k);
                Self::Phase(a, j, k)
            }
            Self::Controlled(a, b, j, k) => {
                let (j, k) = fraction(j, k);
                Self::Controlled(a.min(b), a.max(b), j, k)
            }
        }
    }
    fn touches(&self, axis: usize) -> bool {
        match *self {
            Self::H(a) | Self::Phase(a, _, _) => a == axis,
            Self::Controlled(a, b, _, _) => a == axis || b == axis,
        }
    }
    // Every non-H event is computational-basis diagonal. H can cross only
    // events on disjoint axes; this deliberately retains all H barriers.
    fn commutes(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::H(axis), event) | (event, Self::H(axis)) => !event.touches(*axis),
            _ => true,
        }
    }
}
#[derive(Clone, Debug)]
struct Trace {
    // Output positions expressed in the original input coordinates.
    route: Vec<usize>,
    events: Vec<Event>,
}
fn nat(value: &Value, field: &str) -> Option<usize> {
    usize::try_from(value.field(field).ok()?.number().ok()?).ok()
}
fn ns(value: &Value) -> Option<Vec<usize>> {
    value
        .array()
        .ok()?
        .iter()
        .map(|v| usize::try_from(v.number().ok()?).ok())
        .collect()
}
fn permutation(xs: &[usize], width: usize) -> bool {
    xs.len() == width && xs.iter().copied().collect::<BTreeSet<_>>() == (0..width).collect()
}
fn spend(work: &mut usize, amount: usize) -> Option<()> {
    *work = work.checked_sub(amount)?;
    Some(())
}
fn h_leaf(node: &Node, body: &Value) -> Option<()> {
    if node.before.len() != 1 || node.after.len() != 1 || !node.before[0].bit || !node.after[0].bit
    {
        return None;
    }
    let bytes = body.field("program").ok()?.text().ok()?.as_bytes();
    // The only supported leaf is a complete single-H finite program.
    if bytes.len() > 4096 {
        return None;
    }
    let imported = interchange::import(bytes, None).ok()?;
    let raw = imported.program.raw();
    let [
        RawOp::Gate {
            gate: SingleGate::H,
            input,
            output,
        },
    ] = raw.operations.as_slice()
    else {
        return None;
    };
    let a = &node.before[0];
    let b = &node.after[0];
    if *input != TokenId(a.owner)
        || *output != TokenId(b.owner)
        || raw.quantum_inputs
            != vec![QuantumPort {
                token: TokenId(a.owner),
                wires: a.axes.iter().copied().map(WireId).collect(),
                shape: BasisShape::BIT,
            }]
        || imported.program.output_ports()
            != [QuantumPort {
                token: TokenId(b.owner),
                wires: b.axes.iter().copied().map(WireId).collect(),
                shape: BasisShape::BIT,
            }]
        || !raw.classical_inputs.is_empty()
        || !raw.classical_outputs.is_empty()
        || raw.quantum_outputs != [TokenId(b.owner)]
        || raw.declared_effect != Effect::Unitary
        || imported.root_interface
            != Some(RootInterface {
                input: BasisType::Bit,
                output: BasisType::Bit,
            })
    {
        return None;
    }
    Some(())
}
fn structural_route(node: &Node, body: &Value) -> Option<Vec<usize>> {
    let op = body.field("operation").ok()?;
    let tag = op.field("tag").ok()?.text().ok()?;
    let (register, pair, take) = match tag {
        "take_bit" => (&node.before, &node.after, true),
        "put_bit" => (&node.after, &node.before, false),
        "pack_empty_bits"
            if node.before.is_empty()
                && node.after.len() == 1
                && !node.after[0].bit
                && node.after[0].axes.is_empty() =>
        {
            return Some(vec![]);
        }
        "unpack_empty_bits"
            if node.after.is_empty()
                && node.before.len() == 1
                && !node.before[0].bit
                && node.before[0].axes.is_empty() =>
        {
            return Some(vec![]);
        }
        _ => return None,
    };
    let width = nat(op, "width")?;
    let position = nat(op, "position")?;
    if register.len() != 1
        || pair.len() != 2
        || register[0].bit
        || !pair[0].bit
        || pair[1].bit
        || register[0].axes.len() != width
        || position >= width
        || pair[0].axes.len() != 1
        || pair[0].axes[0] != register[0].axes[position]
        || pair[1].axes
            != register[0]
                .axes
                .iter()
                .enumerate()
                .filter_map(|(i, w)| (i != position).then_some(*w))
                .collect::<Vec<_>>()
    {
        return None;
    }
    let mut route: Vec<_> = (0..width).collect();
    route.remove(position);
    route.insert(0, position);
    if !take {
        let mut inverse = vec![0; width];
        for (i, &j) in route.iter().enumerate() {
            inverse[j] = i;
        }
        route = inverse;
    }
    Some(route)
}
fn node_trace(
    graph: &Graph,
    index: usize,
    cache: &[Option<Trace>],
    work: &mut usize,
) -> Option<Trace> {
    let node = graph.nodes.get(index)?;
    spend(work, node.definition.len())?;
    let definition = json::parse(node.definition.as_bytes()).ok()?;
    if definition.field("effect").ok()?.text().ok()? != "unitary"
        || definition.field("interface").ok()?
            != &json::parse(header(&node.before, &node.after).as_bytes()).ok()?
        || validate(&node.before).is_err()
        || validate(&node.after).is_err()
    {
        return None;
    }
    let body = definition.field("body").ok()?;
    let width = axes(&node.before).len();
    if axes(&node.after).len() != width {
        return None;
    }
    let identity: Vec<_> = (0..width).collect();
    let child = |i: usize| -> Option<(&Node, &Trace)> {
        Some((graph.nodes.get(i)?, cache.get(i)?.as_ref()?))
    };
    let trace = match body.field("tag").ok()?.text().ok()? {
        "leaf" => {
            h_leaf(node, body)?;
            Trace {
                route: identity,
                events: vec![Event::H(0)],
            }
        }
        "dyadic_phase" => {
            if node.before != node.after
                || node.before.len() != 1
                || !node.before[0].bit
                || nat(body, "target")? != node.before[0].owner as usize
            {
                return None;
            }
            let j = body.field("j").ok()?.number().ok()?;
            let k = u32::try_from(nat(body, "k")?).ok()?;
            if k > 8 {
                return None;
            }
            Trace {
                route: identity,
                events: vec![Event::Phase(0, j, k)],
            }
        }
        "rewire" => {
            let p = body.field("permutation").ok()?;
            let owners = ns(p.field("owners").ok()?)?;
            let route = ns(p.field("axes").ok()?)?;
            if !p.field("classical").ok()?.array().ok()?.is_empty()
                || !permutation(&owners, node.before.len())
                || node.after.len() != owners.len()
                || !permutation(&route, width)
            {
                return None;
            }
            let mut output_start = 0;
            for (out, &input) in node.after.iter().zip(&owners) {
                let input_start: usize = node.before[..input].iter().map(|p| p.axes.len()).sum();
                if out.bit != node.before[input].bit
                    || out.axes.len() != node.before[input].axes.len()
                    || route[output_start..output_start + out.axes.len()]
                        != (input_start..input_start + out.axes.len()).collect::<Vec<_>>()
                {
                    return None;
                }
                output_start += out.axes.len();
            }
            Trace {
                route,
                events: vec![],
            }
        }
        "structural" => Trace {
            route: structural_route(node, body)?,
            events: vec![],
        },
        "sequence" => {
            let children = ns(body.field("children").ok()?)?;
            if children.is_empty() {
                return None;
            }
            let mut route = identity;
            let mut events = vec![];
            let mut current = &node.before;
            for i in children {
                let (d, t) = child(i)?;
                if current != &d.before || t.route.len() != width {
                    return None;
                }
                spend(work, width.checked_add(t.events.len().checked_mul(3)?)?)?;
                if events.len().checked_add(t.events.len())? > TRACE_EVENTS {
                    return None;
                }
                for event in &t.events {
                    events.push(event.map(&route)?);
                }
                route = t
                    .route
                    .iter()
                    .map(|&j| route.get(j).copied())
                    .collect::<Option<Vec<_>>>()?;
                current = &d.after;
            }
            if current != &node.after {
                return None;
            }
            Trace { route, events }
        }
        "tensor" => {
            let (a, at) = child(nat(body, "left")?)?;
            let (b, bt) = child(nat(body, "right")?)?;
            if node.before != [a.before.clone(), b.before.clone()].concat()
                || node.after != [a.after.clone(), b.after.clone()].concat()
            {
                return None;
            }
            let offset = at.route.len();
            spend(
                work,
                width.checked_add(
                    at.events
                        .len()
                        .checked_add(bt.events.len())?
                        .checked_mul(3)?,
                )?,
            )?;
            if at.events.len().checked_add(bt.events.len())? > TRACE_EVENTS {
                return None;
            }
            let mut events = at.events.clone();
            let shift: Vec<_> = (offset..width).collect();
            for e in &bt.events {
                events.push(e.map(&shift)?);
            }
            Trace {
                route: at
                    .route
                    .iter()
                    .copied()
                    .chain(bt.route.iter().map(|j| j + offset))
                    .collect(),
                events,
            }
        }
        "control" => {
            let (d, t) = child(nat(body, "definition")?)?;
            if !body.field("polarity").ok()?.boolean().ok()?
                || node.before != node.after
                || node.before.is_empty()
                || !node.before[0].bit
                || node.before[1..] != d.before
                || d.before != d.after
                || t.route != (0..t.route.len()).collect::<Vec<_>>()
            {
                return None;
            }
            spend(work, t.events.len().checked_mul(3)?)?;
            let events = t
                .events
                .iter()
                .map(|e| match *e {
                    Event::Phase(a, j, k) => Some(Event::Controlled(0, a + 1, j, k)),
                    _ => None,
                })
                .collect::<Option<Vec<_>>>()?;
            Trace {
                route: identity,
                events,
            }
        }
        "repeat" => {
            let (d, t) = child(nat(body, "definition")?)?;
            if node.before != d.before
                || node.after != d.after
                || d.before != d.after
                || t.route != identity
            {
                return None;
            }
            let count = body.field("count").ok()?.number().ok()?;
            spend(work, t.events.len().checked_mul(3)?)?;
            let events = t
                .events
                .iter()
                .map(|e| match *e {
                    Event::Phase(a, j, k) => Some(Event::Phase(a, j.checked_mul(count)?, k)),
                    _ => None,
                })
                .collect::<Option<Vec<_>>>()?;
            Trace {
                route: identity,
                events,
            }
        }
        _ => return None,
    };
    if !permutation(&trace.route, width) {
        return None;
    }
    Some(trace)
}
fn trace(graph: &Graph, root: usize) -> Option<Trace> {
    let mut work = TRACE_WORK;
    let mut cache = Vec::with_capacity(root.checked_add(1)?);
    for index in 0..=root {
        let t = node_trace(graph, index, &cache, &mut work);
        cache.push(t);
        if work == 0 {
            return None;
        }
    }
    cache.pop()?
}
fn fraction(mut j: u64, mut k: u32) -> (u64, u32) {
    while k > 0 && j % 2 == 0 {
        j /= 2;
        k -= 1;
    }
    (j, k)
}
fn staircase(trace: &Trace, width: usize) -> bool {
    if !(1..=8).contains(&width) || trace.route != (0..width).rev().collect::<Vec<_>>() {
        return false;
    }
    let mut expected = vec![];
    for target in (0..width).rev() {
        expected.push(Event::H(target));
        expected.extend(
            (0..target).map(|control| {
                Event::Controlled(control, target, 1, (target - control + 1) as u32)
            }),
        );
    }
    // This bounded trace-monoid comparison performs only adjacent swaps of
    // commuting gates. Removing each expected gate is valid exactly when it
    // can cross every preceding remaining gate. The complete gate count and
    // exact normalized phases must match, so no source operation is omitted.
    if trace.events.len() != expected.len() {
        return false;
    }
    let mut pending: Vec<_> = trace.events.iter().map(Event::canonical).collect();
    for event in expected {
        let Some(index) = pending.iter().position(|candidate| candidate == &event) else {
            return false;
        };
        if pending[..index]
            .iter()
            .any(|before| !event.commutes(before))
        {
            return false;
        }
        pending.remove(index);
    }
    pending.is_empty()
}

struct Builder<'a, 'b> {
    lower: &'a mut Lower<'b>,
    precision: usize,
    registers: Vec<Port>,
    highs: Vec<Port>,
    gradients: BTreeMap<usize, usize>,
}
impl Builder<'_, '_> {
    fn fresh(&mut self, bit: bool, axes: Vec<u32>) -> Result<Port> {
        self.lower.owner = self
            .lower
            .owner
            .checked_add(1)
            .ok_or_else(|| limit("owner identities exhausted"))?;
        Ok(Port {
            owner: self.lower.owner,
            bit,
            axes,
        })
    }
    fn boundary(&mut self, width: usize) -> Result<(Port, Port, usize, usize)> {
        let register = self.registers[width].clone();
        let high = self.highs[width - 1].clone();
        let rest = self.registers[width - 1].clone();
        let ns = [width as u32, (width - 1) as u32];
        let take = self.lower.graph.structural(
            vec![register.clone()],
            vec![high.clone(), rest.clone()],
            "take_bit",
            &ns,
        )?;
        let put = self.lower.graph.structural(
            vec![high.clone(), rest.clone()],
            vec![register],
            "put_bit",
            &ns,
        )?;
        Ok((high, rest, take, put))
    }
    fn gradient(&mut self, width: usize) -> Result<usize> {
        if let Some(&index) = self.gradients.get(&width) {
            return Ok(index);
        }
        let index = if width == 0 {
            self.lower.graph.identity(vec![self.registers[0].clone()])?
        } else {
            let (high, _, take, put) = self.boundary(width)?;
            let phase = self
                .lower
                .phase(&high, &[1, (self.precision - width + 1) as u32])?;
            let rest = self.gradient(width - 1)?;
            let middle = self.lower.graph.tensor(phase, rest)?;
            self.lower.graph.sequence(vec![take, middle, put])?
        };
        self.gradients.insert(width, index);
        Ok(index)
    }
    fn recursive(&mut self, width: usize) -> Result<usize> {
        if width == 0 {
            return self.lower.graph.identity(vec![self.registers[0].clone()]);
        }
        let (high, rest, take, put) = self.boundary(width)?;
        let output = self.fresh(true, high.axes.clone())?;
        let leaf = self.lower.finite_gate(SingleGate::H, &high, &output)?;
        let rename = self.lower.graph.rename(vec![output], vec![high.clone()])?;
        let h = self.lower.graph.sequence(vec![leaf, rename])?;
        let idle = self.lower.graph.identity(vec![rest.clone()])?;
        let first = self.lower.graph.tensor(h, idle)?;
        let mut children = vec![take, first];
        if width > 1 {
            let mut gradient = self.gradient(width - 1)?;
            let count = 1usize << (self.precision - width);
            if count > 1 {
                gradient = self.lower.graph.add(
                    vec![rest.clone()],
                    vec![rest.clone()],
                    tagged(
                        "repeat",
                        &[
                            ("definition", gradient.to_string()),
                            ("count", count.to_string()),
                        ],
                    ),
                    tagged(
                        "power",
                        &[
                            ("child", gradient.to_string()),
                            ("count", count.to_string()),
                        ],
                    ),
                    "repeat",
                    vec![gradient],
                )?;
            }
            children.push(self.lower.control(vec![high.clone(), rest], gradient)?);
        }
        let idle = self.lower.graph.identity(vec![high])?;
        let recursive = self.recursive(width - 1)?;
        children.push(self.lower.graph.tensor(idle, recursive)?);
        children.push(put);
        self.lower.graph.sequence(children)
    }
    fn reversal(&mut self, register: Port) -> Result<usize> {
        self.reverse_axes(register, true)
    }
    // Keep the reversed coordinate labels in each recursive tail's actual
    // structural output. Only the outer boundary restores its original frame;
    // no intermediate owner/axis renaming is needed to perform the reversal.
    fn reverse_axes(&mut self, register: Port, close: bool) -> Result<usize> {
        let width = register.axes.len();
        if width <= 1 {
            return self.lower.graph.identity(vec![register]);
        }
        let bit = self.fresh(true, register.axes[..1].to_vec())?;
        let rest = self.fresh(false, register.axes[1..].to_vec())?;
        let take = self.lower.graph.structural(
            vec![register.clone()],
            vec![bit.clone(), rest.clone()],
            "take_bit",
            &[width as u32, 0],
        )?;
        let mut children = vec![take];
        // Reversing a one-axis tail changes no coordinate. Retain its owner
        // through the adjacent take/put boundaries without proposing a tensor
        // of two identity rewires for the native checker to prove again.
        let reversed_rest = if width > 2 {
            let idle = self.lower.graph.identity(vec![bit.clone()])?;
            let reverse = self.reverse_axes(rest.clone(), false)?;
            let after = self.lower.graph.nodes[reverse].after[0].clone();
            children.push(self.lower.graph.tensor(idle, reverse)?);
            after
        } else {
            rest
        };
        let result = Port {
            axes: reversed_rest
                .axes
                .iter()
                .chain(&bit.axes)
                .copied()
                .collect(),
            ..register.clone()
        };
        let put = self.lower.graph.structural(
            vec![bit, reversed_rest],
            vec![result.clone()],
            "put_bit",
            &[width as u32, (width - 1) as u32],
        )?;
        children.push(put);
        if close {
            children.push(self.lower.graph.rename(vec![result], vec![register])?);
        }
        self.lower.graph.sequence(children)
    }
}
impl Lower<'_> {
    pub(super) fn factor_fourier(&mut self, original: usize) -> Result<usize> {
        let node = &self.graph.nodes[original];
        if node.before.len() != 1
            || node.after.len() != 1
            || node.before[0].bit
            || node.after[0].bit
            || node.before[0].axes.len() != node.after[0].axes.len()
        {
            return Ok(original);
        }
        let outer = node.before[0].clone();
        let output = node.after[0].clone();
        let width = outer.axes.len();
        let Some(original_trace) = trace(&self.graph, original) else {
            return Ok(original);
        };
        if !staircase(&original_trace, width) {
            return Ok(original);
        }
        let saved = (
            self.graph.nodes.len(),
            self.graph.encodings.len(),
            self.graph.bytes,
            self.owner,
        );
        let attempt = (|| -> Result<usize> {
            let mut b = Builder {
                lower: &mut *self,
                precision: width,
                registers: vec![],
                highs: vec![],
                gradients: BTreeMap::new(),
            };
            for n in 0..=width {
                let p = b.fresh(false, (0..n as u32).collect())?;
                b.registers.push(p);
                if n > 0 {
                    let p = b.fresh(true, vec![(n - 1) as u32])?;
                    b.highs.push(p);
                }
            }
            let inner = b.registers[width].clone();
            let enter = b
                .lower
                .graph
                .rename(vec![outer.clone()], vec![inner.clone()])?;
            let body = b.recursive(width)?;
            let leave = b.lower.graph.rename(vec![inner], vec![outer.clone()])?;
            let reverse = b.reversal(outer.clone())?;
            let mut children = vec![enter, body, leave, reverse];
            if outer != output {
                children.push(b.lower.graph.rename(vec![outer], vec![output])?);
            }
            let candidate = b.lower.graph.sequence(children)?;
            let candidate_trace = trace(&b.lower.graph, candidate)
                .ok_or_else(|| limit("Fourier candidate trace exceeded its bounded profile"))?;
            // Both complete traces normalize to exactly the same positive-sign
            // staircase using only diagonal/disjoint-support commutations.
            if !staircase(&candidate_trace, width)
                || b.lower.graph.nodes[candidate].before != b.lower.graph.nodes[original].before
                || b.lower.graph.nodes[candidate].after != b.lower.graph.nodes[original].after
            {
                return Err(fail(
                    "Fourier candidate differs from the complete source trace",
                ));
            }
            Ok(candidate)
        })();
        match attempt {
            Ok(candidate) => Ok(candidate),
            Err(error) => {
                // Optional factoring must not reduce the existing producer
                // capacity. No partially appended candidate survives failure.
                self.graph.nodes.truncate(saved.0);
                self.graph.encodings.truncate(saved.1);
                self.graph.cache.retain(|_, index| *index < saved.0);
                self.graph
                    .encoding_cache
                    .retain(|_, index| *index < saved.1);
                self.graph.bytes = saved.2;
                self.owner = saved.3;
                if error.code() == "limit" {
                    Ok(original)
                } else {
                    Err(error)
                }
            }
        }
    }
}

// Compact only when serializing. The producer graph remains available for the
// source trace and translation record. The checker requires every emitted row
// to be reachable; unused source/candidate rows must not be smuggled into it.
fn remap_body(body: &Value, indices: &BTreeMap<usize, usize>) -> Option<Value> {
    let Value::Object(mut fields) = body.clone() else {
        return None;
    };
    let tag = body.field("tag").ok()?.text().ok()?;
    let keys: &[&str] = match tag {
        "tensor" => &["left", "right"],
        "inverse" | "control" => {
            if fields.contains_key("definition") {
                &["definition"]
            } else {
                &["child"]
            }
        }
        "repeat" => &["definition"],
        "power" => &["child"],
        "leaf" | "finite" | "rewire" | "structural" | "dyadic_phase" | "phase" => &[],
        "sequence" => {
            let children = ns(body.field("children").ok()?)?;
            fields.insert(
                "children".into(),
                Value::Array(
                    children
                        .iter()
                        .map(|i| {
                            indices
                                .get(i)
                                .and_then(|&j| u64::try_from(j).ok())
                                .map(Value::Number)
                        })
                        .collect::<Option<Vec<_>>>()?,
                ),
            );
            &[]
        }
        _ => return None,
    };
    for key in keys {
        let old = nat(body, key)?;
        fields.insert(
            (*key).into(),
            Value::Number(u64::try_from(*indices.get(&old)?).ok()?),
        );
    }
    Some(Value::Object(fields))
}
fn encoded(value: &Value) -> Result<String> {
    String::from_utf8(json::encode(value).map_err(|e| fail(e.to_string()))?)
        .map_err(|_| fail("graph JSON is not UTF-8"))
}
impl Graph {
    /// A complete reachable export with consistent definition/meaning/proof
    /// indices. Input/output encodings are reconstructed as exact identities.
    pub(super) fn compact_export(
        &self,
        root: usize,
    ) -> Result<(Graph, usize, BTreeMap<usize, usize>)> {
        let mut live = BTreeSet::new();
        let mut pending = vec![root];
        while let Some(index) = pending.pop() {
            if !live.insert(index) {
                continue;
            }
            let node = self
                .nodes
                .get(index)
                .ok_or_else(|| fail("missing compact graph node"))?;
            let proof = json::parse(node.proof.as_bytes()).map_err(|e| fail(e.to_string()))?;
            let children = ns(proof.field("premises").map_err(|e| fail(e.to_string()))?)
                .ok_or_else(|| fail("invalid compact graph premises"))?;
            if children.iter().any(|&child| child >= index) {
                return Err(fail("compact graph is not topological"));
            }
            pending.extend(children);
        }
        let mut compact = Graph::new();
        let mut indices = BTreeMap::new();
        for index in live {
            let node = &self.nodes[index];
            let definition =
                json::parse(node.definition.as_bytes()).map_err(|e| fail(e.to_string()))?;
            let meaning = json::parse(node.meaning.as_bytes()).map_err(|e| fail(e.to_string()))?;
            let proof = json::parse(node.proof.as_bytes()).map_err(|e| fail(e.to_string()))?;
            let remap = |v: &Value| -> Result<String> {
                let body = v.field("body").map_err(|e| fail(e.to_string()))?;
                encoded(
                    &remap_body(body, &indices)
                        .ok_or_else(|| fail("unsupported compact graph body"))?,
                )
            };
            let premises = ns(proof.field("premises").map_err(|e| fail(e.to_string()))?)
                .ok_or_else(|| fail("invalid compact graph premises"))?
                .iter()
                .map(|i| {
                    indices
                        .get(i)
                        .copied()
                        .ok_or_else(|| fail("missing compact premise"))
                })
                .collect::<Result<Vec<_>>>()?;
            let rule = proof
                .field("rule")
                .and_then(|v| v.field("tag"))
                .and_then(Value::text)
                .map_err(|e| fail(e.to_string()))?;
            let new = compact.add(
                node.before.clone(),
                node.after.clone(),
                remap(&definition)?,
                remap(&meaning)?,
                rule,
                premises,
            )?;
            indices.insert(index, new);
        }
        let entry = indices
            .get(&root)
            .copied()
            .ok_or_else(|| fail("missing compact entry"))?;
        Ok((compact, entry, indices))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::sized::ParsedProgram;
    const SOURCE: &str = include_str!("../../../corpus/sized/qualtran_qft/fourier.qli");

    fn source(text: &str, width: u32) -> ElaboratedProgram {
        ParsedProgram::parse(BTreeMap::from([("fourier".into(), text.into())]))
            .unwrap()
            .instantiate(
                "fourier::fourier",
                BTreeMap::from([("n".into(), width)]),
                BTreeMap::new(),
            )
            .unwrap()
            .elaborate()
            .unwrap()
    }
    fn factor(source: &ElaboratedProgram) -> (Lower<'_>, usize, usize) {
        let mut lower = Lower {
            source,
            graph: Graph::new(),
            owner: 100,
            pure: BTreeMap::new(),
            gate_cache: BTreeMap::new(),
            finite_gates: BTreeMap::new(),
            inline_visits: 0,
        };
        let input = Port {
            owner: 1,
            bit: true,
            axes: vec![0],
        };
        let output = Port {
            owner: 2,
            ..input.clone()
        };
        let h = lower.finite_gate(SingleGate::H, &input, &output).unwrap();
        lower.finite_gates.insert(0, h);
        let child = lower.pure_definition(source.root()).unwrap();
        let before = lower.graph.nodes[child].before.clone();
        let after = lower.graph.nodes[child].after.clone();
        let enter = lower.graph.identity(before.clone()).unwrap();
        let restore = lower.graph.rename(after, before).unwrap();
        let original = lower.graph.sequence(vec![enter, child, restore]).unwrap();
        let candidate = lower.factor_fourier(original).unwrap();
        (lower, original, candidate)
    }
    #[test]
    fn direct_finite_gates_bind_actual_ports_and_reuse_identical_headers() {
        let source = source(SOURCE, 1);
        let (mut lower, _, _) = factor(&source);
        let input = Port {
            owner: 900,
            bit: true,
            axes: vec![7],
        };
        let output = Port {
            owner: 901,
            ..input.clone()
        };
        for gate in [SingleGate::H, SingleGate::X] {
            let node = lower.finite_gate(gate, &input, &output).unwrap();
            assert_eq!(lower.finite_gate(gate, &input, &output).unwrap(), node);
            assert_eq!(lower.graph.nodes[node].before, std::slice::from_ref(&input));
            assert_eq!(lower.graph.nodes[node].after, std::slice::from_ref(&output));
            let definition = json::parse(lower.graph.nodes[node].definition.as_bytes()).unwrap();
            let program = definition
                .field("body")
                .unwrap()
                .field("program")
                .unwrap()
                .text()
                .unwrap();
            let imported = interchange::import(program.as_bytes(), None).unwrap();
            assert_eq!(
                imported.program.raw().operations,
                [RawOp::Gate {
                    gate,
                    input: TokenId(input.owner),
                    output: TokenId(output.owner),
                }]
            );
            let different = Port {
                owner: 902,
                ..output.clone()
            };
            assert_ne!(lower.finite_gate(gate, &input, &different).unwrap(), node);
        }
    }
    #[test]
    fn actual_source_fourier_factoring_preserves_complete_phase_trace() {
        for width in 1..=3 {
            let source = source(SOURCE, width);
            let (mut lower, original, candidate) = factor(&source);
            assert_ne!(original, candidate);
            assert!(staircase(
                &trace(&lower.graph, original).unwrap(),
                width as usize
            ));
            assert!(staircase(
                &trace(&lower.graph, candidate).unwrap(),
                width as usize
            ));
            let (compact, root, map) = lower.graph.compact_export(candidate).unwrap();
            assert!(!map.contains_key(&original));
            assert!(compact.nodes.len() < lower.graph.nodes.len());
            assert!(staircase(&trace(&compact, root).unwrap(), width as usize));
            if let Some(directory) = std::env::var_os("QLEISLI_FOURIER_PROPOSALS") {
                let path = std::path::PathBuf::from(directory);
                std::fs::create_dir_all(&path).unwrap();
                std::fs::write(
                    path.join(format!("candidate-{width}.json")),
                    compact.artifact(root),
                )
                .unwrap();
                let (old, root, _) = lower.graph.compact_export(original).unwrap();
                std::fs::write(
                    path.join(format!("original-{width}.json")),
                    old.artifact(root),
                )
                .unwrap();
            }
            let saved = (
                lower.graph.nodes.len(),
                lower.graph.encodings.len(),
                lower.owner,
            );
            lower.graph.bytes = (16 << 20) - 1;
            assert_eq!(lower.factor_fourier(original).unwrap(), original);
            assert_eq!(
                (
                    lower.graph.nodes.len(),
                    lower.graph.encodings.len(),
                    lower.owner
                ),
                saved
            );
            assert_eq!(lower.graph.bytes, (16 << 20) - 1);
        }
        let equivalent = SOURCE.replace(
            "controlled_phase[1,n-stage-k]",
            "controlled_phase[2,n-stage-k+1]",
        );
        let source = source(&equivalent, 3);
        let (_, original, candidate) = factor(&source);
        assert_ne!(
            original, candidate,
            "exact equivalent dyadic representations must factor"
        );
    }
    #[test]
    fn actual_source_fourier_factoring_commuting_variant_preserves_complete_trace() {
        let delayed = include_str!("../../../tests/fixtures/sized_clients/delayed_fourier.qli");
        for width in 1..=3 {
            let source = source(delayed, width);
            let (lower, original, candidate) = factor(&source);
            assert_ne!(original, candidate);
            assert!(staircase(
                &trace(&lower.graph, original).unwrap(),
                width as usize
            ));
            assert!(staircase(
                &trace(&lower.graph, candidate).unwrap(),
                width as usize
            ));
            if let Some(directory) = std::env::var_os("QLEISLI_FOURIER_PROPOSALS") {
                let path = std::path::PathBuf::from(directory);
                std::fs::create_dir_all(&path).unwrap();
                for (name, entry) in [
                    ("delayed-original", original),
                    ("delayed-candidate", candidate),
                ] {
                    let (compact, entry, _) = lower.graph.compact_export(entry).unwrap();
                    std::fs::write(
                        path.join(format!("{name}-{width}.json")),
                        compact.artifact(entry),
                    )
                    .unwrap();
                }
            }
        }
    }
    #[test]
    fn actual_source_fourier_factoring_rejects_phase_order_and_reversal_changes() {
        for changed in [
            SOURCE.replace(
                "controlled_phase[1,n-stage-k]",
                "controlled_phase[3,n-stage-k]",
            ),
            SOURCE.replace("if static k+k+2 <= n", "if static n+1 <= n"),
            SOURCE.replace(
                "let target = h(target);",
                "let target = h(target); let target = h(target);",
            ),
        ] {
            let source = source(&changed, 3);
            let (_, original, candidate) = factor(&source);
            assert_eq!(
                original, candidate,
                "changed quantum meaning must remain unfactored"
            );
        }
        let mut t = Trace {
            route: vec![1, 0],
            events: vec![Event::H(1), Event::Controlled(0, 1, 1, 2), Event::H(0)],
        };
        assert!(staircase(&t, 2));
        t.events.swap(0, 1);
        assert!(!staircase(&t, 2));
        t.events.swap(0, 1);
        t.events.insert(2, Event::Phase(1, 1, 1));
        assert!(!staircase(&t, 2));
    }
    #[test]
    fn fourier_trace_matching_preserves_h_barriers_and_commutes_diagonal_gates() {
        let original = Trace {
            route: vec![2, 1, 0],
            events: vec![
                Event::H(2),
                Event::Controlled(0, 2, 1, 3),
                Event::Controlled(1, 2, 1, 2),
                Event::H(1),
                Event::Controlled(0, 1, 1, 2),
                Event::H(0),
            ],
        };
        assert!(staircase(&original, 3));
        let mut delayed = original.clone();
        let gate = delayed.events.remove(1);
        delayed.events.insert(4, gate);
        assert!(staircase(&delayed, 3), "C(0,2) may cross H(1)");
        delayed.events.swap(3, 4);
        assert!(staircase(&delayed, 3), "overlapping diagonal gates commute");
        let gate = delayed.events.remove(3);
        delayed.events.push(gate);
        assert!(!staircase(&delayed, 3), "C(0,2) must not cross H(0)");
        let mut altered = original.clone();
        altered.events.swap(0, 1);
        assert!(!staircase(&altered, 3), "C(0,2) must not cross H(2)");

        // Exercise many linear extensions without admitting a changed gate.
        let mut state = 0x37_921a_u64;
        let mut equivalent = original;
        for _ in 0..512 {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
            let index = (state as usize) % (equivalent.events.len() - 1);
            if equivalent.events[index].commutes(&equivalent.events[index + 1]) {
                equivalent.events.swap(index, index + 1);
            }
            assert!(staircase(&equivalent, 3));
        }
    }
}
