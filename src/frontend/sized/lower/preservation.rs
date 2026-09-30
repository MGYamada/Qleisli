//! Independent structural validation of stable fresh-initialization extraction.
//! This validates one preparation pass, not source-to-unitary translation.
use super::{HierarchyProposal, Instrument, Item, Port};
use crate::frontend::sized::{Error, Result, SourceStep, SourceValue, Span};
use crate::interchange::json::{self, Value};
use std::collections::{BTreeMap, BTreeSet};

pub(super) fn invalid(message: impl Into<String>) -> Error {
    Error::new("preservation", Span::default(), message)
}
fn transport(e: crate::interchange::Error) -> Error {
    invalid(e.to_string())
}
fn field<'a>(v: &'a Value, name: &str) -> Result<&'a Value> {
    v.field(name).map_err(transport)
}
fn array(v: &Value) -> Result<&[Value]> {
    v.array().map_err(transport)
}
fn number(v: &Value) -> Result<usize> {
    usize::try_from(v.number().map_err(transport)?)
        .map_err(|_| invalid("transport integer overflow"))
}
fn text(v: &Value) -> Result<&str> {
    v.text().map_err(transport)
}
fn tag(v: &Value) -> Result<&str> {
    text(field(v, "tag")?)
}
fn indices(v: &Value) -> Result<Vec<usize>> {
    array(v)?.iter().map(number).collect()
}
fn port(v: &Value) -> Result<Port> {
    let basis = array(field(v, "basis")?)?;
    if basis.len() != 1 {
        return Err(invalid(
            "preparation frame must retain complete Bit/Bits owners",
        ));
    }
    let bit = tag(&basis[0])? == "bit";
    let width = if bit {
        1
    } else if tag(&basis[0])? == "bits" {
        number(field(&basis[0], "width")?)?
    } else {
        return Err(invalid("unsupported frame basis"));
    };
    let axes = indices(field(v, "axes")?)?
        .into_iter()
        .map(|x| u32::try_from(x).map_err(|_| invalid("axis overflow")))
        .collect::<Result<Vec<_>>>()?;
    if width != axes.len() {
        return Err(invalid("frame basis and axes disagree"));
    }
    Ok(Port {
        owner: u32::try_from(number(field(v, "owner")?)?).map_err(|_| invalid("owner overflow"))?,
        bit,
        axes,
    })
}
fn side(v: &Value) -> Result<Vec<Port>> {
    if !array(field(v, "classical")?)?.is_empty() {
        return Err(invalid("pure preparation frame has classical entries"));
    }
    let ports = array(field(v, "quantum")?)?
        .iter()
        .map(port)
        .collect::<Result<Vec<_>>>()?;
    unique(&ports)?;
    Ok(ports)
}
fn endpoints(v: &Value) -> Result<(Vec<Port>, Vec<Port>)> {
    if text(field(v, "effect")?)? != "unitary" {
        return Err(invalid("crossed actual definition is not unitary"));
    }
    let h = field(v, "interface")?;
    Ok((side(field(h, "inputs")?)?, side(field(h, "outputs")?)?))
}
fn unique(ports: &[Port]) -> Result<()> {
    let owners: BTreeSet<_> = ports.iter().map(|p| p.owner).collect();
    let axes: Vec<_> = ports.iter().flat_map(|p| p.axes.iter()).collect();
    if owners.len() != ports.len() || axes.iter().collect::<BTreeSet<_>>().len() != axes.len() {
        return Err(invalid("source frame aliases owners or axes"));
    }
    Ok(())
}
fn quantum(items: &[Item]) -> Vec<Port> {
    items
        .iter()
        .filter_map(|i| {
            if let Item::Quantum(p) = i {
                Some(p.clone())
            } else {
                None
            }
        })
        .collect()
}
fn wires(ports: &[Port]) -> Vec<u32> {
    ports.iter().flat_map(|p| p.axes.iter().copied()).collect()
}

/// A read-only owner and ordered physical-coordinate view of a source frame.
#[derive(Clone, Copy, Debug)]
pub struct FramePort<'a>(&'a Port);
impl FramePort<'_> {
    pub fn owner(&self) -> u32 {
        self.0.owner
    }
    pub fn is_bit(&self) -> bool {
        self.0.bit
    }
    pub fn axes(&self) -> &[u32] {
        &self.0.axes
    }
}
/// One actual ordered source step, with complete quantum frames. Classical
/// packing remains present even though it leaves the quantum frame unchanged.
#[derive(Clone, Debug)]
pub struct SourceEvent {
    definition: usize,
    step: usize,
    call_path: Vec<usize>,
    module: String,
    span: Span,
    kind: &'static str,
    node: Option<usize>,
    inputs: Vec<Item>,
    outputs: Vec<Item>,
    before: Vec<Port>,
    after: Vec<Port>,
}
impl SourceEvent {
    pub fn kind(&self) -> &str {
        self.kind
    }
    pub fn definition(&self) -> usize {
        self.definition
    }
    pub fn step(&self) -> usize {
        self.step
    }
    pub fn call_path(&self) -> &[usize] {
        &self.call_path
    }
    pub fn module(&self) -> &str {
        &self.module
    }
    pub fn span(&self) -> Span {
        self.span
    }
    pub fn unitary_definition(&self) -> Option<usize> {
        self.node
    }
    pub fn input_frame(&self) -> impl Iterator<Item = FramePort<'_>> {
        self.before.iter().map(FramePort)
    }
    pub fn output_frame(&self) -> impl Iterator<Item = FramePort<'_>> {
        self.after.iter().map(FramePort)
    }
}
/// A proposed stable movement of one fresh init across earlier pure events.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InitializationMove {
    initialization: usize,
    crossed: Vec<usize>,
}
impl InitializationMove {
    pub fn initialization_event(&self) -> usize {
        self.initialization
    }
    pub fn crossed_events(&self) -> &[usize] {
        &self.crossed
    }
}
/// Structural pass validation for byte-identical freshly checked IR. This
/// result is neither an IR seal nor a general source-preservation theorem.
#[derive(Clone, Debug)]
pub struct PreparationValidation {
    events: usize,
    movements: usize,
}
impl PreparationValidation {
    pub fn events(&self) -> usize {
        self.events
    }
    pub fn movements(&self) -> usize {
        self.movements
    }
}

pub(super) fn record(
    state: &mut Instrument,
    definition: usize,
    step_index: usize,
    step: &SourceStep,
    inputs: Vec<Item>,
    outputs: Vec<Item>,
    node: Option<usize>,
) -> Result<()> {
    let kind = if node.is_some() {
        "pure"
    } else {
        match step.primitive() {
            Some("std::quantum::init0") => "init0",
            Some("std::observe::measure_z") => "observe",
            Some("std::classical::empty_bits") => "empty_bits",
            Some("std::classical::prepend_bit") => "prepend_bit",
            _ => return Err(invalid("unsupported trace step")),
        }
    };
    let cost = state
        .current
        .len()
        .checked_mul(2)
        .and_then(|n| n.checked_add(inputs.len() + outputs.len() + 16))
        .ok_or_else(|| invalid("trace accounting overflow"))?;
    state.trace_cells = state
        .trace_cells
        .checked_add(cost)
        .ok_or_else(|| invalid("trace accounting overflow"))?;
    if state.trace_cells > 100_000 || state.events.len() >= 10_000 {
        return Err(Error::new(
            "limit",
            step.span(),
            "source event trace exceeds retained cell/event budget",
        )
        .in_module(step.module()));
    }
    let before = state.current.clone();
    let selected = quantum(&inputs);
    let selected_ids: BTreeSet<_> = selected.iter().map(|p| p.owner).collect();
    let rest: Vec<_> = before
        .iter()
        .filter(|p| !selected_ids.contains(&p.owner))
        .cloned()
        .collect();
    let after = match kind {
        "init0" => [before.clone(), quantum(&outputs)].concat(),
        "pure" => [quantum(&outputs), rest].concat(),
        "observe" => rest,
        _ => before.clone(),
    };
    state.events.push(SourceEvent {
        definition,
        step: step_index,
        call_path: state.call_path.clone(),
        module: step.module().into(),
        span: step.span(),
        kind,
        node,
        inputs,
        outputs,
        before,
        after: after.clone(),
    });
    state.current = after;
    Ok(())
}
pub(super) fn propose_moves(events: &[SourceEvent]) -> Vec<InitializationMove> {
    let mut pure = vec![];
    let mut moves = vec![];
    for (i, e) in events.iter().enumerate() {
        if e.kind == "pure" {
            pure.push(i);
        } else if e.kind == "init0" {
            moves.push(InitializationMove {
                initialization: i,
                crossed: pure.clone(),
            });
        }
    }
    moves
}
pub(super) fn remap_events(
    events: &mut [SourceEvent],
    mapping: &BTreeMap<usize, usize>,
) -> Result<()> {
    for event in events {
        if let Some(old) = event.node {
            event.node = Some(
                *mapping
                    .get(&old)
                    .ok_or_else(|| invalid("compaction lost an actual source operation"))?,
            );
        }
    }
    Ok(())
}

fn atoms(v: &SourceValue) -> Vec<&SourceValue> {
    if v.ty().kind() == "tuple" {
        v.fields().iter().flat_map(atoms).collect()
    } else {
        vec![v]
    }
}
fn assign(
    value: &SourceValue,
    items: &[Item],
    environment: &mut BTreeMap<u32, Item>,
) -> Result<()> {
    let vs = atoms(value);
    if vs.len() != items.len() {
        return Err(invalid("trace result arity differs from actual source"));
    }
    for (v, item) in vs.into_iter().zip(items) {
        let valid = match item {
            Item::Quantum(p) => {
                v.ty().is_quantum()
                    && p.bit == (v.ty().kind() == "bit")
                    && Some(p.axes.len() as u32) == v.ty().width()
            }
            Item::Classical(xs) => !v.ty().is_quantum() && Some(xs.len() as u32) == v.ty().width(),
        };
        if !valid {
            return Err(invalid("trace value differs from complete source type"));
        }
        environment.insert(
            v.identity()
                .ok_or_else(|| invalid("source atom lacks identity"))?,
            item.clone(),
        );
    }
    Ok(())
}
fn take(
    value: &SourceValue,
    environment: &mut BTreeMap<u32, Item>,
    consuming: bool,
) -> Result<Vec<Item>> {
    atoms(value)
        .into_iter()
        .map(|v| {
            let id = v
                .identity()
                .ok_or_else(|| invalid("source atom lacks identity"))?;
            if consuming && v.ty().is_quantum() {
                environment.remove(&id)
            } else {
                environment.get(&id).cloned()
            }
            .ok_or_else(|| invalid("trace uses unavailable source owner"))
        })
        .collect()
}
struct Replay<'a> {
    proposal: &'a HierarchyProposal,
    definitions: &'a [Value],
    next: usize,
    calls: usize,
    current: Vec<Port>,
    seen_owners: BTreeSet<u32>,
    seen_axes: BTreeSet<u32>,
    measured: Vec<(Port, u32)>,
    fresh: Vec<Port>,
}
impl Replay<'_> {
    fn function(&mut self, id: usize, args: Vec<Item>, path: &mut Vec<usize>) -> Result<Vec<Item>> {
        self.calls += 1;
        if self.calls > 1024 || path.len() > 16 {
            return Err(invalid("source trace replay call bound exceeded"));
        }
        let d = self
            .proposal
            .source
            .definitions()
            .get(id)
            .ok_or_else(|| invalid("missing source definition"))?;
        let mut env = BTreeMap::new();
        let mut offset = 0;
        for input in d.inputs() {
            let end = offset + atoms(input).len();
            assign(
                input,
                args.get(offset..end)
                    .ok_or_else(|| invalid("source call argument count differs"))?,
                &mut env,
            )?;
            offset = end;
        }
        if offset != args.len() {
            return Err(invalid("extra source call argument"));
        }
        for (i, step) in d.steps().iter().enumerate() {
            let mut args = vec![];
            for input in step.inputs() {
                args.extend(take(input, &mut env, true)?);
            }
            let atomic = self
                .proposal
                .events
                .get(self.next)
                .is_some_and(|e| e.definition == id && e.step == i && e.call_path == *path);
            let outputs = if let Some(child) = step.called_definition().filter(|_| !atomic) {
                path.push(i);
                let output = self.function(child, args, path);
                path.pop();
                output?
            } else {
                let event = self
                    .proposal
                    .events
                    .get(self.next)
                    .ok_or_else(|| invalid("source event was omitted"))?;
                if !atomic
                    || event.module != step.module()
                    || event.span != step.span()
                    || event.inputs != args
                {
                    return Err(invalid(
                        "event does not match retained source step/operands",
                    ));
                }
                self.event(event, step)?;
                self.next += 1;
                event.outputs.clone()
            };
            assign(step.output(), &outputs, &mut env)?;
        }
        let result = take(d.output(), &mut env, true)?;
        if env.values().any(|v| matches!(v, Item::Quantum(_))) {
            return Err(invalid("source trace implicitly drops an owner"));
        }
        Ok(result)
    }
    fn event(&mut self, e: &SourceEvent, step: &SourceStep) -> Result<()> {
        if self.current != e.before {
            return Err(invalid("source full frames do not compose"));
        }
        unique(&e.before)?;
        unique(&e.after)?;
        let selected = quantum(&e.inputs);
        let outputs = quantum(&e.outputs);
        if selected.iter().any(|p| !self.current.contains(p))
            || selected
                .iter()
                .map(|p| p.owner)
                .collect::<BTreeSet<_>>()
                .len()
                != selected.len()
        {
            return Err(invalid(
                "source event duplicates or changes a selected owner",
            ));
        }
        let rest: Vec<_> = self
            .current
            .iter()
            .filter(|p| !selected.iter().any(|q| q.owner == p.owner))
            .cloned()
            .collect();
        let expected = match e.kind {
            "pure" => {
                if step.effect() != "unitary"
                    || e.inputs.len() != selected.len()
                    || e.outputs.len() != outputs.len()
                {
                    return Err(invalid("non-unitary source step proposed as pure"));
                }
                if !self.measured.is_empty()
                    && !step.primitive().is_some_and(|s| {
                        matches!(
                            s,
                            "std::registers::take_bit"
                                | "std::registers::put_bit"
                                | "std::registers::empty"
                                | "std::registers::consume_empty"
                        )
                    })
                {
                    return Err(invalid("quantum gate crossed observation"));
                }
                let d = self
                    .definitions
                    .get(
                        e.node
                            .ok_or_else(|| invalid("pure source event lacks actual definition"))?,
                    )
                    .ok_or_else(|| invalid("actual definition reference out of bounds"))?;
                if endpoints(d)? != (selected.clone(), outputs.clone()) {
                    return Err(invalid(
                        "actual unitary definition differs from source event frame",
                    ));
                }
                if wires(&selected).into_iter().collect::<BTreeSet<_>>()
                    != wires(&outputs).into_iter().collect()
                {
                    return Err(invalid("unitary event changes physical axis set"));
                }
                [outputs.clone(), rest].concat()
            }
            "init0" => {
                if step.primitive() != Some("std::quantum::init0")
                    || e.node.is_some()
                    || !e.inputs.is_empty()
                    || e.outputs.len() != 1
                    || outputs.len() != 1
                    || !outputs[0].bit
                    || outputs[0].axes.len() != 1
                    || !self.measured.is_empty()
                {
                    return Err(invalid("invalid or post-observation fresh initialization"));
                }
                let p = &outputs[0];
                if self.seen_owners.contains(&p.owner) || self.seen_axes.contains(&p.axes[0]) {
                    return Err(invalid("initialization is not globally fresh"));
                }
                self.seen_axes.insert(p.axes[0]);
                self.fresh.push(p.clone());
                [self.current.clone(), outputs.clone()].concat()
            }
            "observe" => {
                if step.primitive() != Some("std::observe::measure_z")
                    || e.node.is_some()
                    || selected.len() != 1
                    || !selected[0].bit
                    || e.inputs.len() != 1
                    || e.outputs.len() != 1
                {
                    return Err(invalid("invalid observation source event"));
                }
                let Item::Classical(ids) = &e.outputs[0] else {
                    return Err(invalid("observation lacks classical result"));
                };
                if ids.len() != 1 || self.measured.iter().any(|(_, id)| id == &ids[0]) {
                    return Err(invalid("observation result aliases another value"));
                }
                self.measured.push((selected[0].clone(), ids[0]));
                rest
            }
            "empty_bits" => {
                if step.primitive() != Some("std::classical::empty_bits")
                    || e.node.is_some()
                    || !e.inputs.is_empty()
                    || e.outputs != [Item::Classical(vec![])]
                {
                    return Err(invalid("invalid empty classical packing"));
                }
                self.current.clone()
            }
            "prepend_bit" => {
                if step.primitive() != Some("std::classical::prepend_bit")
                    || e.node.is_some()
                    || e.inputs.len() != 2
                {
                    return Err(invalid("invalid classical prepend event"));
                }
                let (Item::Classical(a), Item::Classical(b)) = (&e.inputs[0], &e.inputs[1]) else {
                    return Err(invalid("classical prepend uses quantum input"));
                };
                if a.len() != 1 || e.outputs != [Item::Classical([a.clone(), b.clone()].concat())] {
                    return Err(invalid("classical pack order changed"));
                }
                self.current.clone()
            }
            _ => return Err(invalid("unknown source event kind")),
        };
        if expected != e.after {
            return Err(invalid("source event omits or changes an untouched owner"));
        }
        for p in &outputs {
            if self.seen_owners.contains(&p.owner) && !selected.iter().any(|q| q == p) {
                return Err(invalid("source output reuses a prior owner identity"));
            }
            self.seen_owners.insert(p.owner);
        }
        self.current = expected;
        Ok(())
    }
}

fn definition(defs: &[Value], i: usize) -> Result<&Value> {
    defs.get(i)
        .ok_or_else(|| invalid("missing actual graph definition"))
}
fn route(defs: &[Value], i: usize, before: &[Port], after: &[Port]) -> Result<()> {
    let d = definition(defs, i)?;
    if endpoints(d)? != (before.to_vec(), after.to_vec()) {
        return Err(invalid("framing route has different full endpoints"));
    }
    let body = field(d, "body")?;
    if tag(body)? != "rewire" {
        return Err(invalid("framing route is not an explicit rewire"));
    }
    let p = field(body, "permutation")?;
    let owners = after
        .iter()
        .map(|a| {
            before
                .iter()
                .position(|b| a == b)
                .ok_or_else(|| invalid("framing route loses owner identity"))
        })
        .collect::<Result<Vec<_>>>()?;
    let input = wires(before);
    let axes = wires(after)
        .iter()
        .map(|a| {
            input
                .iter()
                .position(|b| a == b)
                .ok_or_else(|| invalid("framing route loses an axis"))
        })
        .collect::<Result<Vec<_>>>()?;
    if indices(field(p, "owners")?)? != owners
        || indices(field(p, "axes")?)? != axes
        || !array(field(p, "classical")?)?.is_empty()
    {
        return Err(invalid(
            "framing permutation differs from actual source frame",
        ));
    }
    Ok(())
}
fn pure_root(
    defs: &[Value],
    root: usize,
    inputs: &[Port],
    outputs: &[Port],
    events: &[SourceEvent],
) -> Result<()> {
    let d = definition(defs, root)?;
    if endpoints(d)? != (inputs.to_vec(), outputs.to_vec()) {
        return Err(invalid("reordered root has wrong boundary frames"));
    }
    let pure: Vec<_> = events.iter().filter_map(|e| e.node).collect();
    let body = field(d, "body")?;
    if pure.is_empty() && inputs == outputs {
        return route(defs, root, inputs, outputs);
    }
    if tag(body)? != "sequence" {
        return Err(invalid(
            "reordered root is not the complete ordered source sequence",
        ));
    }
    let children = indices(field(body, "children")?)?;
    let mut cursor = 0;
    let mut current = inputs.to_vec();
    let next = |cursor: &mut usize| -> Result<usize> {
        let i = *children
            .get(*cursor)
            .ok_or_else(|| invalid("source operation omitted from root"))?;
        *cursor += 1;
        Ok(i)
    };
    for id in pure {
        let (selected, result) = endpoints(definition(defs, id)?)?;
        if selected.iter().any(|p| !current.contains(p)) {
            return Err(invalid("reordered operation lacks its selected owner"));
        }
        let rest: Vec<_> = current
            .iter()
            .filter(|p| !selected.iter().any(|s| s.owner == p.owner))
            .cloned()
            .collect();
        let arranged = [selected.clone(), rest.clone()].concat();
        if arranged != current {
            route(defs, next(&mut cursor)?, &current, &arranged)?;
        }
        let applied = next(&mut cursor)?;
        if rest.is_empty() {
            if applied != id {
                return Err(invalid("root substitutes a source operation"));
            }
        } else {
            let tensor = definition(defs, applied)?;
            let t = field(tensor, "body")?;
            if tag(t)? != "tensor"
                || number(field(t, "left")?)? != id
                || endpoints(tensor)? != (arranged, [result.clone(), rest.clone()].concat())
            {
                return Err(invalid(
                    "root does not tensor the actual source operation with its complete frame",
                ));
            }
            route(defs, number(field(t, "right")?)?, &rest, &rest)?;
        }
        current = [result, rest].concat();
    }
    if current != outputs {
        route(defs, next(&mut cursor)?, &current, outputs)?;
    }
    if cursor != children.len() {
        return Err(invalid("root contains an extra operation"));
    }
    Ok(())
}

pub(super) fn validate(proposal: &HierarchyProposal) -> Result<PreparationValidation> {
    if !proposal.instrument {
        return Err(invalid(
            "preparation validation requires an instrument proposal",
        ));
    }
    let actual = json::parse(&proposal.payload).map_err(transport)?;
    let graph = field(&actual, "circuit")?;
    if graph != &json::parse(&proposal.graph).map_err(transport)? {
        return Err(invalid(
            "retained pure graph differs from actual instrument",
        ));
    }
    let defs = array(field(graph, "definitions")?)?;
    let prep = field(&actual, "preparation")?;
    let initializations = array(field(prep, "initializations")?)?;
    let initial = if let Some(first) = initializations.first() {
        side(field(field(first, "interface")?, "inputs")?)?
    } else {
        side(field(prep, "outputs")?)?
    };
    let mut replay = Replay {
        proposal,
        definitions: defs,
        next: 0,
        calls: 0,
        current: initial.clone(),
        seen_owners: initial.iter().map(|p| p.owner).collect(),
        seen_axes: wires(&initial).into_iter().collect(),
        measured: vec![],
        fresh: vec![],
    };
    let returned = replay.function(
        proposal.source.root(),
        initial.iter().cloned().map(Item::Quantum).collect(),
        &mut vec![],
    )?;
    if replay.next != proposal.events.len() {
        return Err(invalid("extra event after source return"));
    }
    let classical: Vec<_> = returned
        .iter()
        .filter_map(|i| {
            if let Item::Classical(xs) = i {
                Some(xs.clone())
            } else {
                None
            }
        })
        .collect();
    if classical
        != [replay
            .measured
            .iter()
            .map(|(_, id)| *id)
            .collect::<Vec<_>>()]
    {
        return Err(invalid("source return differs from chronological readout"));
    }
    if quantum(&returned)
        .iter()
        .map(|p| p.owner)
        .collect::<BTreeSet<_>>()
        .len()
        != quantum(&returned).len()
    {
        return Err(invalid("source returns duplicate quantum owners"));
    }
    let residual = quantum(&returned);
    if residual.len() != replay.current.len()
        || residual.iter().any(|p| !replay.current.contains(p))
    {
        return Err(invalid("source return loses or changes a residual owner"));
    }
    // Reconstruct the required crossings independently of the producer helper.
    let expected_moves = proposal
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| e.kind == "init0")
        .map(|(i, _)| InitializationMove {
            initialization: i,
            crossed: (0..i)
                .filter(|j| proposal.events[*j].node.is_some())
                .collect(),
        })
        .collect::<Vec<_>>();
    if proposal.moves != expected_moves {
        return Err(invalid(
            "initialization move omits or adds crossed source events",
        ));
    }
    for movement in &proposal.moves {
        let init = &proposal.events[movement.initialization];
        let fresh = quantum(&init.outputs);
        for &prior in &movement.crossed {
            let e = &proposal.events[prior];
            if e.kind != "pure"
                || fresh.iter().any(|f| {
                    e.before
                        .iter()
                        .chain(&e.after)
                        .any(|p| p.owner == f.owner || p.axes.iter().any(|a| f.axes.contains(a)))
                })
            {
                return Err(invalid(
                    "initialization crosses an effect or non-disjoint owner frame",
                ));
            }
        }
    }
    let mut current = initial;
    if initializations.len() != replay.fresh.len() {
        return Err(invalid(
            "reordered preparation omits or adds an initialization",
        ));
    }
    for (d, p) in initializations.iter().zip(&replay.fresh) {
        let h = field(d, "interface")?;
        let after = [current.clone(), vec![p.clone()]].concat();
        let b = field(d, "body")?;
        if text(field(d, "effect")?)? != "iso"
            || tag(b)? != "init0"
            || number(field(b, "output")?)? != p.owner as usize
            || side(field(h, "inputs")?)? != current
            || side(field(h, "outputs")?)? != after
        {
            return Err(invalid(
                "actual initialization differs from stable source extraction",
            ));
        }
        current = after;
    }
    if side(field(prep, "outputs")?)? != current {
        return Err(invalid(
            "preparation output differs from extracted fresh owners",
        ));
    }
    let desired = [
        replay
            .measured
            .iter()
            .map(|(p, _)| p.clone())
            .collect::<Vec<_>>(),
        quantum(&returned),
    ]
    .concat();
    let root = number(field(field(graph, "entry")?, "implementation")?)?;
    pure_root(defs, root, &current, &desired, &proposal.events)?;
    let readout = field(&actual, "readout")?;
    if indices(field(readout, "pack")?)?
        != replay
            .measured
            .iter()
            .map(|(_, id)| *id as usize)
            .collect::<Vec<_>>()
    {
        return Err(invalid("actual readout packing differs from source"));
    }
    let measures = array(field(readout, "measurements")?)?;
    if measures.len() != replay.measured.len() {
        return Err(invalid("actual readout changes observation count"));
    }
    for (d, (p, id)) in measures.iter().zip(&replay.measured) {
        let body = field(d, "body")?;
        if text(field(d, "effect")?)? != "observe"
            || tag(body)? != "observe_z"
            || number(field(body, "input")?)? != p.owner as usize
            || number(field(body, "output")?)? != *id as usize
        {
            return Err(invalid("actual readout differs from source observation"));
        }
    }
    Ok(PreparationValidation {
        events: proposal.events.len(),
        movements: proposal
            .moves
            .iter()
            .filter(|m| !m.crossed.is_empty())
            .count(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::sized::ParsedProgram;
    fn proposal() -> HierarchyProposal {
        let source = "use std::quantum::h; use std::quantum::init0; use std::observe::measure_z; use std::classical::empty_bits; use std::classical::prepend_bit; pub observe fn f(q: Q<Bit>, z: Q<Bits<0>>) -> (CBits<1>, Q<Bit>, Q<Bits<0>>) { let q = h(q); let fresh = init0(); let bit = measure_z(fresh); let bits = empty_bits(); (prepend_bit[0](bit,bits),q,z) }";
        ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())]))
            .unwrap()
            .instantiate("main::f", BTreeMap::new(), BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap()
            .lower()
            .unwrap()
    }
    fn rejects(p: &HierarchyProposal) {
        assert_eq!(validate(p).unwrap_err().code(), "preservation");
    }
    fn object_mut(v: &mut Value) -> &mut BTreeMap<String, Value> {
        let Value::Object(v) = v else {
            panic!("expected object")
        };
        v
    }
    fn graph_mutation(p: &mut HierarchyProposal, change: impl FnOnce(&mut Value)) {
        let mut actual = json::parse(&p.payload).unwrap();
        let graph = object_mut(&mut actual).get_mut("circuit").unwrap();
        change(graph);
        p.graph = json::encode(graph).unwrap();
        p.payload = json::encode(&actual).unwrap();
    }
    #[test]
    fn initialization_certificate_rejects_missing_crossings_and_source_events() {
        let valid = proposal();
        assert_eq!(validate(&valid).unwrap().movements(), 1);
        let mut bad = valid.clone();
        bad.moves[0].crossed.clear();
        rejects(&bad);
        let mut bad = valid.clone();
        bad.moves[0].crossed.push(2);
        rejects(&bad);
        let mut bad = valid.clone();
        bad.events.remove(0);
        rejects(&bad);
        let mut bad = valid.clone();
        bad.events.swap(0, 1);
        rejects(&bad);
        let mut bad = valid.clone();
        bad.events[0].call_path.push(0);
        rejects(&bad);
        let mut bad = valid.clone();
        bad.events[0].span.start += 1;
        rejects(&bad);
    }
    #[test]
    fn initialization_certificate_rejects_aliases_incomplete_frames_and_wrong_values() {
        let valid = proposal();
        let mut bad = valid.clone();
        bad.events[0].before.retain(|p| !p.axes.is_empty());
        rejects(&bad);
        let mut bad = valid.clone();
        let Item::Quantum(p) = &mut bad.events[1].outputs[0] else {
            panic!()
        };
        p.axes = vec![0];
        rejects(&bad);
        let mut bad = valid.clone();
        let old = bad.events[0].before[0].owner;
        let Item::Quantum(p) = &mut bad.events[1].outputs[0] else {
            panic!()
        };
        p.owner = old;
        rejects(&bad);
        let mut bad = valid.clone();
        bad.events[1].after.pop();
        rejects(&bad);
        let mut bad = valid.clone();
        bad.events[2].outputs = vec![Item::Classical(vec![123])];
        rejects(&bad);
        let mut bad = valid.clone();
        bad.events.last_mut().unwrap().outputs = vec![Item::Classical(vec![])];
        rejects(&bad);
    }
    #[test]
    fn initialization_certificate_reads_actual_transport_and_rejects_root_changes() {
        let valid = proposal();
        let pure = valid.events[0].node.unwrap();
        let mut bad = valid.clone();
        graph_mutation(&mut bad, |graph| {
            let Value::Array(defs) = object_mut(graph).get_mut("definitions").unwrap() else {
                panic!()
            };
            object_mut(&mut defs[pure]).insert("effect".into(), Value::String("observe".into()));
        });
        rejects(&bad);
        let mut bad = valid.clone();
        graph_mutation(&mut bad, |graph| {
            let root =
                number(field(field(graph, "entry").unwrap(), "implementation").unwrap()).unwrap();
            let Value::Array(defs) = object_mut(graph).get_mut("definitions").unwrap() else {
                panic!()
            };
            let body = object_mut(&mut defs[root]).get_mut("body").unwrap();
            let Value::Array(children) = object_mut(body).get_mut("children").unwrap() else {
                panic!()
            };
            children.pop();
        });
        rejects(&bad);
        let mut bad = valid;
        graph_mutation(&mut bad, |graph| {
            let Value::Array(defs) = object_mut(graph).get_mut("definitions").unwrap() else {
                panic!()
            };
            let h = object_mut(&mut defs[pure]).get_mut("interface").unwrap();
            let input = object_mut(h).get_mut("inputs").unwrap();
            object_mut(input).insert("quantum".into(), Value::Array(vec![]));
        });
        rejects(&bad);
    }
}
