//! Bounded untrusted proposal generation. Native reconstruction is still required.
use super::primitive::Primitive;
use super::{
    ElaboratedProgram, Error, HierarchyEligibility, Result, SourceDefinition, SourceOperation,
    SourceStep, SourceType, SourceValue, Span,
};
use crate::contract::{
    BasisType,
    exact::{Exact, Matrix},
};
use crate::interchange::{self, RootInterface, Version};
use crate::ir::{
    BasisShape, CircuitAction, CircuitStep, Effect, QuantumPort, RawOp, RawProgram, SingleGate,
    TokenId, WireId,
};
use std::collections::{BTreeMap, BTreeSet};
#[path = "fourier.rs"]
mod fourier;
mod preservation;
pub use preservation::{FramePort, InitializationMove, PreparationValidation, SourceEvent};

/// Immutable transport proposal retaining the complete source-order precursor.
/// The comparison request is derived from this proposal, not a named algorithm.
#[derive(Clone)]
pub struct HierarchyProposal {
    source: ElaboratedProgram,
    payload: Vec<u8>,
    comparison: Vec<u8>,
    graph: Vec<u8>,
    precursor: Vec<u8>,
    instrument: bool,
    events: Vec<SourceEvent>,
    moves: Vec<InitializationMove>,
}
impl std::fmt::Debug for HierarchyProposal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("HierarchyProposal")
            .field("entry", &self.source.instantiation().entry())
            .field("payload_bytes", &self.payload.len())
            .field("instrument", &self.instrument)
            .field("source_events", &self.events.len())
            .field("initialization_moves", &self.moves.len())
            .finish()
    }
}
impl HierarchyProposal {
    pub fn source(&self) -> &ElaboratedProgram {
        &self.source
    }
    pub fn payload(&self) -> &[u8] {
        &self.payload
    }
    pub fn comparison_request(&self) -> &[u8] {
        &self.comparison
    }
    pub fn pure_graph(&self) -> &[u8] {
        &self.graph
    }
    /// Untrusted pre-compaction table retaining the original source-derived
    /// definitions, including bodies replaced by exact trace factoring.
    pub fn lowering_precursor(&self) -> &[u8] {
        &self.precursor
    }
    /// Whether the proposal uses initialization/unitary/readout transport.
    /// This includes principal Iso roots with no measurements and does not
    /// classify the source effect or establish an isometry theorem.
    pub fn is_instrument(&self) -> bool {
        self.instrument
    }
    pub fn source_events(&self) -> &[SourceEvent] {
        &self.events
    }
    pub fn initialization_moves(&self) -> &[InitializationMove] {
        &self.moves
    }
    /// Validate only stable extraction of fresh initialization against this
    /// exact freshly checked instrument. Source-to-unitary translation remains
    /// a separate obligation; this does not issue production IR evidence.
    pub fn validate_initialization_moves(
        &self,
        checked: &crate::interchange::hierarchical::CheckedInstrument,
    ) -> Result<PreparationValidation> {
        if checked.reconstruction().payload() != self.payload() {
            return Err(preservation::invalid(
                "checked payload differs from source proposal",
            ));
        }
        preservation::validate(self)
    }

    /// Validate source-order initialization moves against the same immutable
    /// instrument accepted natively, without rebuilding legacy Rust leaves.
    pub fn validate_initialization_moves_native(
        &self,
        checked: &crate::interchange::hierarchical::NativeChecked,
    ) -> Result<PreparationValidation> {
        if !checked.is_instrument() || checked.payload() != self.payload() {
            return Err(preservation::invalid(
                "native checked instrument differs from source proposal",
            ));
        }
        preservation::validate(self)
    }
}

fn fail(message: impl Into<String>) -> Error {
    Error::new("unsupported", Span::default(), message)
}
fn limit(message: impl Into<String>) -> Error {
    Error::new("limit", Span::default(), message)
}
fn quote(s: &str) -> String {
    let mut result = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => result.push_str("\\\""),
            '\\' => result.push_str("\\\\"),
            c if c < '\u{20}' => {
                use std::fmt::Write;
                write!(result, "\\u{:04x}", c as u32).unwrap();
            }
            c => result.push(c),
        }
    }
    result.push('"');
    result
}
fn object(fields: &[(&str, String)]) -> String {
    format!(
        "{{{}}}",
        fields
            .iter()
            .map(|(k, v)| format!("{}:{v}", quote(k)))
            .collect::<Vec<_>>()
            .join(",")
    )
}
fn array(xs: impl IntoIterator<Item = String>) -> String {
    format!("[{}]", xs.into_iter().collect::<Vec<_>>().join(","))
}
fn numbers(xs: impl IntoIterator<Item = usize>) -> String {
    array(xs.into_iter().map(|n| n.to_string()))
}
fn tagged(tag: &str, fields: &[(&str, String)]) -> String {
    let mut result = vec![("tag", quote(tag))];
    result.extend_from_slice(fields);
    object(&result)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PortKind {
    Unit,
    Bit,
    Bits,
    Tuple,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Port {
    owner: u32,
    kind: PortKind,
    basis: SourceType,
    axes: Vec<u32>,
}
impl Port {
    fn json(&self) -> String {
        let mut basis = Vec::new();
        let mut pending = vec![&self.basis];
        while let Some(ty) = pending.pop() {
            use crate::frontend::types::Kind;
            basis.push(match &ty.kind {
                Kind::Unit => tagged("unit", &[]),
                Kind::Bit => tagged("bit", &[]),
                Kind::Bits(width) => tagged("bits", &[("width", width.to_string())]),
                Kind::Tuple(fields) => {
                    pending.extend(fields.iter().rev());
                    tagged("tuple", &[("arity", fields.len().to_string())])
                }
                Kind::Q(_) | Kind::Parameter(_) => unreachable!("validated closed ordinary basis"),
            });
        }
        object(&[
            ("owner", self.owner.to_string()),
            ("basis", array(basis)),
            ("axes", numbers(self.axes.iter().map(|n| *n as usize))),
        ])
    }
}
fn side(ports: &[Port], classical: &[(u32, bool, usize)]) -> String {
    object(&[
        ("quantum", array(ports.iter().map(Port::json))),
        (
            "classical",
            array(classical.iter().map(|(id, bit, n)| {
                object(&[
                    ("value", id.to_string()),
                    (
                        "basis",
                        array([if *bit {
                            tagged("bit", &[])
                        } else {
                            tagged("bits", &[("width", n.to_string())])
                        }]),
                    ),
                ])
            })),
        ),
    ])
}
fn header(before: &[Port], after: &[Port]) -> String {
    object(&[("inputs", side(before, &[])), ("outputs", side(after, &[]))])
}
fn axes(ports: &[Port]) -> Vec<u32> {
    ports.iter().flat_map(|p| p.axes.iter().copied()).collect()
}
fn frame_capacity<'a>(ports: impl Iterator<Item = &'a Port>) -> Result<()> {
    let mut cells = 0usize;
    let mut width = 0usize;
    for port in ports {
        let size = port
            .basis
            .storage_size(4096, 64)
            .ok_or_else(|| limit("port basis exceeds type capacity"))?;
        cells = cells
            .checked_add(size.nodes)
            .ok_or_else(|| limit("frame type accounting overflow"))?;
        width = width
            .checked_add(port.axes.len())
            .ok_or_else(|| limit("frame width overflow"))?;
        if cells > 4096 || port.axes.len() > 8 || width > 16 {
            return Err(limit(
                "frame exceeds basis representation or quantum width capacity",
            ));
        }
    }
    Ok(())
}
fn validate(ports: &[Port]) -> Result<()> {
    frame_capacity(ports.iter())?;
    if ports.len() > 4096
        || ports.iter().map(|p| p.owner).collect::<BTreeSet<_>>().len() != ports.len()
    {
        return Err(fail("proposal aliases an owner or exceeds port capacity"));
    }
    let wires = axes(ports);
    if wires.len() > 16
        || wires.iter().collect::<BTreeSet<_>>().len() != wires.len()
        || ports.iter().any(|p| {
            p.axes.len() > 8
                || p.basis.storage_size(4096, 64).is_none()
                || p.basis.basis_width() != Some(p.axes.len() as u32)
                || match p.kind {
                    PortKind::Unit => p.basis.kind() != "unit",
                    PortKind::Bit => p.basis.kind() != "bit",
                    PortKind::Bits => p.basis.kind() != "bits",
                    PortKind::Tuple => p.basis.kind() != "tuple",
                }
        })
    {
        return Err(fail(
            "proposal aliases axes or exceeds the selected quantum profile",
        ));
    }
    Ok(())
}
#[derive(Clone, Debug)]
struct Node {
    before: Vec<Port>,
    after: Vec<Port>,
    definition: String,
    meaning: String,
    proof: String,
}
struct Graph {
    nodes: Vec<Node>,
    encodings: Vec<String>,
    encoding_cache: BTreeMap<String, usize>,
    cache: BTreeMap<String, usize>,
    bytes: usize,
}
impl Graph {
    fn new() -> Self {
        Self {
            nodes: vec![],
            encodings: vec![],
            encoding_cache: BTreeMap::new(),
            cache: BTreeMap::new(),
            bytes: 0,
        }
    }
    fn charge(&mut self, n: usize) -> Result<()> {
        self.bytes = self
            .bytes
            .checked_add(n)
            .ok_or_else(|| limit("proposal byte accounting overflow"))?;
        if self.bytes > 16 << 20 {
            return Err(limit("proposal exceeds 16 MiB"));
        }
        Ok(())
    }
    fn encoding(&mut self, ports: &[Port]) -> Result<usize> {
        let s = side(ports, &[]);
        if let Some(i) = self.encoding_cache.get(&s) {
            return Ok(*i);
        }
        let text = object(&[
            ("logical", s.clone()),
            ("physical", s.clone()),
            ("body", tagged("identity", &[])),
        ]);
        self.charge(text.len() + s.len())?;
        let i = self.encodings.len();
        self.encodings.push(text);
        self.encoding_cache.insert(s, i);
        Ok(i)
    }
    fn add(
        &mut self,
        before: Vec<Port>,
        after: Vec<Port>,
        body: String,
        meaning: String,
        rule: &str,
        premises: Vec<usize>,
    ) -> Result<usize> {
        validate(&before)?;
        validate(&after)?;
        let h = header(&before, &after);
        let key = format!("{h}|{body}|{meaning}|{rule}|{premises:?}");
        if let Some(i) = self.cache.get(&key) {
            return Ok(*i);
        }
        if self.nodes.len() >= 10_000 {
            return Err(limit("proposal exceeds 10000 definitions"));
        }
        if premises.iter().any(|i| *i >= self.nodes.len()) {
            return Err(fail("proposal premise is not an earlier definition"));
        }
        let input_encoding = self.encoding(&before)?;
        let output_encoding = self.encoding(&after)?;
        let i = self.nodes.len();
        let definition = object(&[
            ("interface", h.clone()),
            ("effect", quote("unitary")),
            ("body", body),
        ]);
        let meaning = object(&[("interface", h), ("body", meaning)]);
        let proof = object(&[
            ("kind", quote("equation")),
            ("rule", tagged(rule, &[])),
            ("premises", numbers(premises)),
            ("implementation", i.to_string()),
            ("meaning", i.to_string()),
            ("input_encoding", input_encoding.to_string()),
            ("output_encoding", output_encoding.to_string()),
            (
                "witness",
                object(&[
                    ("template_version", "1".into()),
                    ("parameters", "[]".into()),
                    ("references", "[]".into()),
                ]),
            ),
        ]);
        self.charge(definition.len() + meaning.len() + proof.len() + key.len())?;
        self.nodes.push(Node {
            before,
            after,
            definition,
            meaning,
            proof,
        });
        self.cache.insert(key, i);
        Ok(i)
    }
    fn rewire(
        &mut self,
        before: Vec<Port>,
        after: Vec<Port>,
        owners: Vec<usize>,
        wires: Vec<usize>,
    ) -> Result<usize> {
        let body = tagged(
            "rewire",
            &[(
                "permutation",
                object(&[
                    ("owners", numbers(owners)),
                    ("axes", numbers(wires)),
                    ("classical", "[]".into()),
                ]),
            )],
        );
        self.add(before, after, body.clone(), body, "rewire", vec![])
    }
    fn rename(&mut self, before: Vec<Port>, after: Vec<Port>) -> Result<usize> {
        if before.len() != after.len()
            || before
                .iter()
                .zip(&after)
                .any(|(a, b)| a.basis != b.basis || a.axes.len() != b.axes.len())
        {
            return Err(fail("proposal rename changes an owner type"));
        }
        let n = axes(&before).len();
        let owners = (0..before.len()).collect();
        self.rewire(before, after, owners, (0..n).collect())
    }
    fn route(&mut self, before: Vec<Port>, after: Vec<Port>) -> Result<usize> {
        if before.len() != after.len() {
            return Err(fail("proposal routing loses owners"));
        }
        let ws = axes(&before);
        let owners = after
            .iter()
            .map(|p| {
                before
                    .iter()
                    .position(|q| q == p)
                    .ok_or_else(|| fail("proposal route changes owner metadata"))
            })
            .collect::<Result<Vec<_>>>()?;
        let wires = axes(&after)
            .iter()
            .map(|w| {
                ws.iter()
                    .position(|v| v == w)
                    .ok_or_else(|| fail("proposal route loses axes"))
            })
            .collect::<Result<Vec<_>>>()?;
        self.rewire(before, after, owners, wires)
    }
    fn identity(&mut self, ports: Vec<Port>) -> Result<usize> {
        self.rename(ports.clone(), ports)
    }
    fn sequence(&mut self, children: Vec<usize>) -> Result<usize> {
        let first = *children
            .first()
            .ok_or_else(|| fail("empty proposal sequence"))?;
        for w in children.windows(2) {
            if self.nodes[w[0]].after != self.nodes[w[1]].before {
                return Err(fail("proposal sequence endpoints disagree"));
            }
        }
        let before = self.nodes[first].before.clone();
        let after = self.nodes[*children.last().unwrap()].after.clone();
        let body = tagged(
            "sequence",
            &[("children", numbers(children.iter().copied()))],
        );
        self.add(before, after, body.clone(), body, "sequence", children)
    }
    fn tensor(&mut self, a: usize, b: usize) -> Result<usize> {
        frame_capacity(self.nodes[a].before.iter().chain(&self.nodes[b].before))?;
        frame_capacity(self.nodes[a].after.iter().chain(&self.nodes[b].after))?;
        let before = [self.nodes[a].before.clone(), self.nodes[b].before.clone()].concat();
        let after = [self.nodes[a].after.clone(), self.nodes[b].after.clone()].concat();
        let body = tagged(
            "tensor",
            &[("left", a.to_string()), ("right", b.to_string())],
        );
        self.add(before, after, body.clone(), body, "tensor", vec![a, b])
    }
    fn frame(
        &mut self,
        inputs: Vec<Port>,
        children: &[usize],
        outputs: Vec<Port>,
    ) -> Result<usize> {
        let mut current = inputs;
        let mut steps = Vec::new();
        for &child in children {
            let before = self.nodes[child].before.clone();
            let after = self.nodes[child].after.clone();
            let selected: BTreeSet<_> = before.iter().map(|p| p.owner).collect();
            if before.iter().any(|p| !current.contains(p)) {
                return Err(fail("proposal frame loses an operation input"));
            }
            let rest: Vec<_> = current
                .iter()
                .filter(|p| !selected.contains(&p.owner))
                .cloned()
                .collect();
            frame_capacity(after.iter().chain(&rest))?;
            let arranged = [before, rest.clone()].concat();
            if current != arranged {
                steps.push(self.route(current, arranged)?);
            }
            let node = if rest.is_empty() {
                child
            } else {
                let identity = self.identity(rest.clone())?;
                self.tensor(child, identity)?
            };
            steps.push(node);
            current = [after, rest].concat();
        }
        if current != outputs {
            steps.push(self.route(current, outputs.clone())?);
        }
        if steps.is_empty() {
            self.identity(outputs)
        } else {
            self.sequence(steps)
        }
    }
    fn structural(
        &mut self,
        before: Vec<Port>,
        after: Vec<Port>,
        tag: &str,
        ns: &[u32],
    ) -> Result<usize> {
        let fields = if ns.is_empty() {
            vec![]
        } else {
            vec![
                ("width", ns[0].to_string()),
                ("position", ns[1].to_string()),
            ]
        };
        let body = tagged("structural", &[("operation", tagged(tag, &fields))]);
        self.add(before, after, body.clone(), body, "structural", vec![])
    }
    fn artifact(&self, root: usize) -> String {
        object(&[
            ("format", quote("qleisli.hierarchical-ir")),
            ("version", "1".into()),
            ("profile", quote("qpe-dyadic8-v1")),
            (
                "definitions",
                array(self.nodes.iter().map(|n| n.definition.clone())),
            ),
            (
                "meanings",
                array(self.nodes.iter().map(|n| n.meaning.clone())),
            ),
            ("encodings", array(self.encodings.iter().cloned())),
            ("proofs", array(self.nodes.iter().map(|n| n.proof.clone()))),
            (
                "entry",
                object(&[
                    ("implementation", root.to_string()),
                    ("proof", root.to_string()),
                ]),
            ),
        ])
    }
    fn comparison(&self, root: usize) -> String {
        let n = &self.nodes[root];
        object(&[
            ("format", quote("qleisli.hierarchy-request")),
            ("version", "1".into()),
            ("profile", quote("qpe-dyadic8-v1")),
            ("kind", quote("equation")),
            ("effect", quote("unitary")),
            ("interface", header(&n.before, &n.after)),
            (
                "meanings",
                array(self.nodes.iter().map(|n| n.meaning.clone())),
            ),
            ("entry", root.to_string()),
        ])
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Item {
    Quantum(Port),
    Classical(Vec<u32>),
}
fn leaves(value: &SourceValue) -> Vec<&SourceValue> {
    // Ordinary Unit carries no value port. This is a constructor check,
    // never a width-zero rule: empty quantum/register values remain atoms.
    if value.ty().kind() == "unit" && !value.ty().is_quantum() {
        return Vec::new();
    }
    if value.ty().kind() == "tuple" && !value.ty().is_quantum() {
        value.fields().iter().flat_map(leaves).collect()
    } else {
        vec![value]
    }
}
fn quantum(items: &[Item]) -> Vec<Port> {
    items
        .iter()
        .filter_map(|i| match i {
            Item::Quantum(p) => Some(p.clone()),
            _ => None,
        })
        .collect()
}
fn read(value: &SourceValue, values: &BTreeMap<u32, Item>) -> Result<Vec<Item>> {
    leaves(value)
        .iter()
        .map(|v| {
            values
                .get(
                    &v.identity()
                        .ok_or_else(|| fail("missing source value identity"))?,
                )
                .cloned()
                .ok_or_else(|| fail("source value is unavailable during lowering"))
        })
        .collect()
}
fn bind(value: &SourceValue, items: Vec<Item>, values: &mut BTreeMap<u32, Item>) -> Result<()> {
    let ls = leaves(value);
    if ls.len() != items.len() {
        return Err(fail("lowered source value shape differs"));
    }
    for (v, item) in ls.into_iter().zip(items) {
        match &item {
            Item::Quantum(p)
                if v.ty().is_quantum()
                    && v.ty().quantum_basis() == Some(&p.basis)
                    && p.axes.len() == v.ty().width().unwrap() as usize => {}
            Item::Classical(bits)
                if !v.ty().is_quantum() && bits.len() == v.ty().width().unwrap_or(0) as usize => {}
            _ => return Err(fail("lowered source value type differs")),
        }
        values.insert(v.identity().unwrap(), item);
    }
    Ok(())
}
fn consume(inputs: &[SourceValue], values: &mut BTreeMap<u32, Item>) -> Result<Vec<Item>> {
    let mut result = vec![];
    for input in inputs {
        let items = read(input, values)?;
        for v in leaves(input) {
            if v.ty().is_quantum() {
                values.remove(&v.identity().unwrap());
            }
        }
        result.extend(items);
    }
    Ok(result)
}

struct Lower<'a> {
    source: &'a ElaboratedProgram,
    native_operations: &'a [NativeOperation<'a>],
    graph: Graph,
    owner: u32,
    pure: BTreeMap<usize, usize>,
    gate_cache: BTreeMap<usize, bool>,
    finite_gates: BTreeMap<u8, usize>,
    inline_visits: usize,
}
struct NativeOperation<'a> {
    key: super::elaborate::OperationKey,
    leaf: &'a crate::interchange::finite_leaf::CheckedUnitaryLeaf,
}
impl Lower<'_> {
    fn native_operation(
        &mut self,
        leaf: &crate::interchange::finite_leaf::CheckedUnitaryLeaf,
    ) -> Result<usize> {
        fn source_basis(basis: &BasisType) -> SourceType {
            match basis {
                BasisType::Unit => SourceType::unit(),
                BasisType::Bit => SourceType::bit(),
                BasisType::Bits(width) => SourceType::bits(*width),
                BasisType::Pair(a, b) => SourceType::pair(source_basis(a), source_basis(b)),
                BasisType::Tuple(fields) => {
                    SourceType::tuple(fields.iter().map(source_basis).collect())
                }
            }
        }
        // The native finite gate already bounds the signature tree. Retain its
        // exact fields/association; physical width does not determine the type.
        let basis = source_basis(leaf.boundary().signature());
        let kind = match basis.kind() {
            "unit" => PortKind::Unit,
            "bit" => PortKind::Bit,
            "bits" => PortKind::Bits,
            "tuple" => PortKind::Tuple,
            _ => unreachable!("native exact Unit/Bit/Bits/product signature"),
        };
        let port = |p: &QuantumPort| Port {
            owner: p.token.0,
            kind,
            basis: basis.clone(),
            axes: p.wires.iter().map(|wire| wire.0).collect(),
        };
        let before = vec![port(leaf.boundary().input())];
        let after = vec![port(leaf.boundary().output())];
        let program = std::str::from_utf8(leaf.payload())
            .map_err(|_| fail("checked provider payload is not UTF-8"))?;
        let description =
            interchange::finite_matrix::encode(leaf.meaning()).map_err(|e| fail(e.to_string()))?;
        let description = std::str::from_utf8(&description)
            .map_err(|_| fail("checked provider matrix is not UTF-8"))?;
        // Actual immutable bytes, not a reconstructed provider or success flag.
        // The hierarchy's native gate checks this finite node again.
        let node = self.graph.add(
            before.clone(),
            after.clone(),
            tagged("leaf", &[("program", quote(program))]),
            tagged("finite", &[("description", quote(description))]),
            "finite",
            vec![],
        )?;
        let rename = self.graph.rename(after, before)?;
        self.graph.sequence(vec![node, rename])
    }
    fn fresh(&mut self, ty: &SourceType, axes: Vec<u32>) -> Result<Port> {
        let basis = ty
            .quantum_basis()
            .ok_or_else(|| fail("quantum port requires a quantum source type"))?;
        self.fresh_basis(basis, axes)
    }
    fn fresh_basis(&mut self, basis: &SourceType, axes: Vec<u32>) -> Result<Port> {
        if basis.storage_size(4096, 64).is_none()
            || axes.len() > 8
            || basis.basis_width() != Some(axes.len() as u32)
        {
            return Err(limit("quantum port exceeds exact type/width capacity"));
        }
        let kind = match basis.kind() {
            "unit" => PortKind::Unit,
            "bit" => PortKind::Bit,
            "bits" => PortKind::Bits,
            "tuple" => PortKind::Tuple,
            _ => return Err(fail("invalid quantum basis")),
        };
        self.owner = self
            .owner
            .checked_add(1)
            .ok_or_else(|| limit("owner identities exhausted"))?;
        Ok(Port {
            owner: self.owner,
            kind,
            basis: basis.clone(),
            axes,
        })
    }
    fn input_ports(&mut self, definition: &SourceDefinition) -> Result<Vec<Port>> {
        let mut ports = vec![];
        let mut next = 0u32;
        for value in definition.inputs() {
            for leaf in leaves(value) {
                if !leaf.ty().is_quantum() {
                    return Err(fail("classical entry values are unsupported"));
                }
                let width = leaf.ty().width().unwrap();
                let end = next
                    .checked_add(width)
                    .ok_or_else(|| limit("axis range overflow"))?;
                if width > 8 || end > 16 {
                    return Err(limit("entry exceeds selected quantum width capacity"));
                }
                ports.push(self.fresh(leaf.ty(), (next..end).collect())?);
                next = end;
            }
        }
        validate(&ports)?;
        Ok(ports)
    }
    fn gate_present(&mut self, id: usize) -> bool {
        if let Some(answer) = self.gate_cache.get(&id) {
            return *answer;
        }
        let mut found = false;
        for step in self.source.definitions()[id].steps() {
            found |= if let Some(name) = step.primitive_kind() {
                match name {
                    Primitive::H
                    | Primitive::X
                    | Primitive::Phase
                    | Primitive::PhaseEighth
                    | Primitive::Cnot
                    | Primitive::ControlledPhase => true,
                    Primitive::Unit
                    | Primitive::Split
                    | Primitive::Join
                    | Primitive::Finish
                    | Primitive::Init0
                    | Primitive::MeasureZ
                    | Primitive::TakeBit
                    | Primitive::PutBit
                    | Primitive::Empty
                    | Primitive::ConsumeEmpty
                    | Primitive::EmptyBits
                    | Primitive::PrependBit => false,
                }
            } else if let Some(child) = step.called_definition() {
                self.gate_present(child)
            } else {
                true
            };
        }
        self.gate_cache.insert(id, found);
        found
    }
    fn pure_definition(&mut self, id: usize) -> Result<usize> {
        if let Some(root) = self.pure.get(&id) {
            return Ok(*root);
        }
        let definition = self.source.definitions()[id].clone();
        if definition.effect() != "unitary" {
            return Err(fail("pure proposal requires a unitary source definition"));
        }
        let inputs = self.input_ports(&definition)?;
        let mut values = BTreeMap::new();
        let mut offset = 0;
        for input in definition.inputs() {
            let n = leaves(input).len();
            bind(
                input,
                inputs[offset..offset + n]
                    .iter()
                    .cloned()
                    .map(Item::Quantum)
                    .collect(),
                &mut values,
            )?;
            offset += n;
        }
        let mut children = vec![];
        for step in definition.steps() {
            let items = consume(step.inputs(), &mut values)?;
            if items.iter().any(|i| matches!(i, Item::Classical(_))) {
                return Err(fail("pure proposal has classical operands"));
            }
            let (node, output) = self.pure_step(step, quantum(&items))?;
            children.push(node);
            bind(
                step.output(),
                output.into_iter().map(Item::Quantum).collect(),
                &mut values,
            )?;
        }
        let result = read(definition.output(), &values)?;
        if result.iter().any(|i| matches!(i, Item::Classical(_))) {
            return Err(fail("pure proposal has classical results"));
        }
        let root = self.graph.frame(inputs, &children, quantum(&result))?;
        self.pure.insert(id, root);
        Ok(root)
    }
    fn output_ports(&mut self, value: &SourceValue, groups: Vec<Vec<u32>>) -> Result<Vec<Port>> {
        let ls = leaves(value);
        if ls.len() != groups.len() {
            return Err(fail("source output quantum grouping differs"));
        }
        ls.into_iter()
            .zip(groups)
            .map(|(v, axes)| self.fresh(v.ty(), axes))
            .collect()
    }
    fn gate(&mut self, gate: SingleGate, input: &Port, output: &Port) -> Result<usize> {
        let key = u8::from(gate == SingleGate::X);
        let child = *self
            .finite_gates
            .get(&key)
            .ok_or_else(|| fail("missing finite primitive proposal"))?;
        let before = self.graph.nodes[child].before.clone();
        let after = self.graph.nodes[child].after.clone();
        let a = self.graph.rename(vec![input.clone()], before)?;
        let b = self.graph.rename(after, vec![output.clone()])?;
        self.graph.sequence(vec![a, child, b])
    }
    fn finite_gate(&mut self, gate: SingleGate, input: &Port, output: &Port) -> Result<usize> {
        let raw = RawProgram {
            quantum_inputs: vec![QuantumPort {
                token: TokenId(input.owner),
                wires: input.axes.iter().copied().map(WireId).collect(),
                shape: BasisShape::BIT,
            }],
            classical_inputs: vec![],
            operations: vec![RawOp::Gate {
                gate,
                input: TokenId(input.owner),
                output: TokenId(output.owner),
            }],
            quantum_outputs: vec![TokenId(output.owner)],
            classical_outputs: vec![],
            declared_effect: Effect::Unitary,
        };
        let program = interchange::native::Proposal::from_raw(
            &raw,
            Some(&RootInterface {
                input: BasisType::Bit,
                output: BasisType::Bit,
            }),
            Version::V2,
            None,
        )
        .map_err(|e| fail(e.to_string()))?
        .artifact()
        .to_vec();
        let entries = if gate == SingleGate::H {
            [1, 1, 1, -1]
                .into_iter()
                .map(|n| Exact::new([0, n, 0, 0], 1))
                .collect::<std::result::Result<Vec<_>, _>>()
        } else {
            [0, 1, 1, 0]
                .into_iter()
                .map(|n| Exact::new([n, 0, 0, 0], 0))
                .collect()
        }
        .map_err(|e| fail(e.to_string()))?;
        let matrix = Matrix::new(2, 2, entries).map_err(|e| fail(e.to_string()))?;
        let description =
            interchange::finite_matrix::encode(&matrix).map_err(|e| fail(e.to_string()))?;
        let program =
            String::from_utf8(program).map_err(|_| fail("finite program is not UTF-8"))?;
        let description =
            String::from_utf8(description).map_err(|_| fail("finite description is not UTF-8"))?;
        self.graph.add(
            vec![input.clone()],
            vec![output.clone()],
            tagged("leaf", &[("program", quote(&program))]),
            tagged("finite", &[("description", quote(&description))]),
            "finite",
            vec![],
        )
    }
    /// A closed scalar with no boundary owners, built from existing checked
    /// structural and finite nodes. Its internal Unit owner is still explicit;
    /// an empty physical coordinate list never erases its exact phase.
    fn closed_scalar(&mut self) -> Result<usize> {
        let input = self.fresh_basis(&SourceType::unit(), vec![])?;
        let output = self.fresh_basis(&SourceType::unit(), vec![])?;
        let pack = self
            .graph
            .structural(vec![], vec![input.clone()], "pack_unit", &[])?;
        let raw = RawProgram {
            quantum_inputs: vec![QuantumPort {
                token: TokenId(input.owner),
                wires: vec![],
                shape: BasisShape::UNIT,
            }],
            classical_inputs: vec![],
            operations: vec![RawOp::ApplyUnitary {
                input: TokenId(input.owner),
                output: TokenId(output.owner),
                steps: vec![CircuitStep {
                    controls: vec![],
                    action: CircuitAction::Monomial {
                        indices: vec![],
                        permutation: vec![0],
                        phases: vec![1],
                    },
                }],
            }],
            quantum_outputs: vec![TokenId(output.owner)],
            classical_outputs: vec![],
            declared_effect: Effect::Unitary,
        };
        let proposal = interchange::native::Proposal::from_raw(
            &raw,
            Some(&RootInterface {
                input: BasisType::Unit,
                output: BasisType::Unit,
            }),
            Version::V2,
            None,
        )
        .map_err(|e| fail(e.to_string()))?;
        let program = std::str::from_utf8(proposal.artifact())
            .map_err(|_| fail("finite scalar program is not UTF-8"))?;
        let matrix = Matrix::new(1, 1, vec![Exact::phase(1)]).map_err(|e| fail(e.to_string()))?;
        let description =
            interchange::finite_matrix::encode(&matrix).map_err(|e| fail(e.to_string()))?;
        let description = std::str::from_utf8(&description)
            .map_err(|_| fail("finite scalar description is not UTF-8"))?;
        let leaf = self.graph.add(
            vec![input],
            vec![output.clone()],
            tagged("leaf", &[("program", quote(program))]),
            tagged("finite", &[("description", quote(description))]),
            "finite",
            vec![],
        )?;
        let unpack = self
            .graph
            .structural(vec![output], vec![], "unpack_unit", &[])?;
        self.graph.sequence(vec![pack, leaf, unpack])
    }
    fn closed_gate(&mut self, gate: SingleGate, p: &Port) -> Result<usize> {
        self.owner = self
            .owner
            .checked_add(1)
            .ok_or_else(|| limit("owner identities exhausted"))?;
        let out = Port {
            owner: self.owner,
            ..p.clone()
        };
        let leaf = self.gate(gate, p, &out)?;
        let rename = self.graph.rename(vec![out], vec![p.clone()])?;
        self.graph.sequence(vec![leaf, rename])
    }
    fn phase(&mut self, p: &Port, ns: &[u32]) -> Result<usize> {
        self.graph.add(
            vec![p.clone()],
            vec![p.clone()],
            tagged(
                "dyadic_phase",
                &[
                    ("target", p.owner.to_string()),
                    ("j", ns[0].to_string()),
                    ("k", ns[1].to_string()),
                ],
            ),
            tagged(
                "phase",
                &[("j", ns[0].to_string()), ("k", ns[1].to_string())],
            ),
            "phase",
            vec![],
        )
    }
    fn control(&mut self, before: Vec<Port>, child: usize) -> Result<usize> {
        self.graph.add(
            before.clone(),
            before,
            tagged(
                "control",
                &[
                    ("definition", child.to_string()),
                    ("polarity", "true".into()),
                ],
            ),
            tagged(
                "control",
                &[("child", child.to_string()), ("polarity", "true".into())],
            ),
            "control",
            vec![child],
        )
    }
    fn operation(&mut self, op: &SourceOperation) -> Result<usize> {
        let key = op.key();
        if let Some(native) = self.native_operations.iter().find(|entry| entry.key == key) {
            return self.native_operation(native.leaf);
        }
        if let Some(id) = op.definition() {
            let child = self.pure_definition(id)?;
            let before = self.graph.nodes[child].before.clone();
            let after = self.graph.nodes[child].after.clone();
            let enter = self.graph.identity(before.clone())?;
            let rename = self.graph.rename(after, before)?;
            let closed = self.graph.sequence(vec![enter, child, rename])?;
            self.factor_fourier(closed)
        } else {
            let child = self.operation(op.child().ok_or_else(|| fail("missing repeat child"))?)?;
            let count = op
                .repeat_count()
                .ok_or_else(|| fail("missing repeat count"))?;
            let ports = self.graph.nodes[child].before.clone();
            self.graph.add(
                ports.clone(),
                ports,
                tagged(
                    "repeat",
                    &[
                        ("definition", child.to_string()),
                        ("count", count.to_string()),
                    ],
                ),
                tagged(
                    "power",
                    &[("child", child.to_string()), ("count", count.to_string())],
                ),
                "repeat",
                vec![child],
            )
        }
    }
    fn pure_step(&mut self, step: &SourceStep, before: Vec<Port>) -> Result<(usize, Vec<Port>)> {
        if let Some(id) = step.called_definition() {
            let child = self.pure_definition(id)?;
            let first = self.graph.nodes[child].before.clone();
            let last = self.graph.nodes[child].after.clone();
            let map: BTreeMap<_, _> = axes(&first).into_iter().zip(axes(&before)).collect();
            let groups = last
                .iter()
                .map(|p| {
                    p.axes
                        .iter()
                        .map(|a| {
                            map.get(a)
                                .copied()
                                .ok_or_else(|| fail("pure call introduced an axis"))
                        })
                        .collect::<Result<Vec<_>>>()
                })
                .collect::<Result<Vec<_>>>()?;
            let after = self.output_ports(step.output(), groups)?;
            let a = self.graph.rename(before, first)?;
            let b = self.graph.rename(last, after.clone())?;
            return Ok((self.graph.sequence(vec![a, child, b])?, after));
        }
        if let Some(op) = step.operation() {
            let mut child = self.operation(op)?;
            if step.kind() == "adjoint" {
                let ports = self.graph.nodes[child].before.clone();
                child = self.graph.add(
                    ports.clone(),
                    ports,
                    tagged("inverse", &[("definition", child.to_string())]),
                    tagged("inverse", &[("child", child.to_string())]),
                    "inverse",
                    vec![child],
                )?;
            }
            let target = if step.kind() == "controlled" {
                before[1..].to_vec()
            } else {
                before.clone()
            };
            let canonical = self.graph.nodes[child].before.clone();
            let a = self.graph.rename(target.clone(), canonical.clone())?;
            let after = self.output_ports(
                step.output(),
                before.iter().map(|p| p.axes.clone()).collect(),
            )?;
            if step.kind() != "controlled" {
                // The operation is closed at its canonical frame. Return
                // directly to the checked source's actual result ports rather
                // than routing through the consumed argument owners first.
                let b = self.graph.rename(canonical, after.clone())?;
                return Ok((self.graph.sequence(vec![a, child, b])?, after));
            }
            let b = self.graph.rename(canonical, target.clone())?;
            child = self.graph.sequence(vec![a, child, b])?;
            let node = self.control(before.clone(), child)?;
            let rename = self.graph.rename(before, after.clone())?;
            return Ok((self.graph.sequence(vec![node, rename])?, after));
        }
        let name = step
            .primitive_kind()
            .ok_or_else(|| fail("unsupported source step"))?;
        let ns = step.natural_arguments();
        match name {
            Primitive::Split => {
                if before.len() != 1 || !ns.is_empty() {
                    return Err(fail("split has invalid source arity"));
                }
                let fields = before[0]
                    .basis
                    .tuple_fields()
                    .filter(|fields| fields.len() == 2)
                    .ok_or_else(|| fail("split requires an exact binary basis"))?;
                let width = fields[0]
                    .basis_width()
                    .ok_or_else(|| fail("invalid split basis"))?
                    as usize;
                let after = self.output_ports(
                    step.output(),
                    vec![
                        before[0].axes[..width].to_vec(),
                        before[0].axes[width..].to_vec(),
                    ],
                )?;
                let node = self
                    .graph
                    .structural(before, after.clone(), "split_tuple", &[])?;
                Ok((node, after))
            }
            Primitive::Join => {
                if before.len() != 2 || !ns.is_empty() {
                    return Err(fail("join has invalid source arity"));
                }
                let wires = axes(&before);
                let after = self.output_ports(step.output(), vec![wires])?;
                let node = self
                    .graph
                    .structural(before, after.clone(), "join_tuple", &[])?;
                Ok((node, after))
            }
            Primitive::TakeBit => {
                let mut rest = before[0].axes.clone();
                let bit = rest.remove(ns[1] as usize);
                let after = self.output_ports(step.output(), vec![vec![bit], rest])?;
                let node = self
                    .graph
                    .structural(before, after.clone(), "take_bit", ns)?;
                Ok((node, after))
            }
            Primitive::PutBit => {
                let mut wires = before[1].axes.clone();
                wires.insert(ns[1] as usize, before[0].axes[0]);
                let after = self.output_ports(step.output(), vec![wires])?;
                let node = self
                    .graph
                    .structural(before, after.clone(), "put_bit", ns)?;
                Ok((node, after))
            }
            Primitive::Unit | Primitive::Empty => {
                let after = self.output_ports(step.output(), vec![vec![]])?;
                let operation = if name == Primitive::Unit {
                    "pack_unit"
                } else {
                    "pack_empty_bits"
                };
                let node = self
                    .graph
                    .structural(before, after.clone(), operation, &[])?;
                Ok((node, after))
            }
            Primitive::Finish | Primitive::ConsumeEmpty => {
                let operation = if name == Primitive::Finish {
                    "unpack_unit"
                } else {
                    "unpack_empty_bits"
                };
                let node = self.graph.structural(before, vec![], operation, &[])?;
                Ok((node, vec![]))
            }
            Primitive::H | Primitive::X => {
                let after = self.output_ports(step.output(), vec![before[0].axes.clone()])?;
                // Bind the exact finite program to these actual source ports.
                // Canonical leaf adapters add owner routes and an extra
                // composition without changing the primitive's meaning.
                let node = self.finite_gate(
                    if name == Primitive::H {
                        SingleGate::H
                    } else {
                        SingleGate::X
                    },
                    &before[0],
                    &after[0],
                )?;
                Ok((node, after))
            }
            Primitive::PhaseEighth => {
                if before.len() != 1 || !ns.is_empty() {
                    return Err(fail(
                        "scalar phase requires one quantum atom and no static arguments",
                    ));
                }
                let after = self.output_ports(step.output(), vec![before[0].axes.clone()])?;
                // Keep the source atom's exact basis and owner separately from
                // the fresh internal zero-axis Unit owner of the scalar.
                let identity = self.graph.identity(before.clone())?;
                let scalar = self.closed_scalar()?;
                let action = self.graph.tensor(identity, scalar)?;
                let rename = self.graph.rename(before, after.clone())?;
                Ok((self.graph.sequence(vec![action, rename])?, after))
            }
            Primitive::Phase | Primitive::ControlledPhase | Primitive::Cnot => {
                let controlled = name != Primitive::Phase;
                let target = &before[usize::from(controlled)];
                let child = if name == Primitive::Cnot {
                    self.closed_gate(SingleGate::X, target)?
                } else {
                    self.phase(target, ns)?
                };
                let node = if controlled {
                    self.control(before.clone(), child)?
                } else {
                    child
                };
                let after = self.output_ports(
                    step.output(),
                    before.iter().map(|p| p.axes.clone()).collect(),
                )?;
                let rename = self.graph.rename(before, after.clone())?;
                Ok((self.graph.sequence(vec![node, rename])?, after))
            }
            Primitive::Init0
            | Primitive::MeasureZ
            | Primitive::EmptyBits
            | Primitive::PrependBit => {
                Err(fail("non-pure or unsupported primitive in pure proposal"))
            }
        }
    }
}

struct Instrument {
    inputs: Vec<Port>,
    fresh: Vec<Port>,
    initializations: Vec<String>,
    pure_steps: Vec<usize>,
    measured: Vec<(Port, u32)>,
    next_axis: u32,
    next_classical: u32,
    current: Vec<Port>,
    events: Vec<SourceEvent>,
    call_path: Vec<usize>,
    trace_cells: usize,
}
impl Lower<'_> {
    fn invoke(
        &mut self,
        id: usize,
        arguments: Vec<Item>,
        instrument: &mut Instrument,
        depth: usize,
    ) -> Result<Vec<Item>> {
        self.inline_visits += 1;
        if self.inline_visits > 1024 || depth > 16 {
            return Err(limit("observing proposal inline-call limit exceeded"));
        }
        let definition = self.source.definitions()[id].clone();
        let mut values = BTreeMap::new();
        let mut offset = 0;
        for input in definition.inputs() {
            let n = leaves(input).len();
            let end = offset + n;
            if end > arguments.len() {
                return Err(fail("effectful argument shape mismatch"));
            }
            bind(input, arguments[offset..end].to_vec(), &mut values)?;
            offset = end;
        }
        if offset != arguments.len() {
            return Err(fail("effectful argument arity mismatch"));
        }
        for (step_index, step) in definition.steps().iter().enumerate() {
            let items = consume(step.inputs(), &mut values)?;
            let recorded_items = items.clone();
            let mut node = None;
            let mut inlined = false;
            let output = if let Some(child) = step.called_definition() {
                if self.source.definitions()[child].effect() != "unitary"
                    || !self.gate_present(child)
                {
                    inlined = true;
                    instrument.call_path.push(step_index);
                    let output = self.invoke(child, items, instrument, depth + 1);
                    instrument.call_path.pop();
                    output?
                } else {
                    let (output, reference) = self.instrument_pure_step(step, items, instrument)?;
                    node = Some(reference);
                    output
                }
            } else {
                match step.primitive_kind() {
                    Some(Primitive::Init0) => {
                        if !instrument.measured.is_empty() {
                            return Err(Error::new(
                                "unsupported",
                                step.span(),
                                "initialization after observation requires a preservation proof",
                            )
                            .in_module(step.module()));
                        }
                        if instrument.next_axis >= 16 {
                            return Err(limit("instrument exceeds 16 allocated axes"));
                        }
                        let p =
                            self.fresh(leaves(step.output())[0].ty(), vec![instrument.next_axis])?;
                        instrument.next_axis += 1;
                        let before = [instrument.inputs.clone(), instrument.fresh.clone()].concat();
                        let after = [before.clone(), vec![p.clone()]].concat();
                        instrument.initializations.push(object(&[
                            ("interface", header(&before, &after)),
                            ("effect", quote("iso")),
                            ("body", tagged("init0", &[("output", p.owner.to_string())])),
                        ]));
                        instrument.fresh.push(p.clone());
                        vec![Item::Quantum(p)]
                    }
                    Some(Primitive::MeasureZ) => {
                        let Item::Quantum(p) = &items[0] else {
                            return Err(fail("measure operand is not quantum"));
                        };
                        instrument.next_classical += 1;
                        instrument
                            .measured
                            .push((p.clone(), instrument.next_classical));
                        vec![Item::Classical(vec![instrument.next_classical])]
                    }
                    Some(Primitive::EmptyBits) => vec![Item::Classical(vec![])],
                    Some(Primitive::PrependBit) => {
                        let (Item::Classical(first), Item::Classical(rest)) =
                            (&items[0], &items[1])
                        else {
                            return Err(fail("classical packing operands differ"));
                        };
                        vec![Item::Classical([first.clone(), rest.clone()].concat())]
                    }
                    Some(
                        Primitive::Unit
                        | Primitive::Split
                        | Primitive::Join
                        | Primitive::Finish
                        | Primitive::H
                        | Primitive::X
                        | Primitive::Cnot
                        | Primitive::Phase
                        | Primitive::PhaseEighth
                        | Primitive::ControlledPhase
                        | Primitive::TakeBit
                        | Primitive::PutBit
                        | Primitive::Empty
                        | Primitive::ConsumeEmpty,
                    )
                    | None => {
                        let (output, reference) =
                            self.instrument_pure_step(step, items, instrument)?;
                        node = Some(reference);
                        output
                    }
                }
            };
            if !inlined {
                preservation::record(
                    instrument,
                    id,
                    step_index,
                    step,
                    recorded_items,
                    output.clone(),
                    node,
                )?;
            }
            bind(step.output(), output, &mut values)?;
        }
        read(definition.output(), &values)
    }
    fn instrument_pure_step(
        &mut self,
        step: &SourceStep,
        items: Vec<Item>,
        instrument: &mut Instrument,
    ) -> Result<(Vec<Item>, usize)> {
        let structural = step.primitive_kind().is_some_and(|name| match name {
            Primitive::Unit
            | Primitive::Split
            | Primitive::Join
            | Primitive::Finish
            | Primitive::TakeBit
            | Primitive::PutBit
            | Primitive::Empty
            | Primitive::ConsumeEmpty => true,
            Primitive::H
            | Primitive::X
            | Primitive::Cnot
            | Primitive::Phase
            | Primitive::PhaseEighth
            | Primitive::ControlledPhase
            | Primitive::Init0
            | Primitive::MeasureZ
            | Primitive::EmptyBits
            | Primitive::PrependBit => false,
        });
        if !structural && !instrument.measured.is_empty() {
            return Err(Error::new(
                "unsupported",
                step.span(),
                "quantum gate after observation requires a preservation proof",
            )
            .in_module(step.module()));
        }
        if items.iter().any(|i| matches!(i, Item::Classical(_))) {
            return Err(fail("quantum proposal contains classical operands"));
        }
        let (node, output) = self.pure_step(step, quantum(&items))?;
        instrument.pure_steps.push(node);
        Ok((output.into_iter().map(Item::Quantum).collect(), node))
    }
}

/// Preserve the existing preflight error API using the same typed classification
/// used by target selection. Internal/limit failures are never reclassified.
pub(super) fn check_profile(source: &ElaboratedProgram) -> Result<()> {
    match hierarchy_eligibility(source)? {
        HierarchyEligibility::Eligible => Ok(()),
        HierarchyEligibility::Ineligible(error) => Err(error),
    }
}

/// Classify only explicit profile mismatches without narrowing generic source
/// typing. Body lowering still checks each operation and concrete capability.
pub(super) fn hierarchy_eligibility(source: &ElaboratedProgram) -> Result<HierarchyEligibility> {
    let root = &source.definitions()[source.root()];
    let unsupported = |message: &str| {
        Error::new("unsupported", root.span(), message).in_module(
            root.path()
                .rsplit_once("::")
                .map_or(root.path(), |(module, _)| module),
        )
    };
    if root
        .inputs()
        .iter()
        .flat_map(leaves)
        .any(|input| !input.ty().is_quantum())
    {
        return Ok(HierarchyEligibility::Ineligible(unsupported(
            "selected sized lowering profile requires quantum entry values; classical entry values are unsupported",
        )));
    }
    if root.effect() == "iso" {
        let classical: Vec<_> = leaves(root.output())
            .into_iter()
            .filter(|output| !output.ty().is_quantum())
            .collect();
        if !classical.is_empty()
            && (classical.len() != 1
                || classical[0].ty().kind() != "bits"
                || classical[0].ty().width() != Some(0))
        {
            return Ok(HierarchyEligibility::Ineligible(unsupported(
                "selected isometry lowering requires quantum results with at most one ordinary Bits<0> result",
            )));
        }
    }
    if root.effect() == "unitary"
        && leaves(root.output())
            .iter()
            .any(|output| !output.ty().is_quantum())
    {
        return Ok(HierarchyEligibility::Ineligible(unsupported(
            "selected sized lowering profile requires quantum results from unitary roots; classical results are unsupported",
        )));
    }
    if root.effect() == "observe" {
        let classical: Vec<_> = leaves(root.output())
            .into_iter()
            .filter(|output| !output.ty().is_quantum())
            .collect();
        if classical.len() != 1 || classical[0].ty().kind() != "bits" {
            return Ok(HierarchyEligibility::Ineligible(unsupported(
                "selected sized lowering profile requires an observe root returning exactly one Bits value",
            )));
        }
    }
    for definition in source.definitions() {
        for step in definition.steps() {
            if step.boolean().is_some() {
                return Ok(HierarchyEligibility::Ineligible(Error::new(
                    "unsupported",
                    step.span(),
                    "hierarchical transport does not support ordinary Boolean source steps; select an explicitly supported finite target",
                ).in_module(step.module())));
            }
        }
    }
    Ok(HierarchyEligibility::Eligible)
}

pub(super) fn lower(source: &ElaboratedProgram) -> Result<HierarchyProposal> {
    source.require_unrefined()?;
    lower_inner(source, &[])
}

pub(super) fn lower_with_checked_operation(
    check: &super::SourceMeaningCheck<'_>,
) -> Result<HierarchyProposal> {
    let proposal = check.source();
    proposal.source().require_unrefined()?;
    let op = proposal
        .operation()
        .ok_or_else(|| fail("hierarchy binding requires an original source operation binding"))?;
    let operations = [NativeOperation {
        key: op.key(),
        leaf: check.leaf(),
    }];
    lower_inner(proposal.source(), &operations)
}

pub(super) fn lower_with_checked_meanings(
    check: &super::CheckedSourceMeanings<'_>,
) -> Result<HierarchyProposal> {
    let operations = check
        .leaves
        .iter()
        .map(|(key, leaf)| NativeOperation {
            key: key.clone(),
            leaf,
        })
        .collect::<Vec<_>>();
    lower_inner(check.source(), &operations)
}

fn lower_inner<'a>(
    source: &'a ElaboratedProgram,
    native_operations: &'a [NativeOperation<'a>],
) -> Result<HierarchyProposal> {
    check_profile(source)?;
    let mut lower = Lower {
        source,
        native_operations,
        graph: Graph::new(),
        owner: 100,
        pure: BTreeMap::new(),
        gate_cache: BTreeMap::new(),
        finite_gates: BTreeMap::new(),
        inline_visits: 0,
    };
    // Shared primitive proposals precede composite definitions. This is transport
    // sharing only: source steps, finite bytes and every reconstruction remain.
    for (name, gate, key) in [
        (Primitive::H, SingleGate::H, 0),
        (Primitive::X, SingleGate::X, 1),
    ] {
        let needed = source
            .definitions()
            .iter()
            .flat_map(|d| d.steps())
            .any(|s| {
                s.primitive_kind() == Some(name)
                    || (key == 1 && s.primitive_kind() == Some(Primitive::Cnot))
            });
        if needed {
            let input = Port {
                owner: 1,
                kind: PortKind::Bit,
                basis: SourceType::bit(),
                axes: vec![0],
            };
            let output = Port {
                owner: 2,
                kind: PortKind::Bit,
                basis: SourceType::bit(),
                axes: vec![0],
            };
            let child = lower.finite_gate(gate, &input, &output)?;
            lower.finite_gates.insert(key, child);
        }
    }
    let root = &source.definitions()[source.root()];
    let mut events = vec![];
    let precursor;
    let (payload, comparison, graph, instrument) = if root.effect() == "unitary" {
        let id = lower.pure_definition(source.root())?;
        let id = lower.factor_fourier(id)?;
        precursor = lower.graph.artifact(id);
        let (compact, id, _) = lower.graph.compact_export(id)?;
        let graph = compact.artifact(id);
        (graph.clone(), compact.comparison(id), graph, false)
    } else {
        let inputs = lower.input_ports(root)?;
        let mut state = Instrument {
            next_axis: axes(&inputs).len() as u32,
            inputs: inputs.clone(),
            fresh: vec![],
            initializations: vec![],
            pure_steps: vec![],
            measured: vec![],
            next_classical: 1_000_000,
            current: inputs.clone(),
            events: vec![],
            call_path: vec![],
            trace_cells: 0,
        };
        let returned = lower.invoke(
            source.root(),
            inputs.iter().cloned().map(Item::Quantum).collect(),
            &mut state,
            0,
        )?;
        let classical: Vec<_> = returned
            .iter()
            .filter_map(|i| match i {
                Item::Classical(bits) => Some(bits.clone()),
                _ => None,
            })
            .collect();
        let output_classical_types: Vec<_> = leaves(root.output())
            .into_iter()
            .filter(|v| !v.ty().is_quantum())
            .collect();
        let isometry = root.effect() == "iso";
        if isometry {
            if !state.measured.is_empty()
                || (!classical.is_empty() && classical != [Vec::<u32>::new()])
            {
                return Err(fail(
                    "isometry source cannot contain observation or a nonempty classical result",
                ));
            }
        } else if classical.len() != 1 || output_classical_types[0].ty().kind() != "bits" {
            return Err(fail("instrument root must return exactly one Bits value"));
        }
        // The native readout carrier has one empty outcome when no axis is
        // measured. It does not add a source Observe effect or a quantum action.
        let empty_outcome = Vec::new();
        let pack = classical.first().unwrap_or(&empty_outcome);
        let measurement_values: Vec<_> = state.measured.iter().map(|(_, id)| *id).collect();
        if pack != &measurement_values {
            return Err(fail(
                "instrument result must retain every observation in chronological low-bit-first order",
            ));
        }
        let desired = [
            state
                .measured
                .iter()
                .map(|(p, _)| p.clone())
                .collect::<Vec<_>>(),
            quantum(&returned),
        ]
        .concat();
        let preparation_outputs = [inputs.clone(), state.fresh.clone()].concat();
        let pure = lower.graph.frame(
            preparation_outputs.clone(),
            &state.pure_steps,
            desired.clone(),
        )?;
        precursor = lower.graph.artifact(pure);
        let (compact, pure, map) = lower.graph.compact_export(pure)?;
        preservation::remap_events(&mut state.events, &map)?;
        let graph = compact.artifact(pure);
        let pure_request = compact.comparison(pure);
        let readout_inputs = side(&desired, &[]);
        let mut current = desired;
        let mut classical_ports = vec![];
        let mut measurements = vec![];
        for (port, id) in &state.measured {
            let before = side(&current, &classical_ports);
            current.retain(|p| p.owner != port.owner);
            classical_ports.push((*id, true, 1));
            let after = side(&current, &classical_ports);
            measurements.push(object(&[
                (
                    "interface",
                    object(&[("inputs", before), ("outputs", after)]),
                ),
                ("effect", quote("observe")),
                (
                    "body",
                    tagged(
                        "observe_z",
                        &[
                            ("input", port.owner.to_string()),
                            ("output", id.to_string()),
                        ],
                    ),
                ),
            ]));
        }
        let result = state
            .next_classical
            .checked_add(1)
            .ok_or_else(|| limit("classical identity overflow"))?;
        let outputs = side(&current, &[(result, false, pack.len())]);
        let prep = object(&[
            ("initializations", array(state.initializations)),
            ("outputs", side(&preparation_outputs, &[])),
        ]);
        let readout = object(&[
            ("measurements", array(measurements)),
            ("pack", numbers(pack.iter().map(|n| *n as usize))),
            ("outputs", outputs.clone()),
        ]);
        let payload = object(&[
            ("format", quote("qleisli.instrument-ir")),
            ("version", "1".into()),
            ("profile", quote("initialize-unitary-readout-v1")),
            ("preparation", prep),
            ("circuit", graph.clone()),
            ("readout", readout),
        ]);
        let comparison = object(&[
            ("format", quote("qleisli.instrument-request")),
            ("version", "1".into()),
            ("profile", quote("initialize-unitary-readout-v1")),
            (
                "preparation",
                object(&[
                    ("inputs", side(&inputs, &[])),
                    ("fresh", array(state.fresh.iter().map(Port::json))),
                ]),
            ),
            ("circuit", pure_request),
            (
                "readout",
                object(&[
                    ("inputs", readout_inputs),
                    (
                        "owners",
                        numbers(state.measured.iter().map(|(p, _)| p.owner as usize)),
                    ),
                    ("result", result.to_string()),
                ]),
            ),
            ("outputs", outputs),
        ]);
        events = state.events;
        (payload, comparison, graph, true)
    };
    if payload.len() > 16 << 20 || comparison.len() > 16 << 20 || precursor.len() > 16 << 20 {
        return Err(limit("serialized proposal exceeds 16 MiB"));
    }
    let moves = preservation::propose_moves(&events);
    let result = HierarchyProposal {
        source: source.clone(),
        payload: payload.into_bytes(),
        comparison: comparison.into_bytes(),
        graph: graph.into_bytes(),
        precursor: precursor.into_bytes(),
        instrument,
        events,
        moves,
    };
    if instrument {
        preservation::validate(&result)?;
    }
    Ok(result)
}
