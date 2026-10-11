//! Bounded QIRF1/2 transport. All imported evidence is reconstructed by the
//! ordinary finite checker; labels and embedded source text are never executed.
mod codec;
pub mod finite_leaf;
pub mod finite_matrix;
pub mod hierarchical;
pub(crate) mod json;
pub mod native;

use codec::Codec;
use json::Value;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use crate::AcceptedProgram;
use crate::contract::exact::Budget;
use crate::contract::function::RetainedIdentity;
use crate::contract::meaning::{FiniteMeaning, MeaningEvidence};
use crate::contract::{BasisType, ContractError, FunctionEvidence};
use crate::ir::{Effect, RawProgram};

const MAX_OBJECTS: usize = 65_536;
const MAX_NODES: usize = 1_000_000;
const MAX_SOURCE_BYTES: usize = 1 << 20;

/// A transport/verification failure, with an RFC 6901 pointer when available.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Error {
    pub code: &'static str,
    pub message: String,
    pub json_pointer: String,
}
impl Error {
    pub(crate) fn new(code: &'static str, message: impl Into<String>) -> Self {
        Self {
            code,
            message: message.into(),
            json_pointer: String::new(),
        }
    }
    fn format(message: impl Into<String>) -> Self {
        Self::new("format", message)
    }
    fn limit(message: impl Into<String>) -> Self {
        Self::new("limit", message)
    }
    fn at(mut self, pointer: impl Into<String>) -> Self {
        self.json_pointer = pointer.into();
        self
    }
}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.json_pointer.is_empty() {
            write!(f, "{}: {}", self.code, self.message)
        } else {
            write!(
                f,
                "{} at {}: {}",
                self.code, self.json_pointer, self.message
            )
        }
    }
}
impl std::error::Error for Error {}
type Result<T> = std::result::Result<T, Error>;

fn contract_error(e: ContractError) -> Error {
    let code = if e.is_capacity() { "limit" } else { "contract" };
    Error::new(code, e.to_string())
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Version {
    V1,
    V2,
}
impl Version {
    fn number(self) -> u64 {
        match self {
            Self::V1 => 1,
            Self::V2 => 2,
        }
    }
    fn profile(self) -> &'static str {
        match self {
            Self::V1 => "finite-v0",
            Self::V2 => "finite-meaning-v1",
        }
    }
}

/// Exact type trees retained by a producer. Width alone never reconstructs them.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RootInterface {
    pub input: BasisType,
    pub output: BasisType,
}

#[derive(Debug)]
pub struct Imported {
    pub program: AcceptedProgram,
    pub root_interface: Option<RootInterface>,
    pub request_checked: bool,
    /// Charged exact-kernel work, excluding tokenization and structural checks.
    pub exact_work: usize,
}

struct Decoder<'a> {
    evidence: &'a [Option<Arc<FunctionEvidence>>],
}
struct Encoder {
    version: Version,
    programs: Vec<Value>,
    entries: Vec<Value>,
    seen: BTreeMap<usize, usize>,
    canonical_evidence: BTreeMap<Arc<[u8]>, usize>,
    sources: Vec<(String, String)>,
    source_ids: BTreeMap<String, usize>,
    remaining: usize,
    meanings: BTreeMap<Arc<[u8]>, FiniteMeaning>,
    identity_remaining: usize,
    source_remaining: usize,
}
impl Encoder {
    fn new(version: Version) -> Self {
        Self {
            version,
            programs: vec![],
            entries: vec![],
            seen: BTreeMap::new(),
            canonical_evidence: BTreeMap::new(),
            sources: vec![],
            source_ids: BTreeMap::new(),
            remaining: MAX_NODES,
            meanings: BTreeMap::new(),
            identity_remaining: MAX_SOURCE_BYTES,
            source_remaining: MAX_SOURCE_BYTES,
        }
    }
    fn charge(&mut self, amount: usize) -> Result<()> {
        self.remaining = self
            .remaining
            .checked_sub(amount)
            .ok_or_else(|| Error::limit("export node budget exhausted"))?;
        Ok(())
    }
    fn object(&self) -> Result<()> {
        if self.programs.len() + self.entries.len() >= MAX_OBJECTS {
            return Err(Error::limit("too many program/evidence objects"));
        }
        Ok(())
    }
    fn program(&mut self, raw: &RawProgram) -> Result<usize> {
        proposal_depth(raw)?;
        self.object()?;
        let id = self.programs.len();
        self.programs.push(Value::Null);
        self.programs[id] = raw.write(self)?;
        Ok(id)
    }
    fn evidence(&mut self, receipt: &Arc<FunctionEvidence>) -> Result<usize> {
        let key = Arc::as_ptr(receipt) as usize;
        if let Some(&index) = self.seen.get(&key) {
            return Ok(index);
        }
        if let Some(&index) = self.canonical_evidence.get(receipt.snapshot_key()) {
            self.seen.insert(key, index);
            return Ok(index);
        }
        self.object()?;
        let id = self.entries.len();
        self.entries.push(Value::Null);
        self.seen.insert(key, id);
        self.canonical_evidence
            .insert(Arc::clone(receipt.snapshot_key()), id);
        let target = self.meanings.get(receipt.snapshot_key()).cloned();
        self.evidence_fields(
            id,
            receipt.signature(),
            receipt.implementation(),
            receipt.specification(),
            receipt.identity_parts(),
            target,
        )?;
        Ok(id)
    }

    fn evidence_fields(
        &mut self,
        id: usize,
        signature: &BasisType,
        raw_implementation: &RawProgram,
        raw_specification: &RawProgram,
        identity: (&str, &str, &[(String, String)]),
        target: Option<FiniteMeaning>,
    ) -> Result<()> {
        let implementation = self.program(raw_implementation)?;
        let specification = if target.is_none() {
            Some(self.program(raw_specification)?)
        } else {
            None
        };
        let (implementation_name, specification_name, snapshot) = identity;
        self.identity_remaining = self
            .identity_remaining
            .checked_sub(implementation_name.len() + specification_name.len())
            .ok_or_else(|| Error::limit("aggregate identity bytes exceed 1 MiB"))?;
        let mut sources = Vec::new();
        for (path, text) in snapshot {
            let index = if let Some(&index) = self.source_ids.get(path) {
                if self.sources[index].1 != *text {
                    return Err(Error::format("conflicting source snapshots for one label"));
                }
                index
            } else {
                self.identity_remaining = self
                    .identity_remaining
                    .checked_sub(path.len() + text.len())
                    .ok_or_else(|| Error::limit("aggregate identity bytes exceed 1 MiB"))?;
                if self.sources.len() >= 128 {
                    return Err(Error::limit("more than 128 sources"));
                }
                self.source_remaining = self
                    .source_remaining
                    .checked_sub(text.len())
                    .ok_or_else(|| Error::limit("embedded source text exceeds 1 MiB"))?;
                let index = self.sources.len();
                self.sources.push((path.clone(), text.clone()));
                self.source_ids.insert(path.clone(), index);
                index
            };
            sources.push(Value::Number(index as u64));
        }
        let mut fields = vec![
            ("signature", signature.write(self)?),
            ("implementation", Value::Number(implementation as u64)),
            (
                "identity",
                Value::object([
                    ("implementation", Value::String(implementation_name.into())),
                    ("specification", Value::String(specification_name.into())),
                    ("sources", Value::Array(sources)),
                ]),
            ),
        ];
        if let Some(target) = target {
            fields.push(("meaning", meaning_value(&target)));
        } else {
            fields.push((
                "specification",
                Value::Number(specification.expect("circuit target") as u64),
            ));
        }
        if self.version == Version::V2 {
            fields.push((
                "tag",
                Value::String(
                    if specification.is_some() {
                        "circuit"
                    } else {
                        "meaning"
                    }
                    .into(),
                ),
            ));
        }
        self.entries[id] = Value::object(fields);
        Ok(())
    }
}

fn source_values(sources: &[(String, String)]) -> Value {
    Value::Array(
        sources
            .iter()
            .map(|(path, text)| {
                Value::object([
                    ("path", Value::String(path.clone())),
                    ("text", Value::String(text.clone())),
                ])
            })
            .collect(),
    )
}

/// Export finite evidence as circuit entries. The retained canonical target IR
/// of a MeaningEvidence receipt is checked in exactly the same way as any IR.
/// No meaning tag is inferred from names, hashes or a numerical matrix.
pub fn export(
    program: &AcceptedProgram,
    interface: Option<&RootInterface>,
    version: Version,
) -> Result<Vec<u8>> {
    export_inner(program, interface, Encoder::new(version))
}

/// Retain explicitly supplied mathematical targets as QIRF2 meaning entries.
/// Each target must be the sealed receipt actually referenced by the program.
pub fn export_with_meanings(
    program: &AcceptedProgram,
    interface: Option<&RootInterface>,
    meanings: &[MeaningEvidence],
) -> Result<Vec<u8>> {
    let mut encoder = Encoder::new(Version::V2);
    for meaning in meanings {
        encoder.meanings.insert(
            Arc::clone(meaning.receipt().snapshot_key()),
            meaning.target().clone(),
        );
    }
    export_inner(program, interface, encoder)
}

fn meaning_value(target: &FiniteMeaning) -> Value {
    let (tag, table) = if target.phase_table().iter().all(|&p| p == 0) {
        (
            "permutation",
            target
                .permutation_table()
                .iter()
                .map(|&n| Value::Number(u64::from(n)))
                .collect(),
        )
    } else {
        (
            "phase8",
            target
                .phase_table()
                .iter()
                .map(|&n| Value::Number(u64::from(n)))
                .collect(),
        )
    };
    Value::object([
        ("tag", Value::String(tag.into())),
        ("table", Value::Array(table)),
    ])
}

fn export_inner(
    program: &AcceptedProgram,
    interface: Option<&RootInterface>,
    encoder: Encoder,
) -> Result<Vec<u8>> {
    if let Some(interface) = interface {
        check_interface(program, interface)?;
    }
    let bytes = encode_proposal(program.raw(), interface, encoder)?;
    // Public export retains its portable-validity contract. Native
    // adapters call encode_proposal directly and obtain a fresh native decision.
    program.kernel().inspect(&bytes, None)?;
    Ok(bytes)
}

/// Serialization is an untrusted proposal, never an acceptance result. Keeping
/// it separate avoids importing an export twice on selected checking paths.
fn encode_proposal(
    program: &RawProgram,
    interface: Option<&RootInterface>,
    mut encoder: Encoder,
) -> Result<Vec<u8>> {
    if let Some(interface) = interface {
        for tree in [&interface.input, &interface.output] {
            let mut pending = vec![(tree, 0usize)];
            let mut nodes = 0;
            while let Some((tree, depth)) = pending.pop() {
                nodes += 1;
                if depth > 32 || nodes > 128 {
                    return Err(Error::limit(
                        "proposal type exceeds transport depth/node limits",
                    ));
                }
                match tree {
                    BasisType::Pair(left, right) => {
                        pending.extend([(left.as_ref(), depth + 1), (right.as_ref(), depth + 1)])
                    }
                    BasisType::Tuple(fields) => {
                        if fields.len() > 128 {
                            return Err(Error::limit(
                                "proposal tuple exceeds transport node limit",
                            ));
                        }
                        pending.extend(fields.iter().map(|field| (field, depth + 1)));
                    }
                    BasisType::Unit | BasisType::Bit | BasisType::Bits(_) => {}
                }
            }
        }
    }
    let root = encoder.program(program)?;
    if encoder
        .meanings
        .keys()
        .any(|key| !encoder.canonical_evidence.contains_key(key))
    {
        return Err(Error::format(
            "supplied meaning receipt is not referenced by the program",
        ));
    }
    finish_proposal(root, interface, encoder)
}

fn finish_proposal(
    root: usize,
    interface: Option<&RootInterface>,
    mut encoder: Encoder,
) -> Result<Vec<u8>> {
    let version = encoder.version;
    let interface = match interface {
        Some(i) => Value::object([
            ("input", i.input.write(&mut encoder)?),
            ("output", i.output.write(&mut encoder)?),
        ]),
        None => Value::Null,
    };
    let value = Value::object([
        ("format", Value::String("qleisli.finite-ir".into())),
        ("version", Value::Number(version.number())),
        ("profile", Value::String(version.profile().into())),
        ("sources", source_values(&encoder.sources)),
        ("programs", Value::Array(encoder.programs)),
        ("evidence", Value::Array(encoder.entries)),
        ("root", Value::Number(root as u64)),
        ("root_interface", interface),
    ]);
    json::encode(&value)
}

/// Bound recursive transport construction before it starts. This walk does not
/// inspect ownership, effects, equations or evidence validity; those still go
/// to the independent checkers. Vector sizes are charged by Codec::write.
fn proposal_depth(program: &RawProgram) -> Result<()> {
    let mut pending = vec![(program.operations.as_slice(), 0usize)];
    let mut nodes = 0;
    while let Some((operations, depth)) = pending.pop() {
        if depth > 64 || operations.len() > MAX_NODES - nodes {
            return Err(Error::limit("proposal exceeds transport depth/node limits"));
        }
        nodes += operations.len();
        for operation in operations {
            if let crate::ir::RawOp::ClassicalBranch {
                then_ops, else_ops, ..
            } = operation
            {
                pending.extend([
                    (then_ops.as_slice(), depth + 1),
                    (else_ops.as_slice(), depth + 1),
                ]);
            }
        }
    }
    Ok(())
}

fn index(value: &Value, bound: usize) -> Result<usize> {
    let n = usize::read(value, &Decoder { evidence: &[] })?;
    if n >= bound {
        return Err(Error::format("dangling object reference"));
    }
    Ok(n)
}

fn sources(value: &Value) -> Result<Vec<(String, String)>> {
    let entries = value.array()?;
    if entries.len() > 128 {
        return Err(Error::limit("more than 128 sources"));
    }
    let mut names = BTreeSet::new();
    let mut bytes = 0usize;
    let mut out = Vec::new();
    for entry in entries {
        entry.fields(&["path", "text"])?;
        let path = entry.field("path")?.text()?;
        let text = entry.field("text")?.text()?;
        if path.is_empty() || path.contains('\0') || !names.insert(path) {
            return Err(Error::format("invalid or duplicate source path label"));
        }
        if path.len() > 4096 {
            return Err(Error::limit("source path exceeds 4096 bytes"));
        }
        bytes = bytes
            .checked_add(text.len())
            .ok_or_else(|| Error::limit("source byte overflow"))?;
        if bytes > MAX_SOURCE_BYTES {
            return Err(Error::limit("embedded source text exceeds 1 MiB"));
        }
        out.push((path.into(), text.into()));
    }
    Ok(out)
}

// Ordered snapshots are interned only within this import. The ordinary exact
// checker still validates every receipt and charges each distinct allocation.
type Snapshots = BTreeMap<Vec<usize>, Arc<Vec<(String, String)>>>;

fn identity(
    value: &Value,
    sources: &[(String, String)],
    used: &mut BTreeSet<usize>,
    remaining: &mut usize,
    snapshots: &mut Snapshots,
) -> Result<RetainedIdentity> {
    value.fields(&["implementation", "specification", "sources"])?;
    let implementation = value.field("implementation")?.text()?;
    let specification = value.field("specification")?.text()?;
    if implementation.is_empty() || specification.is_empty() {
        return Err(Error::format("empty evidence identity name"));
    }
    if implementation.len() > 4096 || specification.len() > 4096 {
        return Err(Error::limit("identity name exceeds 4096 bytes"));
    }
    *remaining = remaining
        .checked_sub(implementation.len() + specification.len())
        .ok_or_else(|| Error::limit("aggregate identity bytes exceed 1 MiB"))?;
    let mut local = BTreeSet::new();
    let mut snapshot = Vec::new();
    for item in value.field("sources")?.array()? {
        let i = index(item, sources.len())?;
        if !local.insert(i) {
            return Err(Error::format("duplicate identity source reference"));
        }
        if used.insert(i) {
            let (path, text) = &sources[i];
            *remaining = remaining
                .checked_sub(path.len() + text.len())
                .ok_or_else(|| Error::limit("aggregate identity bytes exceed 1 MiB"))?;
        }
        snapshot.push(i);
    }
    let shared = snapshots.entry(snapshot).or_insert_with_key(|indices| {
        Arc::new(indices.iter().map(|&i| sources[i].clone()).collect())
    });
    Ok(RetainedIdentity::shared(
        implementation.into(),
        specification.into(),
        Arc::clone(shared),
    ))
}

fn entry_tag(value: &Value, version: Version) -> Result<&str> {
    let tag = if version == Version::V1 {
        "circuit"
    } else {
        value.field("tag")?.text()?
    };
    match (version, tag) {
        (Version::V1, "circuit") => {
            value.fields(&["signature", "implementation", "specification", "identity"])?;
        }
        (Version::V2, "circuit") => {
            value.fields(&[
                "tag",
                "signature",
                "implementation",
                "specification",
                "identity",
            ])?;
        }
        (Version::V2, "meaning") => {
            value.fields(&["tag", "signature", "implementation", "meaning", "identity"])?;
        }
        _ => return Err(Error::format("unknown evidence tag")),
    }
    Ok(tag)
}

/// Preflight the combined graph iteratively, with one height per shared node.
/// A short first path cannot hide a deeper second path into a shared dependency.
fn graph(
    programs: &[Value],
    entries: &[Value],
    root: usize,
    version: Version,
) -> Result<Vec<usize>> {
    let p = programs.len();
    let n = p
        .checked_add(entries.len())
        .ok_or_else(|| Error::limit("object count overflow"))?;
    if n > MAX_OBJECTS {
        return Err(Error::limit("more than 65536 program/evidence objects"));
    }
    let mut edges = vec![vec![]; n];
    let mut count = 0usize;
    for (i, program) in programs.iter().enumerate() {
        let mut stack = vec![program];
        while let Some(value) = stack.pop() {
            match value {
                Value::Object(fields) => {
                    if fields.contains_key("tag") {
                        count += 1;
                    }
                    if fields.get("tag").and_then(|v| v.text().ok()) == Some("contract") {
                        edges[i].push(p + index(value.field("evidence")?, entries.len())?);
                    }
                    stack.extend(fields.values());
                }
                Value::Array(values) => stack.extend(values),
                _ => {}
            }
            if count > MAX_NODES {
                return Err(Error::limit("raw/step node budget exhausted"));
            }
        }
    }
    for (i, entry) in entries.iter().enumerate() {
        let tag = entry_tag(entry, version)?;
        edges[p + i].push(index(entry.field("implementation")?, p)?);
        if tag == "circuit" {
            edges[p + i].push(index(entry.field("specification")?, p)?);
        }
    }
    let mut states = vec![0u8; n];
    let mut heights = vec![0usize; n];
    let mut order = vec![];
    let mut stack = vec![(root, 0usize)];
    states[root] = 1;
    while let Some((node, next)) = stack.last_mut() {
        if let Some(&child) = edges[*node].get(*next) {
            *next += 1;
            match states[child] {
                1 => return Err(Error::format("cyclic program/evidence graph")),
                0 => {
                    states[child] = 1;
                    stack.push((child, 0));
                    if stack.len() > 32 {
                        return Err(Error::limit("graph depth exceeds 32"));
                    }
                }
                _ => {}
            }
        } else {
            let id = *node;
            heights[id] = 1 + edges[id].iter().map(|&c| heights[c]).max().unwrap_or(0);
            if heights[id] > 32 {
                return Err(Error::limit("graph depth exceeds 32"));
            }
            states[id] = 2;
            order.push(id);
            stack.pop();
        }
    }
    if states.contains(&0) {
        return Err(Error::format("unused program or evidence entry"));
    }
    Ok(order)
}

fn type_bits(ty: &BasisType) -> Result<usize> {
    let mut stack = vec![(ty, 1)];
    let (mut bits, mut nodes) = (0usize, 0usize);
    while let Some((ty, depth)) = stack.pop() {
        nodes += 1;
        if nodes > 4096 || depth > 64 {
            return Err(Error::limit("root type exceeds depth 64 or 4096 nodes"));
        }
        match ty {
            BasisType::Unit => {}
            BasisType::Bit => {
                bits = bits
                    .checked_add(1)
                    .ok_or_else(|| Error::limit("root bit width overflows host capacity"))?;
            }
            BasisType::Bits(width) => {
                bits = bits
                    .checked_add(*width as usize)
                    .ok_or_else(|| Error::limit("root bit width overflows host capacity"))?;
            }
            BasisType::Pair(a, b) => {
                stack.push((b, depth + 1));
                stack.push((a, depth + 1));
            }
            BasisType::Tuple(fields) => {
                if fields.len() < 3 {
                    return Err(Error::format("tuple type requires at least three fields"));
                }
                if fields.len() > 4096 {
                    return Err(Error::limit("root tuple exceeds type-node limit"));
                }
                stack.extend(fields.iter().map(|field| (field, depth + 1)));
            }
        }
    }
    if bits > 12 {
        return Err(Error::limit("root type exceeds twelve bits"));
    }
    Ok(bits)
}

fn check_interface(program: &AcceptedProgram, interface: &RootInterface) -> Result<()> {
    let raw = program.raw();
    if raw.declared_effect != Effect::Unitary
        || raw.quantum_inputs.len() != 1
        || raw.quantum_outputs.len() != 1
        || !raw.classical_inputs.is_empty()
        || !raw.classical_outputs.is_empty()
    {
        return Err(Error::new(
            "invalid_ir",
            "root interface requires a unary unitary with no classical ports",
        ));
    }
    let width = usize::from(raw.quantum_inputs[0].shape.bits);
    // The finite verifier established conservation of dimension and complete
    // ownership. With one input and one output, the output has this same width;
    // its ordered wires remain those bound in the complete raw program.
    if type_bits(&interface.input)? != width || type_bits(&interface.output)? != width {
        return Err(Error::new(
            "invalid_ir",
            "root type width does not match its verified port",
        ));
    }
    Ok(())
}

fn meaning(value: &Value, signature: BasisType) -> Result<FiniteMeaning> {
    value.fields(&["tag", "table"])?;
    let decoder = Decoder { evidence: &[] };
    match value.field("tag")?.text()? {
        "permutation" => FiniteMeaning::permutation(
            signature,
            Vec::<u16>::read(value.field("table")?, &decoder)?,
        )
        .map_err(contract_error),
        "phase8" => {
            FiniteMeaning::phase(signature, Vec::<u8>::read(value.field("table")?, &decoder)?)
                .map_err(contract_error)
        }
        _ => Err(Error::format("unknown finite meaning tag")),
    }
}

pub(crate) fn function_snapshot_key(
    signature: &BasisType,
    implementation: &RawProgram,
    specification: &RawProgram,
    identity: (&str, &str, &[(String, String)]),
) -> Result<Arc<[u8]>> {
    let mut encoder = Encoder::new(Version::V2);
    encoder.entries.push(Value::Null);
    encoder.evidence_fields(0, signature, implementation, specification, identity, None)?;
    Ok(Arc::from(finish_proposal(0, None, encoder)?))
}

/// Fresh native acceptance of complete QIRF/request bytes. Source labels are data.
pub fn import(bytes: &[u8], request: Option<&[u8]>) -> Result<Imported> {
    native::Kernel::selected()?
        .check(bytes, request)
        .map(|checked| checked.imported)
}

// Structural transport parsing only: this neither checks semantics nor issues a handle.
// Share it with optional diagnostics after native rejection, preserving field locations.
fn envelope(value: &Value) -> Result<(Version, &[Value], &[Value], usize)> {
    value.fields(&[
        "format",
        "version",
        "profile",
        "sources",
        "programs",
        "evidence",
        "root",
        "root_interface",
    ])?;
    if value.field("format")?.text().map_err(|e| e.at("/format"))? != "qleisli.finite-ir" {
        return Err(Error::format("unknown artifact format").at("/format"));
    }
    let version = match value
        .field("version")?
        .number()
        .map_err(|e| e.at("/version"))?
    {
        1 => Version::V1,
        2 => Version::V2,
        _ => return Err(Error::format("unknown QIRF version").at("/version")),
    };
    if value
        .field("profile")?
        .text()
        .map_err(|e| e.at("/profile"))?
        != version.profile()
    {
        return Err(Error::format("version/profile mismatch").at("/profile"));
    }
    let programs = value
        .field("programs")?
        .array()
        .map_err(|e| e.at("/programs"))?;
    let entries = value
        .field("evidence")?
        .array()
        .map_err(|e| e.at("/evidence"))?;
    let root = index(value.field("root")?, programs.len()).map_err(|e| e.at("/root"))?;
    Ok((version, programs, entries, root))
}

type RootParts = (RawProgram, Option<RootInterface>, Vec<(String, String)>);
fn decode_native(native: &native::NativeChecked, budget: &mut Budget) -> Result<RootParts> {
    let value = json::parse(native.artifact())?;
    let (version, programs, entries, root) = envelope(&value)?;
    let snapshot = sources(value.field("sources")?).map_err(|e| e.at("/sources"))?;
    let order = graph(programs, entries, root, version)?;
    let mut checked = vec![None; programs.len()];
    let mut receipts = vec![None; entries.len()];
    let mut used = BTreeSet::new();
    let mut identity_bytes = MAX_SOURCE_BYTES;
    let mut snapshots = Snapshots::new();
    for node in order {
        let decoder = Decoder {
            evidence: &receipts,
        };
        if node < programs.len() {
            let pointer = format!("/programs/{node}");
            let raw = RawProgram::read(&programs[node], &decoder).map_err(|e| e.at(&pointer))?;
            checked[node] = Some(raw);
        } else {
            let i = node - programs.len();
            let entry = &entries[i];
            let pointer = format!("/evidence/{i}");
            let mut make_receipt = || -> Result<Arc<FunctionEvidence>> {
                let signature = BasisType::read(entry.field("signature")?, &decoder)?;
                let implementation = checked
                    [index(entry.field("implementation")?, programs.len())?]
                .as_ref()
                .expect("topological implementation")
                .clone();
                let identity = identity(
                    entry.field("identity")?,
                    &snapshot,
                    &mut used,
                    &mut identity_bytes,
                    &mut snapshots,
                )?;
                if entry_tag(entry, version)? == "circuit" {
                    let specification = checked
                        [index(entry.field("specification")?, programs.len())?]
                    .as_ref()
                    .expect("topological specification")
                    .clone();
                    Ok(Arc::new(
                        FunctionEvidence::decode_native(
                            native,
                            signature,
                            implementation,
                            specification,
                            identity,
                            budget,
                        )
                        .map_err(|diagnostic| contract_error(diagnostic.error))?,
                    ))
                } else {
                    let target = meaning(entry.field("meaning")?, signature.clone())?;
                    Ok(Arc::new(
                        FunctionEvidence::decode_native(
                            native,
                            signature,
                            implementation,
                            target.target_ir().map_err(contract_error)?,
                            identity,
                            budget,
                        )
                        .map_err(|diagnostic| contract_error(diagnostic.error))?,
                    ))
                }
            };
            receipts[i] = Some(make_receipt().map_err(|e| e.at(pointer))?);
        }
    }
    if used.len() != snapshot.len() {
        return Err(Error::format("unused source entry").at("/sources"));
    }
    let program = checked[root].take().expect("root checked");
    let interface = match value.field("root_interface")? {
        Value::Null => None,
        i => {
            i.fields(&["input", "output"])?;
            let decoder = Decoder { evidence: &[] };
            let interface = RootInterface {
                input: BasisType::read(i.field("input")?, &decoder)?,
                output: BasisType::read(i.field("output")?, &decoder)?,
            };
            Some(interface)
        }
    };
    Ok((program, interface, snapshot))
}

/// Checked format migration preserves exact root metadata and source ordering.
/// V2 meaning entries cannot be converted to V1 by this adapter.
pub fn convert(bytes: &[u8], version: Version) -> Result<Vec<u8>> {
    import(bytes, None)?;
    let output = convert_proposal(bytes, version)?;
    import(&output, None)?;
    Ok(output)
}

/// Called only after an original artifact check; output still needs a fresh
/// check. This transformation cannot manufacture an accepted-program handle.
fn convert_proposal(bytes: &[u8], version: Version) -> Result<Vec<u8>> {
    let mut value = json::parse(bytes)?;
    let Value::Object(ref mut object) = value else {
        unreachable!()
    };
    if let Some(Value::Array(entries)) = object.get_mut("evidence") {
        for entry in entries {
            let Value::Object(fields) = entry else {
                unreachable!()
            };
            if version == Version::V1 {
                if fields
                    .get("tag")
                    .is_some_and(|v| v.text().ok() == Some("meaning"))
                {
                    return Err(Error::new(
                        "unsupported",
                        "QIRF1 cannot represent meaning entries",
                    ));
                }
                fields.remove("tag");
            } else {
                fields
                    .entry("tag".into())
                    .or_insert_with(|| Value::String("circuit".into()));
            }
        }
    }
    object.insert("version".into(), Value::Number(version.number()));
    object.insert("profile".into(), Value::String(version.profile().into()));
    json::encode(&value)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn set(value: &mut Value, key: &str, new: Value) {
        let Value::Object(fields) = value else {
            panic!()
        };
        fields.insert(key.into(), new);
    }
    fn program(dependencies: &[usize]) -> Value {
        Value::Array(
            dependencies
                .iter()
                .map(|&i| {
                    Value::object([
                        ("tag", Value::String("contract".into())),
                        ("evidence", Value::Number(i as u64)),
                    ])
                })
                .collect(),
        )
    }
    fn entry(implementation: usize, specification: usize) -> Value {
        Value::object([
            ("signature", Value::Null),
            ("identity", Value::Null),
            ("implementation", Value::Number(implementation as u64)),
            ("specification", Value::Number(specification as u64)),
        ])
    }
    #[test]
    fn graph_checks_cycles_dangling_unused_and_every_shared_path() {
        let mut programs = vec![program(&[0]), program(&[]), program(&[])];
        let mut entries = vec![entry(1, 2)];
        assert_eq!(
            graph(&programs, &entries, 0, Version::V1).unwrap(),
            vec![1, 2, 3, 0]
        );
        set(&mut entries[0], "implementation", Value::Number(0));
        assert!(
            graph(&programs, &entries, 0, Version::V1)
                .unwrap_err()
                .message
                .contains("cyclic")
        );
        entries[0] = entry(1, 2);
        programs.push(program(&[]));
        assert!(
            graph(&programs, &entries, 0, Version::V1)
                .unwrap_err()
                .message
                .contains("unused")
        );
        programs.pop();
        programs[0] = program(&[1]);
        assert!(graph(&programs, &entries, 0, Version::V1).is_err());
        // The leaf is first reached directly, then again through a long path.
        for depth in [15, 16] {
            let mut p = vec![program(&[0, 1]), program(&[])];
            let mut e = vec![entry(1, 1)];
            for i in 1..=depth {
                let target = p.len();
                p.push(if i == depth {
                    program(&[0])
                } else {
                    program(&[i + 1])
                });
                e.push(entry(target, target));
            }
            let result = graph(&p, &e, 0, Version::V1);
            if depth == 15 {
                assert!(result.is_err());
            } // 33 nodes on longest path.
            assert_eq!(result.unwrap_err().code, "limit");
        }
        assert_eq!(
            graph(&vec![Value::Null; MAX_OBJECTS + 1], &[], 0, Version::V1)
                .unwrap_err()
                .code,
            "limit"
        );
    }
    #[test]
    fn strict_json_bounds_and_unicode_do_not_normalize_identities() {
        for bytes in [
            br#"{"a":0,"a":1}"#.as_slice(),
            br#"{"a":0,"\u0061":1}"#,
            br#""\ud800""#,
            br#""\udc00""#,
            br#"[01]"#,
            br#"[1e0]"#,
            br#"[+1]"#,
            br#"[1,]"#,
            br#"{"a":1,}"#,
        ] {
            assert!(json::parse(bytes).is_err());
        }
        assert_eq!(
            json::parse(br#""\ud83e\udd80""#).unwrap(),
            Value::String("🦀".into())
        );
        let bytes = format!("[{}0]", "0,".repeat(1_000_000));
        assert_eq!(json::parse(bytes.as_bytes()).unwrap_err().code, "limit");
        let bytes = format!("{}0{}", "[".repeat(128), "]".repeat(128));
        json::parse(bytes.as_bytes()).unwrap();
        assert_eq!(
            json::parse(format!("[{bytes}]").as_bytes())
                .unwrap_err()
                .code,
            "limit"
        );
    }
    #[test]
    fn source_and_identity_limits_are_aggregate_and_sources_never_resolve() {
        let values =
            source_values(&[("../../does-not-exist".into(), "x".repeat(MAX_SOURCE_BYTES))]);
        let source = sources(&values).unwrap();
        let id = Value::object([
            ("implementation", Value::String("f".into())),
            ("specification", Value::String("s".into())),
            ("sources", Value::Array(vec![Value::Number(0)])),
        ]);
        let mut remaining = MAX_SOURCE_BYTES;
        assert_eq!(
            identity(
                &id,
                &source,
                &mut BTreeSet::new(),
                &mut remaining,
                &mut Snapshots::new()
            )
            .err()
            .unwrap()
            .code,
            "limit"
        );
        let values = source_values(&[
            ("x".into(), "x".repeat(MAX_SOURCE_BYTES)),
            ("y".into(), "z".into()),
        ]);
        assert_eq!(sources(&values).unwrap_err().code, "limit");
        assert!(
            sources(&source_values(&[
                ("a".into(), "".into()),
                ("a".into(), "".into())
            ]))
            .is_err()
        );
        assert!(sources(&source_values(&[("\0".into(), "".into())])).is_err());
    }

    #[test]
    fn shared_snapshots_charge_once_and_preserve_order_and_duplicate_checks() {
        let source = vec![
            ("a".into(), "x".repeat(600_000)),
            ("b".into(), "y".repeat(100_000)),
        ];
        let id = |indices: &[u64]| {
            Value::object([
                ("implementation", Value::String("f".into())),
                ("specification", Value::String("s".into())),
                (
                    "sources",
                    Value::Array(indices.iter().copied().map(Value::Number).collect()),
                ),
            ])
        };
        let mut used = BTreeSet::new();
        let mut remaining = MAX_SOURCE_BYTES;
        let mut snapshots = Snapshots::new();
        let first = identity(
            &id(&[0, 1]),
            &source,
            &mut used,
            &mut remaining,
            &mut snapshots,
        )
        .unwrap();
        let second = identity(
            &id(&[0, 1]),
            &source,
            &mut used,
            &mut remaining,
            &mut snapshots,
        )
        .unwrap();
        let (
            RetainedIdentity::Shared { sources: a, .. },
            RetainedIdentity::Shared { sources: b, .. },
        ) = (first, second)
        else {
            panic!("shared snapshots required")
        };
        assert!(Arc::ptr_eq(&a, &b));
        assert_eq!(remaining, MAX_SOURCE_BYTES - 700_002 - 4);
        let reverse = identity(
            &id(&[1, 0]),
            &source,
            &mut used,
            &mut remaining,
            &mut snapshots,
        )
        .unwrap();
        let RetainedIdentity::Shared {
            sources: reverse, ..
        } = reverse
        else {
            unreachable!()
        };
        assert_eq!(reverse[0], source[1]);
        assert!(!Arc::ptr_eq(&a, &reverse));
        assert!(
            identity(
                &id(&[0, 0]),
                &source,
                &mut used,
                &mut remaining,
                &mut snapshots
            )
            .is_err()
        );
        assert!(
            identity(
                &id(&[2]),
                &source,
                &mut used,
                &mut remaining,
                &mut snapshots
            )
            .is_err()
        );
        // Repeated names still consume the artifact's aggregate identity budget.
        let mut tiny = 1;
        assert_eq!(
            identity(&id(&[0, 1]), &source, &mut used, &mut tiny, &mut snapshots)
                .err()
                .unwrap()
                .code,
            "limit"
        );
    }

    #[test]
    fn display_omits_only_the_absent_pointer() {
        assert_eq!(
            Error::limit("budget exhausted").to_string(),
            "limit: budget exhausted"
        );
        assert_eq!(
            Error::limit("budget exhausted")
                .at("/evidence/0")
                .to_string(),
            "limit at /evidence/0: budget exhausted"
        );
    }
}

mod process;
