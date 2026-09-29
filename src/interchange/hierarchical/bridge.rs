//! Strict external field codec and untrusted schedule/binary producer.
//! The Lean checker independently validates every proposed reference and rule.
mod request;
pub(super) use request::decode_request;

use std::collections::VecDeque;

use super::super::json::{self, Value};
use super::super::{Error, Result};

pub(super) struct Decoded {
    pub value: Value,
    pub bridge: Vec<u8>,
    pub definition_order: Vec<usize>,
}

pub(super) fn number(value: &Value) -> Result<u32> {
    u32::try_from(value.number()?).map_err(|_| Error::limit("hierarchy integer exceeds u32"))
}

struct Writer {
    bytes: Vec<u8>,
    reads: usize,
    current: usize,
    counts: [usize; 4],
    edges: Vec<Vec<usize>>,
    payload_bytes: usize,
}

impl Writer {
    fn word(&mut self, n: u32) -> Result<()> {
        self.reads += 1;
        if self.reads > 1_000_000 || self.bytes.len() + 4 > 64 << 20 {
            return Err(Error::limit("hierarchy bridge framing limit exceeded"));
        }
        self.bytes.extend_from_slice(&n.to_le_bytes());
        Ok(())
    }
    fn nat(&mut self, v: &Value) -> Result<()> {
        self.word(number(v)?)
    }
    fn field(&mut self, v: &Value, key: &str) -> Result<()> {
        self.nat(v.field(key)?)
    }
    fn boolean(&mut self, v: &Value) -> Result<()> {
        self.word(u32::from(v.boolean()?))
    }
    fn bytes(&mut self, v: &Value) -> Result<()> {
        let bytes = v.text()?.as_bytes();
        self.word(bytes.len() as u32)?;
        self.payload_bytes += bytes.len();
        if self.payload_bytes > json::MAX_BYTES || self.bytes.len() + bytes.len() > 64 << 20 {
            return Err(Error::limit("aggregate hierarchy payload exceeds 16 MiB"));
        }
        self.bytes.extend_from_slice(bytes);
        Ok(())
    }
    fn array(&mut self, v: &Value, f: impl Fn(&mut Self, &Value) -> Result<()>) -> Result<()> {
        let values = v.array()?;
        if values.len() > 100_000 {
            return Err(Error::limit("hierarchy array exceeds 100000"));
        }
        self.word(values.len() as u32)?;
        for value in values {
            f(self, value)?;
        }
        Ok(())
    }
    fn numbers(&mut self, v: &Value) -> Result<()> {
        self.array(v, Self::nat)
    }
    fn reference(&mut self, table: usize, value: &Value) -> Result<()> {
        let n = number(value)? as usize;
        if n >= self.counts[table] {
            return Err(Error::new(
                "invalid_ir",
                "hierarchy reference outside its table",
            ));
        }
        let offset: usize = self.counts[..table].iter().sum();
        self.edges[self.current].push(offset + n);
        self.word(n as u32)
    }
    fn reference_field(&mut self, table: usize, value: &Value, key: &str) -> Result<()> {
        self.reference(table, value.field(key)?)
    }
    fn basis(&mut self, v: &Value) -> Result<()> {
        self.array(v, |w, atom| match atom.field("tag")?.text()? {
            "unit" => {
                atom.fields(&["tag"])?;
                w.word(0)
            }
            "bit" => {
                atom.fields(&["tag"])?;
                w.word(1)
            }
            "bits" => {
                atom.fields(&["tag", "width"])?;
                w.word(2)?;
                w.field(atom, "width")
            }
            "tuple" => {
                atom.fields(&["tag", "arity"])?;
                w.word(3)?;
                w.field(atom, "arity")
            }
            _ => Err(Error::format("unknown hierarchy type atom")),
        })
    }
    fn side(&mut self, v: &Value) -> Result<()> {
        v.fields(&["quantum", "classical"])?;
        self.array(v.field("quantum")?, |w, p| {
            p.fields(&["owner", "basis", "axes"])?;
            w.field(p, "owner")?;
            w.basis(p.field("basis")?)?;
            w.numbers(p.field("axes")?)
        })?;
        self.array(v.field("classical")?, |w, p| {
            p.fields(&["value", "basis"])?;
            w.field(p, "value")?;
            w.basis(p.field("basis")?)
        })
    }
    fn interface(&mut self, v: &Value) -> Result<()> {
        v.fields(&["inputs", "outputs"])?;
        self.side(v.field("inputs")?)?;
        self.side(v.field("outputs")?)
    }
    fn port_map(&mut self, v: &Value) -> Result<()> {
        v.fields(&["owners", "axes", "classical"])?;
        for key in ["owners", "axes", "classical"] {
            self.numbers(v.field(key)?)?;
        }
        Ok(())
    }
    fn structural(&mut self, v: &Value) -> Result<()> {
        let tag = v.field("tag")?.text()?;
        let tags = [
            "take_bit",
            "put_bit",
            "split_tuple",
            "join_tuple",
            "bit_to_bits",
            "bits_to_bit",
            "pack_unit",
            "unpack_unit",
            "pack_empty_bits",
            "unpack_empty_bits",
        ];
        let code = tags
            .iter()
            .position(|t| *t == tag)
            .ok_or_else(|| Error::format("unknown structural operation"))?;
        if code < 2 {
            v.fields(&["tag", "width", "position"])?;
        } else {
            v.fields(&["tag"])?;
        }
        self.word(code as u32)?;
        if code < 2 {
            self.field(v, "width")?;
            self.field(v, "position")?;
        }
        Ok(())
    }
    fn definition(&mut self, v: &Value) -> Result<()> {
        v.fields(&["interface", "effect", "body"])?;
        self.interface(v.field("interface")?)?;
        self.word(match v.field("effect")?.text()? {
            "unitary" => 0,
            "iso" => 1,
            "observe" => 2,
            _ => return Err(Error::format("unknown effect")),
        })?;
        let b = v.field("body")?;
        match b.field("tag")?.text()? {
            "leaf" => {
                b.fields(&["tag", "program"])?;
                self.word(0)?;
                self.bytes(b.field("program")?)
            }
            "sequence" => {
                b.fields(&["tag", "children"])?;
                self.word(1)?;
                self.array(b.field("children")?, |w, v| w.reference(0, v))
            }
            "tensor" => {
                b.fields(&["tag", "left", "right"])?;
                self.word(2)?;
                self.reference_field(0, b, "left")?;
                self.reference_field(0, b, "right")
            }
            "call" => {
                b.fields(&["tag", "definition", "input_map", "output_map"])?;
                self.word(3)?;
                self.reference_field(0, b, "definition")?;
                self.port_map(b.field("input_map")?)?;
                self.port_map(b.field("output_map")?)
            }
            "repeat" => {
                b.fields(&["tag", "count", "definition"])?;
                self.word(4)?;
                self.field(b, "count")?;
                self.reference_field(0, b, "definition")
            }
            "inverse" => {
                b.fields(&["tag", "definition"])?;
                self.word(5)?;
                self.reference_field(0, b, "definition")
            }
            "control" => {
                b.fields(&["tag", "definition", "polarity"])?;
                self.word(6)?;
                self.reference_field(0, b, "definition")?;
                self.boolean(b.field("polarity")?)
            }
            "rewire" => {
                b.fields(&["tag", "permutation"])?;
                self.word(7)?;
                self.port_map(b.field("permutation")?)
            }
            "structural" => {
                b.fields(&["tag", "operation"])?;
                self.word(8)?;
                self.structural(b.field("operation")?)
            }
            "dyadic_phase" => {
                b.fields(&["tag", "target", "j", "k"])?;
                self.word(9)?;
                self.field(b, "target")?;
                self.field(b, "j")?;
                self.field(b, "k")
            }
            "computed" => {
                b.fields(&["tag", "compute", "use", "logical", "encoding"])?;
                self.word(10)?;
                self.reference_field(0, b, "compute")?;
                self.reference_field(0, b, "use")?;
                self.reference_field(1, b, "logical")?;
                self.reference_field(2, b, "encoding")
            }
            "observe_z" => {
                b.fields(&["tag", "input", "output"])?;
                self.word(11)?;
                self.field(b, "input")?;
                self.field(b, "output")
            }
            "init0" => {
                b.fields(&["tag", "output"])?;
                self.word(12)?;
                self.field(b, "output")
            }
            _ => Err(Error::format("unknown definition node")),
        }
    }
    fn meaning(&mut self, v: &Value) -> Result<()> {
        v.fields(&["interface", "body"])?;
        self.interface(v.field("interface")?)?;
        let b = v.field("body")?;
        match b.field("tag")?.text()? {
            "identity" => {
                b.fields(&["tag"])?;
                self.word(0)
            }
            "finite" => {
                b.fields(&["tag", "description"])?;
                self.word(1)?;
                self.bytes(b.field("description")?)
            }
            "sequence" => {
                b.fields(&["tag", "children"])?;
                self.word(2)?;
                self.array(b.field("children")?, |w, v| w.reference(1, v))
            }
            "tensor" => {
                b.fields(&["tag", "left", "right"])?;
                self.word(3)?;
                self.reference_field(1, b, "left")?;
                self.reference_field(1, b, "right")
            }
            "inverse" => {
                b.fields(&["tag", "child"])?;
                self.word(4)?;
                self.reference_field(1, b, "child")
            }
            "control" => {
                b.fields(&["tag", "child", "polarity"])?;
                self.word(5)?;
                self.reference_field(1, b, "child")?;
                self.boolean(b.field("polarity")?)
            }
            "power" => {
                b.fields(&["tag", "child", "count"])?;
                self.word(6)?;
                self.reference_field(1, b, "child")?;
                self.field(b, "count")
            }
            "rewire" => {
                b.fields(&["tag", "permutation"])?;
                self.word(7)?;
                self.port_map(b.field("permutation")?)
            }
            "structural" => {
                b.fields(&["tag", "operation"])?;
                self.word(8)?;
                self.structural(b.field("operation")?)
            }
            "phase" => {
                b.fields(&["tag", "j", "k"])?;
                self.word(9)?;
                self.field(b, "j")?;
                self.field(b, "k")
            }
            "qft" => {
                b.fields(&["tag", "width"])?;
                self.word(10)?;
                self.field(b, "width")
            }
            "qpe_instrument" => {
                b.fields(&["tag", "target", "precision", "provider_meaning"])?;
                self.word(11)?;
                self.field(b, "target")?;
                self.field(b, "precision")?;
                self.reference_field(1, b, "provider_meaning")
            }
            _ => Err(Error::format("unknown meaning node")),
        }
    }
    fn encoding(&mut self, v: &Value) -> Result<()> {
        v.fields(&["logical", "physical", "body"])?;
        self.side(v.field("logical")?)?;
        self.side(v.field("physical")?)?;
        let b = v.field("body")?;
        match b.field("tag")?.text()? {
            "identity" => {
                b.fields(&["tag"])?;
                self.word(0)
            }
            "tensor" => {
                b.fields(&["tag", "left", "right"])?;
                self.word(1)?;
                self.reference_field(2, b, "left")?;
                self.reference_field(2, b, "right")
            }
            "rewire" => {
                b.fields(&["tag", "child", "permutation"])?;
                self.word(2)?;
                self.reference_field(2, b, "child")?;
                self.port_map(b.field("permutation")?)
            }
            "zero_scratch" => {
                b.fields(&["tag", "scratch_bits", "compute"])?;
                self.word(3)?;
                self.field(b, "scratch_bits")?;
                self.reference_field(0, b, "compute")
            }
            _ => Err(Error::format("unknown encoding node")),
        }
    }
    fn proof(&mut self, v: &Value) -> Result<()> {
        v.fields(&[
            "kind",
            "rule",
            "premises",
            "implementation",
            "meaning",
            "input_encoding",
            "output_encoding",
            "witness",
        ])?;
        self.word(match v.field("kind")?.text()? {
            "equation" => 0,
            "instrument" => 1,
            _ => return Err(Error::format("unknown proof kind")),
        })?;
        let rule = v.field("rule")?;
        let tag = rule.field("tag")?.text()?;
        if tag == "schema" {
            rule.fields(&["tag", "id"])?;
            return Err(Error::new(
                "contract",
                "external hierarchy schemas remain disabled",
            ));
        }
        rule.fields(&["tag"])?;
        let tags = [
            "finite",
            "sequence",
            "tensor",
            "inverse",
            "control",
            "repeat",
            "associativity",
            "rewire",
            "structural",
            "phase",
            "computed",
            "conjugation",
        ];
        self.word(
            tags.iter()
                .position(|t| *t == tag)
                .ok_or_else(|| Error::format("unknown proof rule"))? as u32,
        )?;
        self.array(v.field("premises")?, |w, v| w.reference(3, v))?;
        for (table, key) in [
            (0, "implementation"),
            (1, "meaning"),
            (2, "input_encoding"),
            (2, "output_encoding"),
        ] {
            self.reference_field(table, v, key)?;
        }
        let witness = v.field("witness")?;
        witness.fields(&["template_version", "parameters", "references"])?;
        self.field(witness, "template_version")?;
        self.numbers(witness.field("parameters")?)?;
        self.array(witness.field("references")?, |w, r| {
            r.fields(&["table", "index"])?;
            let table = match r.field("table")?.text()? {
                "definition" => 0,
                "meaning" => 1,
                "encoding" => 2,
                "proof" => 3,
                _ => return Err(Error::format("unknown reference table")),
            };
            w.word(table as u32)?;
            w.reference_field(table, r, "index")
        })
    }
    fn schedule(&self) -> Result<Vec<usize>> {
        let mut remaining: Vec<usize> = self.edges.iter().map(Vec::len).collect();
        let mut parents = vec![Vec::new(); self.edges.len()];
        let mut ready = VecDeque::new();
        for (index, children) in self.edges.iter().enumerate() {
            if children.is_empty() {
                ready.push_back(index);
            }
            for child in children {
                parents[*child].push(index);
            }
        }
        let mut order = Vec::with_capacity(self.edges.len());
        while let Some(child) = ready.pop_front() {
            order.push(child);
            for parent in &parents[child] {
                remaining[*parent] -= 1;
                if remaining[*parent] == 0 {
                    ready.push_back(*parent);
                }
            }
        }
        if order.len() != self.edges.len() {
            return Err(Error::new("invalid_ir", "cyclic hierarchy references"));
        }
        Ok(order)
    }
}

pub(super) fn decode(payload: &[u8]) -> Result<Decoded> {
    let value = json::parse(payload)?;
    value.fields(&[
        "format",
        "version",
        "profile",
        "definitions",
        "meanings",
        "encodings",
        "proofs",
        "entry",
    ])?;
    if value.field("format")?.text()? != "qleisli.hierarchical-ir"
        || value.field("version")?.number()? != 1
        || value.field("profile")?.text()? != "qpe-dyadic8-v1"
    {
        return Err(Error::format(
            "unsupported hierarchy format, version or profile",
        ));
    }
    let names = ["definitions", "meanings", "encodings", "proofs"];
    let mut counts = [0; 4];
    for (i, key) in names.iter().enumerate() {
        counts[i] = value.field(key)?.array()?.len();
    }
    let total: usize = counts.iter().sum();
    if total == 0 || total > 100_000 {
        return Err(Error::limit(
            "combined hierarchy tables exceed 100000 nodes",
        ));
    }
    let mut w = Writer {
        bytes: b"QLH1".to_vec(),
        reads: 0,
        current: 0,
        counts,
        edges: vec![vec![]; total],
        payload_bytes: 0,
    };
    let methods = [
        Writer::definition,
        Writer::meaning,
        Writer::encoding,
        Writer::proof,
    ];
    let mut offset = 0;
    for (i, key) in names.iter().enumerate() {
        w.word(counts[i] as u32)?;
        for (index, item) in value.field(key)?.array()?.iter().enumerate() {
            w.current = offset + index;
            methods[i](&mut w, item)?;
        }
        offset += counts[i];
    }
    let entry = value.field("entry")?;
    entry.fields(&["implementation", "proof"])?;
    for (table, key) in [(0, "implementation"), (3, "proof")] {
        let n = number(entry.field(key)?)? as usize;
        if n >= counts[table] {
            return Err(Error::new("invalid_ir", "entry outside its table"));
        }
        w.word(n as u32)?;
    }
    let order = w.schedule()?;
    let definition_order = order.iter().copied().filter(|i| *i < counts[0]).collect();
    w.word(order.len() as u32)?;
    for index in order {
        w.word(index as u32)?;
    }
    Ok(Decoded {
        value,
        bridge: w.bytes,
        definition_order,
    })
}
