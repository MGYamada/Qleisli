//! Private named-QPE framing; candidate structure is never acceptance evidence.
//! Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

use std::collections::BTreeSet;

use super::request::BoundDecoded;
use super::{Error, Result, Value, Writer, decode_request, json, number};

pub(crate) struct QpeDecoded {
    pub provider: BoundDecoded,
    pub bridge: Vec<u8>,
    pub hadamards: BTreeSet<usize>,
}

fn body<'a>(definitions: &'a [Value], index: usize, tag: &str) -> Result<&'a Value> {
    let value = definitions
        .get(index)
        .ok_or_else(|| Error::format("QPE candidate definition outside table"))?
        .field("body")?;
    if value.field("tag")?.text()? != tag {
        return Err(Error::new(
            "contract",
            "QPE candidate has a different body shape",
        ));
    }
    Ok(value)
}

fn child(values: &[Value], index: usize) -> Result<usize> {
    values
        .get(index)
        .ok_or_else(|| Error::new("contract", "QPE candidate misses a child"))
        .and_then(|v| number(v).map(|n| n as usize))
}

/// Only recover the exact finite-obligation indices; Lean independently checks
/// every shape, interface, route and equation. At most eight stages are read.
fn expected_hadamards(graph: &Value, candidate: &Value, width: usize) -> Result<BTreeSet<usize>> {
    if !(1..=8).contains(&width) {
        return Err(Error::limit("QPE precision requires 1..=8 bits"));
    }
    let phase = candidate.field("hadamards")?.array()?;
    if phase.len() != width {
        return Err(Error::new("contract", "QPE phase Hadamard arity differs"));
    }
    let definitions = graph.field("definitions")?.array()?;
    let mut expected = BTreeSet::new();
    for atom in phase {
        atom.fields(&["index", "interface"])?;
        let index = number(atom.field("index")?)? as usize;
        body(definitions, index, "leaf")?;
        expected.insert(index);
    }
    let inverse = candidate.field("inverse_fourier")?;
    inverse.fields(&["index", "interface"])?;
    let inverse = body(
        definitions,
        number(inverse.field("index")?)? as usize,
        "inverse",
    )?;
    let forward = body(
        definitions,
        number(inverse.field("definition")?)? as usize,
        "sequence",
    )?;
    let mut index = child(forward.field("children")?.array()?, 1)?;
    for remaining in (1..=width).rev() {
        let stage = body(definitions, index, "sequence")?;
        let children = stage.field("children")?.array()?;
        if children.len() != if remaining == 1 { 4 } else { 5 } {
            return Err(Error::new("contract", "QPE Fourier stage arity differs"));
        }
        let first = body(definitions, child(children, 1)?, "tensor")?;
        let h = body(
            definitions,
            number(first.field("left")?)? as usize,
            "sequence",
        )?;
        let h_children = h.field("children")?.array()?;
        if h_children.len() != 2 {
            return Err(Error::new(
                "contract",
                "QPE Fourier H wrapper arity differs",
            ));
        }
        let leaf = child(h_children, 0)?;
        body(definitions, leaf, "leaf")?;
        expected.insert(leaf);
        if remaining > 1 {
            let last = body(definitions, child(children, 3)?, "tensor")?;
            index = number(last.field("right")?)? as usize;
        }
    }
    Ok(expected)
}

pub(crate) fn decode_qpe_instrument(
    payload: &[u8],
    request: &[u8],
    candidate: &[u8],
) -> Result<QpeDecoded> {
    let actual = json::parse(payload)?;
    let required = json::parse(request)?;
    let candidate = json::parse(candidate)?;
    actual.fields(&[
        "format",
        "version",
        "profile",
        "preparation",
        "circuit",
        "readout",
    ])?;
    required.fields(&[
        "format",
        "version",
        "profile",
        "preparation",
        "circuit",
        "provider",
        "readout",
        "outputs",
    ])?;
    candidate.fields(&[
        "format",
        "version",
        "profile",
        "provider_proof",
        "hadamards",
        "powers",
        "inverse_fourier",
        "trace_order",
        "power_orders",
        "fourier_order",
    ])?;
    if actual.field("format")?.text()? != "qleisli.instrument-ir"
        || actual.field("version")?.number()? != 1
        || actual.field("profile")?.text()? != "initialize-unitary-readout-v1"
        || required.field("format")?.text()? != "qleisli.qpe-instrument-request"
        || required.field("version")?.number()? != 1
        || required.field("profile")?.text()? != "qpe-dyadic8-v1"
        || candidate.field("format")?.text()? != "qleisli.qpe-instrument-candidate"
        || candidate.field("profile")?.text()? != "qpe-dyadic8-v1"
        || candidate.field("version")?.number()? != 1
    {
        return Err(Error::format(
            "unsupported named QPE format, version or profile",
        ));
    }
    let circuit = required.field("circuit")?;
    circuit.fields(&["interface", "phase", "target", "route", "provider"])?;
    let original = actual.field("circuit")?;
    let original_entry = original.field("entry")?;
    original_entry.fields(&["implementation", "proof"])?;
    let Value::Object(mut provider_graph) = original.clone() else {
        return Err(Error::format("QPE circuit must be an object"));
    };
    provider_graph.insert(
        "entry".into(),
        Value::object([
            ("implementation", circuit.field("provider")?.clone()),
            ("proof", candidate.field("provider_proof")?.clone()),
        ]),
    );
    let provider = decode_request(
        &json::encode(&Value::Object(provider_graph))?,
        &json::encode(required.field("provider")?)?,
    )?;
    if provider.fourier_width.is_some() {
        return Err(Error::format(
            "QPE provider requires an ordinary equation request",
        ));
    }
    let width = circuit.field("phase")?.array()?.len();
    let hadamards = expected_hadamards(original, &candidate, width)?;
    let preparation = actual.field("preparation")?;
    preparation.fields(&["initializations", "outputs"])?;
    let prepare_request = required.field("preparation")?;
    prepare_request.fields(&["inputs", "fresh"])?;
    let readout = actual.field("readout")?;
    readout.fields(&["measurements", "pack", "outputs"])?;
    let readout_request = required.field("readout")?;
    readout_request.fields(&["inputs", "owners", "result"])?;
    let mut w = Writer {
        bytes: b"QLQ1".to_vec(),
        reads: provider.word_count,
        current: 0,
        counts: [0; 4],
        edges: vec![],
        payload_bytes: 0,
    };
    w.word(
        u32::try_from(provider.bridge.len()).map_err(|_| Error::limit("QPE frame exceeds u32"))?,
    )?;
    if w.bytes.len() + provider.bridge.len() > 64 << 20 {
        return Err(Error::limit("combined QPE framing exceeds 64 MiB"));
    }
    w.bytes.extend_from_slice(&provider.bridge);
    w.field(original_entry, "implementation")?;
    w.field(original_entry, "proof")?;
    w.interface(circuit.field("interface")?)?;
    for field in ["phase", "target", "route"] {
        w.numbers(circuit.field(field)?)?;
    }
    w.field(circuit, "provider")?;
    let atom = |w: &mut Writer, v: &Value| -> Result<()> {
        v.fields(&["index", "interface"])?;
        w.field(v, "index")?;
        w.interface(v.field("interface")?)
    };
    w.array(candidate.field("hadamards")?, atom)?;
    w.array(candidate.field("powers")?, atom)?;
    atom(&mut w, candidate.field("inverse_fourier")?)?;
    w.numbers(candidate.field("trace_order")?)?;
    w.array(candidate.field("power_orders")?, Writer::numbers)?;
    w.numbers(candidate.field("fourier_order")?)?;
    w.side(prepare_request.field("inputs")?)?;
    w.side(&Value::object([
        ("quantum", prepare_request.field("fresh")?.clone()),
        ("classical", Value::Array(vec![])),
    ]))?;
    w.array(preparation.field("initializations")?, Writer::definition)?;
    w.side(preparation.field("outputs")?)?;
    w.side(readout_request.field("inputs")?)?;
    w.numbers(readout_request.field("owners")?)?;
    w.field(readout_request, "result")?;
    w.array(readout.field("measurements")?, Writer::definition)?;
    w.numbers(readout.field("pack")?)?;
    w.side(readout.field("outputs")?)?;
    w.side(required.field("outputs")?)?;
    Ok(QpeDecoded {
        provider,
        bridge: w.bytes,
        hadamards,
    })
}
