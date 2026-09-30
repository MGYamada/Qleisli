//! Independent request framing and an untrusted graph-pair proposal.
//! Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
use std::collections::BTreeMap;

use super::{Error, Result, Value, Writer, decode, json, number};

pub(super) struct Pair {
    pub actual: usize,
    pub requested: usize,
    pub children: Vec<usize>,
}

pub(crate) struct BoundDecoded {
    pub actual: Value,
    pub request: Value,
    pub pairs: Vec<(usize, usize)>,
    pub bridge: Vec<u8>,
    pub fourier_width: Option<usize>,
    pub word_count: usize,
}

/// Propose a dependency order for only the actual outer routing nodes. This
/// makes no acceptance decision; the fresh Lean cache validates every body.
fn wiring_order(actual: &Value, order: &[usize]) -> Result<Vec<usize>> {
    let definitions = actual.field("definitions")?.array()?;
    let root = number(actual.field("entry")?.field("implementation")?)? as usize;
    let body = definitions[root].field("body")?;
    if body.field("tag")?.text()? != "sequence" {
        return Ok(vec![]);
    }
    let children = body.field("children")?.array()?;
    let mut stack = Vec::new();
    for (i, child) in children.iter().enumerate() {
        if i != 1 {
            stack.push(number(child)? as usize);
        }
    }
    let mut selected = vec![false; definitions.len()];
    while let Some(index) = stack.pop() {
        if selected[index] {
            continue;
        }
        selected[index] = true;
        let body = definitions[index].field("body")?;
        match body.field("tag")?.text()? {
            "sequence" => {
                for child in body.field("children")?.array()? {
                    stack.push(number(child)? as usize);
                }
            }
            "tensor" => {
                stack.push(number(body.field("left")?)? as usize);
                stack.push(number(body.field("right")?)? as usize);
            }
            _ => {}
        }
    }
    Ok(order.iter().copied().filter(|i| selected[*i]).collect())
}

fn children(meaning: &Value) -> Result<Vec<usize>> {
    let body = meaning.field("body")?;
    let fields: &[&str] = match body.field("tag")?.text()? {
        "sequence" => {
            return body
                .field("children")?
                .array()?
                .iter()
                .map(|v| number(v).map(|n| n as usize))
                .collect();
        }
        "tensor" => &["left", "right"],
        "inverse" | "control" | "power" => &["child"],
        "qpe_instrument" => &["provider_meaning"],
        "identity" | "finite" | "rewire" | "structural" | "phase" | "qft" => &[],
        _ => return Err(Error::format("unknown requested meaning body")),
    };
    fields
        .iter()
        .map(|key| number(body.field(key)?).map(|n| n as usize))
        .collect()
}

pub(crate) fn decode_request(payload: &[u8], request: &[u8]) -> Result<BoundDecoded> {
    let decoded = decode(payload)?;
    let required = json::parse(request)?;
    required.fields(&[
        "format",
        "version",
        "profile",
        "kind",
        "effect",
        "interface",
        "meanings",
        "entry",
    ])?;
    if required.field("format")?.text()? != "qleisli.hierarchy-request"
        || required.field("version")?.number()? != 1
        || required.field("profile")?.text()? != "qpe-dyadic8-v1"
    {
        return Err(Error::format(
            "unsupported hierarchy request format, version or profile",
        ));
    }
    let requested = required.field("meanings")?.array()?;
    if requested.is_empty() || requested.len() > 100_000 {
        return Err(Error::limit("requested meanings require 1..=100000 nodes"));
    }
    let mut w = Writer {
        bytes: b"QLR1".to_vec(),
        reads: 0,
        current: 0,
        counts: [0, requested.len(), 0, 0],
        edges: vec![vec![]; requested.len()],
        payload_bytes: 0,
    };
    w.word(decoded.bridge.len() as u32)?;
    if w.bytes.len() + decoded.bridge.len() > 64 << 20 {
        return Err(Error::limit(
            "combined hierarchy request framing exceeds 64 MiB",
        ));
    }
    w.bytes.extend_from_slice(&decoded.bridge);
    w.word(match required.field("kind")?.text()? {
        "equation" => 0,
        "instrument" => 1,
        _ => return Err(Error::format("unknown requested proof kind")),
    })?;
    w.word(match required.field("effect")?.text()? {
        "unitary" => 0,
        "iso" => 1,
        "observe" => 2,
        _ => return Err(Error::format("unknown requested effect")),
    })?;
    w.interface(required.field("interface")?)?;
    w.word(requested.len() as u32)?;
    for (i, meaning) in requested.iter().enumerate() {
        w.current = i;
        w.meaning(meaning)?;
    }
    let entry = number(required.field("entry")?)? as usize;
    if entry >= requested.len() {
        return Err(Error::new(
            "invalid_ir",
            "requested entry outside its table",
        ));
    }
    w.word(entry as u32)?;
    // Reject cycles in the requested table before proposing node pairs.
    w.schedule()?;
    if requested[entry].field("body")?.field("tag")?.text()? == "qft" {
        if requested.len() != 1
            || entry != 0
            || required.field("kind")?.text()? != "equation"
            || required.field("effect")?.text()? != "unitary"
            || requested[0].field("interface")? != required.field("interface")?
        {
            return Err(Error::new(
                "contract",
                "Fourier request requires one matching unitary equation",
            ));
        }
        let width = number(requested[0].field("body")?.field("width")?)? as usize;
        w.bytes[..4].copy_from_slice(b"QLF1");
        let order = wiring_order(&decoded.value, &decoded.definition_order)?;
        w.word(order.len() as u32)?;
        for index in order {
            w.word(index as u32)?;
        }
        return Ok(BoundDecoded {
            actual: decoded.value,
            request: required,
            pairs: vec![],
            bridge: w.bytes,
            fourier_width: Some(width),
            word_count: w.reads + decoded.word_count,
        });
    }
    let actual = decoded.value.field("meanings")?.array()?;
    let proof = number(decoded.value.field("entry")?.field("proof")?)? as usize;
    let root = number(decoded.value.field("proofs")?.array()?[proof].field("meaning")?)? as usize;
    let mut pairs = vec![Pair {
        actual: root,
        requested: entry,
        children: vec![],
    }];
    let mut indices = BTreeMap::from([((root, entry), 0)]);
    let mut index = 0;
    let mut edges = 0usize;
    while index < pairs.len() {
        let pair = &pairs[index];
        let a = children(&actual[pair.actual])?;
        let r = children(&requested[pair.requested])?;
        if a.len() != r.len() {
            return Err(Error::new(
                "contract",
                "requested meaning has different child arity",
            ));
        }
        edges += a.len();
        if edges > 1_000_000 {
            return Err(Error::limit("requested graph pairing exceeds edge limit"));
        }
        let mut child_pairs = Vec::with_capacity(a.len());
        for (a, r) in a.into_iter().zip(r) {
            let next = if let Some(existing) = indices.get(&(a, r)) {
                *existing
            } else {
                if pairs.len() == 100_000 {
                    return Err(Error::limit("requested graph pairing exceeds node limit"));
                }
                let next = pairs.len();
                pairs.push(Pair {
                    actual: a,
                    requested: r,
                    children: vec![],
                });
                indices.insert((a, r), next);
                next
            };
            child_pairs.push(next);
        }
        pairs[index].children = child_pairs;
        index += 1;
    }
    w.word(pairs.len() as u32)?;
    for pair in &pairs {
        w.word(pair.actual as u32)?;
        w.word(pair.requested as u32)?;
        w.word(pair.children.len() as u32)?;
        for child in &pair.children {
            w.word(*child as u32)?;
        }
    }
    w.edges = pairs.iter().map(|p| p.children.clone()).collect();
    let order = w.schedule()?;
    w.word(order.len() as u32)?;
    for i in order {
        w.word(i as u32)?;
    }
    Ok(BoundDecoded {
        actual: decoded.value,
        request: required,
        pairs: pairs.into_iter().map(|p| (p.actual, p.requested)).collect(),
        bridge: w.bytes,
        fourier_width: None,
        word_count: w.reads + decoded.word_count,
    })
}
