//! Composite framing is untrusted; the native checker binds all three stages.
//! Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

use super::request::BoundDecoded;
use super::{Error, Result, Value, Writer, decode_request, json};

pub(crate) struct InstrumentDecoded {
    pub pure: BoundDecoded,
    pub bridge: Vec<u8>,
}

pub(crate) fn decode_instrument(payload: &[u8], request: &[u8]) -> Result<InstrumentDecoded> {
    let actual = json::parse(payload)?;
    let required = json::parse(request)?;
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
        "readout",
        "outputs",
    ])?;
    for (value, format) in [
        (&actual, "qleisli.instrument-ir"),
        (&required, "qleisli.instrument-request"),
    ] {
        if value.field("format")?.text()? != format
            || value.field("version")?.number()? != 1
            || value.field("profile")?.text()? != "initialize-unitary-readout-v1"
        {
            return Err(Error::format(
                "unsupported instrument format, version or profile",
            ));
        }
    }
    let preparation = actual.field("preparation")?;
    preparation.fields(&["initializations", "outputs"])?;
    let preparation_request = required.field("preparation")?;
    preparation_request.fields(&["inputs", "fresh"])?;
    let readout = actual.field("readout")?;
    readout.fields(&["measurements", "pack", "outputs"])?;
    let readout_request = required.field("readout")?;
    readout_request.fields(&["inputs", "owners", "result"])?;
    let pure = decode_request(
        &json::encode(actual.field("circuit")?)?,
        &json::encode(required.field("circuit")?)?,
    )?;
    if pure.fourier_width.is_some() {
        return Err(Error::format(
            "instrument profile requires an explicit equation request",
        ));
    }
    let mut w = Writer {
        bytes: b"QLI1".to_vec(),
        reads: pure.word_count,
        current: 0,
        counts: [0; 4],
        edges: vec![],
        payload_bytes: 0,
    };
    // One allowance covers this frame and both nested root/artifact frames.
    w.word(
        u32::try_from(pure.bridge.len())
            .map_err(|_| Error::limit("instrument frame exceeds u32"))?,
    )?;
    if w.bytes.len() + pure.bridge.len() > 64 << 20 {
        return Err(Error::limit("combined instrument framing exceeds 64 MiB"));
    }
    w.bytes.extend_from_slice(&pure.bridge);
    w.side(preparation_request.field("inputs")?)?;
    w.side(&Value::object([
        ("quantum", preparation_request.field("fresh")?.clone()),
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
    Ok(InstrumentDecoded {
        pure,
        bridge: w.bytes,
    })
}
