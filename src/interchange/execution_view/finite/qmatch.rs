//! Walk the exact retained graph and named-arm request; no JSON replay.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::interchange::qmatch::Request;

pub(in crate::interchange) fn complete(graph: Graph<'_>, request: &Request) -> Result<Vec<u8>> {
    let mut writer = Writer {
        bytes: b"QDV1".to_vec(),
        limit: MAX_BYTES,
        depth: 0,
    };
    writer.sized(5, 6)?;
    writer.depth += 1;
    writer.text(crate::interchange::qmatch::PROFILE)?;
    graph.write(&mut writer)?;
    let mut view = View {
        writer: &mut writer,
        dependencies: &BTreeMap::new(),
    };
    carrier::interface(&mut view, &request.attached)?;
    carrier::interface(&mut view, &request.required)?;
    view.record("source-focus", 3, |w| {
        w.writer.text(&request.source.module)?;
        w.writer.text(&request.source.function)?;
        w.n(request.source.offset as usize)
    })?;
    view.list(&request.arms, |w, arm| {
        w.record("qmatch-arm", 2, |w| {
            w.n(arm.evidence as usize)?;
            w.n(arm.controlled as usize)
        })
    })?;
    writer.depth -= 1;
    Ok(writer.bytes)
}
