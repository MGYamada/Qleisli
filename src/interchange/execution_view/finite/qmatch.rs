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
    writer.sized(5, 4)?;
    writer.depth += 1;
    writer.text(crate::interchange::qmatch::PROFILE)?;
    graph.write(&mut writer)?;
    let mut view = View {
        writer: &mut writer,
        dependencies: &BTreeMap::new(),
    };
    view.record("source-function", 2, |w| {
        w.writer.text(&request.source.module)?;
        w.writer.text(&request.source.function)
    })?;
    view.list(&request.sites, |w, site| {
        w.record("qmatch-site", 4, |w| {
            carrier::interface(w, &site.attached)?;
            carrier::interface(w, &site.required)?;
            w.record("source-interval", 3, |w| {
                w.n(site.position.offset as usize)?;
                w.n(site.position.start as usize)?;
                w.n(site.position.count as usize)
            })?;
            w.list(&site.arms, |w, arm| {
                w.record("qmatch-arm", 2, |w| {
                    w.n(arm.evidence as usize)?;
                    w.n(arm.controlled as usize)
                })
            })
        })
    })?;
    writer.depth -= 1;
    Ok(writer.bytes)
}
