//! Walk the retained graph and ordinary-result metadata, without JSON replay.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::interchange::ordinary_root::{Request, Storage};

pub(super) fn storage(view: &mut View<'_>, value: &Storage) -> Result<()> {
    match value {
        Storage::Unit => view.record("unit", 0, |_| Ok(())),
        Storage::Bit(id) => view.record("bit", 1, |w| w.n(id.0 as usize)),
        Storage::Bits(ids) => view.record("bits", 1, |w| w.list(ids, |w, id| w.n(id.0 as usize))),
        Storage::Enum(origin, ids) => view.record("enum", 2, |w| {
            carrier::origin(w, origin)?;
            w.list(ids, |w, id| w.n(id.0 as usize))
        }),
        Storage::Pair(a, b) => view.record("pair", 2, |w| {
            storage(w, a)?;
            storage(w, b)
        }),
        Storage::Tuple(fields) => view.record("tuple", 1, |w| w.list(fields, storage)),
        Storage::Record(origin, fields) => view.record("record", 2, |w| {
            carrier::origin(w, origin)?;
            w.list(fields, |w, (name, value)| {
                w.record("field", 2, |w| {
                    w.writer.text(name)?;
                    storage(w, value)
                })
            })
        }),
    }
}

pub(in crate::interchange) fn complete(graph: Graph<'_>, request: &Request) -> Result<Vec<u8>> {
    let mut writer = Writer {
        bytes: b"QDV1".to_vec(),
        limit: MAX_BYTES,
        depth: 0,
    };
    writer.sized(5, 11)?;
    writer.depth += 1;
    writer.text("finite-ordinary-root-v2")?;
    graph.write(&mut writer)?;
    let mut view = View {
        writer: &mut writer,
        dependencies: &BTreeMap::new(),
    };
    view.writer.text(request.selection.name())?;
    view.writer.text(&request.module)?;
    view.writer.text(&request.declaration)?;
    view.list(&request.parameters, |w, basis| w.list(basis, carrier::atom))?;
    view.list(&request.input_storage, storage)?;
    view.list(&request.input_rows, |w, row| {
        w.list(row, |w, bit| w.boolean(*bit))
    })?;
    view.list(&request.basis, carrier::atom)?;
    storage(&mut view, &request.storage)?;
    view.effect(request.public_effect)?;
    writer.depth -= 1;
    Ok(writer.bytes)
}
