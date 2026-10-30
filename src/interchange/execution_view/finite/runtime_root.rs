//! Walk the actual retained mixed type/storage forest, without JSON replay.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::interchange::runtime_root::{Atom, Request, Storage};

fn atom(view: &mut View<'_>, value: &Atom) -> Result<()> {
    match value {
        Atom::Finite(node) => view.record("finite", 1, |w| carrier::atom(w, node)),
        Atom::Quantum => view.record("quantum", 0, |_| Ok(())),
    }
}

fn storage(view: &mut View<'_>, value: &Storage) -> Result<()> {
    match value {
        Storage::Ordinary(basis, stored) => view.record("ordinary", 2, |w| {
            w.list(basis, carrier::atom)?;
            ordinary_root::storage(w, stored)
        }),
        Storage::Quantum(owner) => view.record("quantum", 1, |w| carrier::owner(w, owner)),
        Storage::Tuple(arity) => view.record("tuple", 1, |w| w.n(*arity as usize)),
    }
}

pub(in crate::interchange) fn complete(graph: Graph<'_>, request: &Request) -> Result<Vec<u8>> {
    request.preflight()?;
    let mut writer = Writer {
        bytes: b"QDV1".to_vec(),
        limit: MAX_BYTES,
        depth: 0,
    };
    writer.sized(5, 11)?;
    writer.depth += 1;
    writer.text("finite-runtime-root-v1")?;
    graph.write(&mut writer)?;
    let mut view = View {
        writer: &mut writer,
        dependencies: &BTreeMap::new(),
    };
    view.writer.text(request.selection.name())?;
    view.writer.text(&request.module)?;
    view.writer.text(&request.declaration)?;
    view.list(&request.parameters, |w, tree| w.list(tree, atom))?;
    view.list(&request.input_storage, |w, tree| w.list(tree, storage))?;
    view.list(&request.input_rows, |w, row| {
        w.list(row, |w, bit| w.boolean(*bit))
    })?;
    view.list(&request.result, atom)?;
    view.list(&request.storage, storage)?;
    view.effect(request.public_effect)?;
    writer.depth -= 1;
    Ok(writer.bytes)
}
