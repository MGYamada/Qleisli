//! Walk retained typed data and the same actual decoded graph, without JSON.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::interchange::carrier::{Atom, Interface, Origin, Owner, Request};

pub(super) fn origin(view: &mut View<'_>, value: &Origin) -> Result<()> {
    view.record("origin", 3, |w| {
        w.writer.text(&value.module)?;
        w.writer.text(&value.declaration)?;
        w.writer.text(&value.source)
    })
}

pub(super) fn atom(view: &mut View<'_>, value: &Atom) -> Result<()> {
    match value {
        Atom::Unit => view.record("unit", 0, |_| Ok(())),
        Atom::Bit => view.record("bit", 0, |_| Ok(())),
        Atom::Bits(width) => view.record("bits", 1, |w| w.n(*width as usize)),
        Atom::Pair => view.record("pair", 0, |_| Ok(())),
        Atom::Tuple(arity) => view.record("tuple", 1, |w| w.n(*arity as usize)),
        Atom::Enum(source, names) | Atom::Record(source, names) => view.record(
            if matches!(value, Atom::Enum(..)) {
                "enum"
            } else {
                "record"
            },
            2,
            |w| {
                origin(w, source)?;
                w.list(names, |w, name| w.writer.text(name))
            },
        ),
    }
}

fn owner(view: &mut View<'_>, value: &Owner) -> Result<()> {
    view.record("typed-owner", 2, |w| {
        w.port(&value.port)?;
        w.list(&value.basis, atom)
    })
}

fn interface(view: &mut View<'_>, value: &Interface) -> Result<()> {
    view.record("carrier-interface", 3, |w| {
        w.list(&value.inputs, owner)?;
        w.list(&value.outputs, owner)?;
        w.effect(value.public_effect)
    })
}

pub(in crate::interchange) fn complete(graph: Graph<'_>, request: &Request) -> Result<Vec<u8>> {
    let mut writer = Writer {
        bytes: b"QDV1".to_vec(),
        limit: MAX_BYTES,
        depth: 0,
    };
    writer.sized(5, 5)?;
    writer.depth += 1;
    writer.text("finite-carrier-pure-v1")?;
    graph.write(&mut writer)?;
    let mut view = View {
        writer: &mut writer,
        dependencies: &BTreeMap::new(),
    };
    interface(&mut view, &request.attached)?;
    interface(&mut view, &request.required)?;
    view.matrix(&request.logical)?;
    writer.depth -= 1;
    Ok(writer.bytes)
}
