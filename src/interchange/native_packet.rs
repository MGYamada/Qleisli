//! QLV2 external framing; original profile bytes stay immutable inner inputs.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::{Error, Result};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub(super) enum Scope {
    Inspection,
    Execution,
    Caller,
}

impl Scope {
    pub(super) fn name(self) -> &'static str {
        match self {
            Self::Inspection => "inspection",
            Self::Execution => "execution",
            Self::Caller => "caller",
        }
    }
}

pub(super) struct View<'a> {
    pub(super) graph: &'a [u8],
    pub(super) caller: Option<(&'a [u8], &'a [usize])>,
}

pub(super) struct Caller {
    pub(super) bytes: Vec<u8>,
    pub(super) indices: Vec<usize>,
}

pub(super) fn encode(original: &[u8], view: Option<View<'_>>) -> Result<(Vec<u8>, Scope)> {
    let (scope, graph, caller, indices) = match view {
        None => (Scope::Inspection, &[][..], &[][..], &[][..]),
        Some(View {
            graph,
            caller: None,
        }) if !graph.is_empty() => (Scope::Execution, graph, &[][..], &[][..]),
        Some(View {
            graph,
            caller: Some((caller, indices)),
        }) if !graph.is_empty() && !caller.is_empty() => (Scope::Caller, graph, caller, indices),
        _ => return Err(Error::format("native execution views must be nonempty")),
    };
    // Bound each component before arithmetic and allocation.
    if original.is_empty()
        || original.len() > 64 << 20
        || graph.len() > 64 << 20
        || caller.len() > 64 << 20
        || indices.len() > 100_000
        || graph.len() + caller.len() > super::execution_view::MAX_BYTES
    {
        return Err(Error::limit("native envelope exceeds component limits"));
    }
    let total = 24 + original.len() + graph.len() + caller.len() + 4 * indices.len();
    if total > 64 << 20 {
        return Err(Error::limit("native envelope exceeds 64 MiB"));
    }
    let mut packet = Vec::with_capacity(total);
    packet.extend_from_slice(b"QLV2");
    for field in [
        scope as usize,
        original.len(),
        graph.len(),
        caller.len(),
        indices.len(),
    ] {
        packet.extend_from_slice(&(field as u32).to_le_bytes());
    }
    packet.extend_from_slice(original);
    packet.extend_from_slice(graph);
    packet.extend_from_slice(caller);
    for index in indices {
        let index =
            u32::try_from(*index).map_err(|_| Error::limit("native alias index exceeds u32"))?;
        packet.extend_from_slice(&index.to_le_bytes());
    }
    Ok((packet, scope))
}
