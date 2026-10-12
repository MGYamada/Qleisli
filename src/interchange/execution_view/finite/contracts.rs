//! Describe actual typed obligations independently of native-request JSON.
//! This data walker does not confer acceptance or an execution handle.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::interchange::finite_leaf::UnitaryBoundary;
use crate::interchange::pure_leaf::PureBoundary;

pub(in crate::interchange) enum Request<'a> {
    Encoded(&'a Contract),
    Leaf(&'a UnitaryBoundary, &'a Matrix),
    PureLeaf(&'a PureBoundary, &'a Matrix),
    Control(&'a BasisType, &'a [usize]),
    ControlOwners(&'a [BasisType], &'a [usize]),
    Instrument {
        actual: &'a Signature,
        expected: &'a Signature,
        identity: (&'a str, &'a str, &'a [(String, String)]),
    },
}

pub(in crate::interchange) fn request(value: Request<'_>) -> Result<Vec<u8>> {
    let indices = BTreeMap::new();
    let mut view = View {
        writer: Writer {
            bytes: b"QDV1".to_vec(),
            limit: MAX_BYTES,
            depth: 0,
        },
        dependencies: &indices,
    };
    match value {
        Request::Encoded(contract) => view.record("encoded", 1, |w| w.contract(contract))?,
        Request::Leaf(boundary, required) => view.record("leaf", 4, |w| {
            w.basis(boundary.signature())?;
            w.port(boundary.input())?;
            w.port(boundary.output())?;
            w.matrix(required)
        })?,
        Request::PureLeaf(boundary, required) => view.record("pure-leaf", 5, |w| {
            w.basis(boundary.domain())?;
            w.basis(boundary.codomain())?;
            w.port(boundary.input())?;
            w.port(boundary.output())?;
            w.matrix(required)
        })?,
        Request::Control(signature, axes) => view.record("control", 2, |w| {
            w.basis(signature)?;
            w.axes(axes)
        })?,
        Request::ControlOwners(signatures, axes) => view.record("control-owners", 2, |w| {
            w.list(signatures, View::basis)?;
            w.axes(axes)
        })?,
        Request::Instrument {
            actual,
            expected,
            identity,
        } => view.record("instrument", 3, |w| {
            w.signature(actual)?;
            w.signature(expected)?;
            w.identity(identity)
        })?,
    }
    Ok(view.writer.bytes)
}

pub(in crate::interchange) fn circuit(
    value: &Circuit,
    dependencies: &[Arc<FunctionEvidence>],
) -> Result<Vec<u8>> {
    let indices = dependency_indices(dependencies)?;
    let mut view = View {
        writer: Writer {
            bytes: b"QDV1".to_vec(),
            limit: MAX_BYTES,
            depth: 0,
        },
        dependencies: &indices,
    };
    view.circuit(value)?;
    Ok(view.writer.bytes)
}

#[cfg(test)]
mod tests;
