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
    #[cfg(test)]
    Control(&'a BasisType, &'a [usize]),
    ControlOwners(&'a [BasisType], &'a [usize]),
    Instrument {
        actual: &'a Signature,
        expected: &'a Signature,
        identity: (&'a str, &'a str, &'a [(String, String)]),
    },
}

fn write_request(value: Request<'_>, writer: &mut Writer) -> Result<()> {
    let indices = BTreeMap::new();
    let mut view = View {
        writer,
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
        #[cfg(test)]
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
    Ok(())
}

#[cfg(test)]
pub(in crate::interchange) fn request(value: Request<'_>) -> Result<Vec<u8>> {
    let mut writer = Writer {
        bytes: b"QDV1".to_vec(),
        limit: MAX_BYTES,
        depth: 0,
    };
    write_request(value, &mut writer)?;
    Ok(writer.bytes)
}

/// Describe actual request data and both retained runtime graphs with one
/// bounded writer. Independently checked reference data is mandatory for
/// instruments, and no reference slot is inferred from the actual graph.
pub(in crate::interchange) fn complete(
    value: Request<'_>,
    actual: Graph<'_>,
    expected: Option<Graph<'_>>,
) -> Result<Vec<u8>> {
    if matches!(value, Request::Instrument { .. }) != expected.is_some() {
        return Err(Error::format(
            "instrument execution view requires its own reference graph",
        ));
    }
    let indices = BTreeMap::new();
    let mut writer = Writer {
        bytes: b"QDV1".to_vec(),
        limit: MAX_BYTES,
        depth: 0,
    };
    let mut view = View {
        writer: &mut writer,
        dependencies: &indices,
    };
    view.record("native-contract", 3, |w| {
        write_request(value, w.writer)?;
        actual.write(w.writer)?;
        match expected {
            Some(reference) => reference.write(w.writer),
            None => w.writer.append(&[0]),
        }
    })?;
    Ok(writer.bytes)
}

#[cfg(test)]
pub(in crate::interchange) fn circuit(
    value: &Circuit,
    dependencies: &[Arc<FunctionEvidence>],
) -> Result<Vec<u8>> {
    let indices = dependency_indices(dependencies)?;
    let mut writer = Writer {
        bytes: b"QDV1".to_vec(),
        limit: MAX_BYTES,
        depth: 0,
    };
    let mut view = View {
        writer: &mut writer,
        dependencies: &indices,
    };
    view.circuit(value)?;
    Ok(writer.bytes)
}

#[cfg(test)]
mod tests;
