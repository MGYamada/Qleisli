//! Reserve the complete retained runtime object before nested JSON copies.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::interchange::{ordinary_root, runtime_root};

fn origin(value: &crate::interchange::carrier::Origin, remaining: &mut usize) -> Result<()> {
    for text in [&value.module, &value.declaration, &value.source] {
        charge(remaining, text.len().saturating_mul(6).saturating_add(32))?;
    }
    Ok(())
}

fn ordinary(value: &ordinary_root::Storage, remaining: &mut usize) -> Result<()> {
    use ordinary_root::Storage::*;
    let mut pending = vec![value];
    while let Some(value) = pending.pop() {
        charge(remaining, 128)?;
        match value {
            Unit | Bit(_) => {}
            Bits(ids) => charge(remaining, ids.len().saturating_mul(24))?,
            Pair(first, second) => pending.extend([first.as_ref(), second.as_ref()]),
            Tuple(fields) => pending.extend(fields),
            Enum(identity, ids) => {
                origin(identity, remaining)?;
                charge(remaining, ids.len().saturating_mul(24))?;
            }
            Record(identity, fields) => {
                origin(identity, remaining)?;
                for (name, value) in fields {
                    charge(remaining, name.len().saturating_mul(6).saturating_add(32))?;
                    pending.push(value);
                }
            }
        }
    }
    Ok(())
}

pub(super) fn bounded(value: &runtime_root::Request, remaining: &mut usize) -> Result<()> {
    value.preflight()?;
    charge(remaining, 2048usize.saturating_add(
        value.module.len().saturating_add(value.declaration.len()).saturating_mul(6)))?;
    for (name, basis) in &value.static_bases {
        charge(remaining, name.len().saturating_mul(6).saturating_add(64))?;
        basis_storage(basis, remaining)?;
    }
    for (name, _) in &value.static_naturals {
        charge(remaining, name.len().saturating_mul(6).saturating_add(64))?;
    }
    for atom in value.parameters.iter().flatten().chain(&value.result) {
        match atom {
            runtime_root::Atom::Finite(atom) => basis_storage(std::slice::from_ref(atom), remaining)?,
            runtime_root::Atom::Quantum => charge(remaining, 64)?,
        }
    }
    for atom in value.input_storage.iter().flatten().chain(&value.storage) {
        charge(remaining, 128)?;
        match atom {
            runtime_root::Storage::Ordinary(basis, stored) => {
                basis_storage(basis, remaining)?;
                ordinary(stored, remaining)?;
            }
            runtime_root::Storage::Quantum(owner) => {
                basis_storage(&owner.basis, remaining)?;
                charge(remaining, owner.port.wires.len().saturating_mul(24))?;
            }
            runtime_root::Storage::Tuple(_) => {}
        }
    }
    for row in &value.input_rows {
        charge(remaining, 64usize.saturating_add(row.len().saturating_mul(8)))?;
    }
    Ok(())
}
