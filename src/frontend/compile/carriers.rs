//! Reuse immutable type descriptions inside one original-source compilation.
//! This caches proposal data only. Native type/code checks still run afresh.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;
use crate::interchange::carrier::Atom;

fn copy_cells(atoms: &[Atom]) -> usize {
    atoms.iter().fold(atoms.len(), |total, atom| {
        total.saturating_add(match atom {
            Atom::Enum(_, names) | Atom::Record(_, names) => {
                names.iter().map(|name| name.len() + 1).sum()
            }
            _ => 0,
        })
    })
}

impl Compiler<'_> {
    pub(super) fn carrier_description(
        &mut self,
        module: &str,
        span: Span,
        ty: &Ty,
    ) -> Result<Vec<Atom>, CompileError> {
        let mut work = self.work;
        let result = (|| {
            // Full tree equality, including original identities, member order
            // and zero-width nodes. Shared origins alone do not identify a tree.
            if ty.basis_bits().is_none() {
                for (original, atoms) in &self.carrier_descriptions {
                    if original.equivalent_by_budgeted(
                        ty,
                        &mut |a, b| Ok::<_, CompileError>(a == b),
                        &mut |cells| self.charge_at(&mut work, module, span, cells),
                    )? {
                        self.charge_at(&mut work, module, span, copy_cells(atoms))?;
                        return Ok((atoms.clone(), false));
                    }
                }
            }
            let atoms =
                crate::frontend::specialize::carrier_description_budgeted(ty, &mut |_, cells| {
                    self.charge_at(&mut work, module, span, cells)
                        .map_err(|error| Error::new("limit", span, error.to_string()))
                })
                .map_err(|error| {
                    self.error(
                        module,
                        span,
                        if error.code == "limit" {
                            ErrorCode::Limit
                        } else {
                            ErrorCode::Unsupported
                        },
                        error.to_string(),
                    )
                })?;
            if ty.basis_bits().is_none() {
                // Atom copies share the immutable Arc<Origin>; label strings
                // and the full cache key remain charged before allocation.
                self.charge_at(
                    &mut work,
                    module,
                    span,
                    operations::port_copy_nodes(ty) + copy_cells(&atoms) + 1,
                )?;
            }
            Ok((atoms, ty.basis_bits().is_none()))
        })();
        self.work = work;
        let (atoms, insert) = result?;
        if insert {
            self.carrier_descriptions.push((ty.clone(), atoms.clone()));
        }
        Ok(atoms)
    }
}
