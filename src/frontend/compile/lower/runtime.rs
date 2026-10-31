//! Propose full source types and actual storage through the common Raw emitter.
//! Native runtime-root checking alone grants acceptance; this is no body proof.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::interchange::carrier::{Atom as BasisAtom, Owner};
use crate::interchange::native::Proposal;
use crate::interchange::ordinary_root::Selection;
use crate::interchange::runtime_root::{Atom, Request, Storage};
use ordinary::NativeResult;

fn failure(error: CompileError) -> crate::interchange::Error {
    crate::interchange::Error::new("limit", error.to_string())
}

fn describe(lower: &mut Lowerer<'_, '_>, key: Key, ty: &Ty) -> NativeResult<Vec<BasisAtom>> {
    let name = lower
        .compiler
        .source
        .resolution
        .declaration(key)
        .name
        .0
        .clone();
    let span = lower.compiler.declarations[&key].span;
    lower
        .compiler
        .carrier_description(&name, span, ty)
        .map_err(failure)
}

fn type_tree(lower: &mut Lowerer<'_, '_>, key: Key, ty: &Ty) -> NativeResult<Vec<Atom>> {
    let name = lower
        .compiler
        .source
        .resolution
        .declaration(key)
        .name
        .0
        .clone();
    let span = lower.compiler.declarations[&key].span;
    lower
        .compiler
        .charge(&name, span, ty.tree_size().nodes.saturating_mul(2))
        .map_err(failure)?;
    if !ty.linear() {
        return Ok(describe(lower, key, ty)?
            .into_iter()
            .map(Atom::Finite)
            .collect());
    }
    let mut tree = Vec::new();
    match &ty.kind {
        Kind::Q(basis) => {
            tree.push(Atom::Quantum);
            tree.extend(describe(lower, key, basis)?.into_iter().map(Atom::Finite));
        }
        Kind::Tuple(fields) => {
            tree.push(Atom::Finite(if fields.len() == 2 {
                BasisAtom::Pair
            } else {
                BasisAtom::Tuple(fields.len() as u32)
            }));
            for field in fields {
                tree.extend(type_tree(lower, key, field)?);
            }
        }
        _ => unreachable!("checked linear type"),
    }
    Ok(tree)
}

fn storage(
    lower: &mut Lowerer<'_, '_>,
    key: Key,
    value: &Value,
    registers: &BTreeMap<Slot, Register>,
) -> NativeResult<Vec<Storage>> {
    let name = lower
        .compiler
        .source
        .resolution
        .declaration(key)
        .name
        .0
        .clone();
    let span = lower.compiler.declarations[&key].span;
    lower
        .compiler
        .charge(
            &name,
            span,
            value
                .tree_size()
                .nodes
                .saturating_mul(2)
                .saturating_add(value.nominal_copy_work()),
        )
        .map_err(failure)?;
    if !value.owns_quantum() {
        return Ok(vec![Storage::Ordinary(
            describe(lower, key, &value.ty())?,
            ordinary::storage(value)?,
        )]);
    }
    let mut tree = Vec::new();
    match value {
        Value::Quantum(slot, _) => {
            let register = registers.get(slot).ok_or_else(|| {
                crate::interchange::Error::new("format", "runtime storage lost its actual owner")
            })?;
            tree.push(Storage::Quantum(Owner {
                port: QuantumPort {
                    token: register.token,
                    wires: register.wires.clone(),
                    shape: BasisShape {
                        bits: register.wires.len() as u8,
                    },
                },
                basis: describe(lower, key, &register.basis)?,
            }));
        }
        Value::Pair(a, b) => {
            tree.push(Storage::Tuple(2));
            tree.extend(storage(lower, key, a, registers)?);
            tree.extend(storage(lower, key, b, registers)?);
        }
        Value::Tuple(fields) => {
            tree.push(Storage::Tuple(fields.len() as u32));
            for field in fields {
                tree.extend(storage(lower, key, field, registers)?);
            }
        }
        _ => unreachable!("checked quantum value"),
    }
    Ok(tree)
}

pub(super) struct Inputs {
    values: Vec<Value>,
    registers: BTreeMap<Slot, Register>,
}

// Snapshot before expansion consumes the argument values/registers. No carrier
// descriptor or six-bit profile is imposed unless the root needs typed checking.
pub(super) fn inputs(
    lower: &mut Lowerer<'_, '_>,
    key: Key,
    values: &[Value],
) -> Result<Inputs, CompileError> {
    let name = lower
        .compiler
        .source
        .resolution
        .declaration(key)
        .name
        .0
        .clone();
    let span = lower.compiler.declarations[&key].span;
    let cost = total_size(values.iter().map(|value| {
        value
            .tree_size()
            .nodes
            .saturating_add(value.nominal_copy_work())
    }))
    .saturating_add(total_size(lower.raw.registers.values().map(|register| {
        register
            .size()
            .saturating_add(crate::frontend::compile::operations::port_copy_nodes(
                &register.basis,
            ))
    })));
    lower.compiler.charge(&name, span, cost)?;
    Ok(Inputs {
        values: values.to_vec(),
        registers: lower.raw.registers.clone(),
    })
}

pub(super) fn accept(
    lower: &mut Lowerer<'_, '_>,
    key: &Key,
    parameters: &[Ty],
    inputs: Inputs,
    result: &Value,
    raw: &RawProgram,
) -> NativeResult<AcceptedProgram> {
    let decl = lower.compiler.declarations[key];
    let name = lower
        .compiler
        .source
        .resolution
        .declaration(*key)
        .name
        .clone();
    let instance = lower
        .compiler
        .concrete_context
        .current
        .clone()
        .ok_or_else(|| {
            crate::interchange::Error::new(
                "format",
                "typed runtime root lost its original instance",
            )
        })?;
    if instance.definition != *key || !instance.operations.is_empty() {
        return Err(crate::interchange::Error::new(
            "unsupported",
            "typed runtime root requires its original Basis/Nat instance without operation formals",
        ));
    }
    let mut static_bases = Vec::new();
    let mut static_naturals = Vec::new();
    for (formal, basis) in &instance.interface.bases {
        lower
            .compiler
            .charge(&name.0, decl.span, formal.name.len() + 1)
            .map_err(failure)?;
        static_bases.push((formal.name.clone(), describe(lower, *key, basis)?));
    }
    for (formal, value) in &instance.interface.naturals {
        lower
            .compiler
            .charge(&name.0, decl.span, formal.name.len() + 1)
            .map_err(failure)?;
        static_naturals.push((formal.name.clone(), *value));
    }
    lower
        .compiler
        .charge(
            &name.0,
            decl.span,
            total_size(parameters.iter().map(|ty| ty.tree_size().nodes))
                .saturating_mul(3)
                .saturating_add(result.tree_size().nodes.saturating_mul(3))
                .saturating_add(result.nominal_copy_work())
                .saturating_add(total_size(lower.raw.registers.values().map(|register| {
                    register.size().saturating_add(
                        crate::frontend::compile::operations::port_copy_nodes(&register.basis),
                    )
                }))),
        )
        .map_err(failure)?;
    let parameters = parameters
        .iter()
        .map(|ty| type_tree(lower, *key, ty))
        .collect::<NativeResult<Vec<_>>>()?;
    let input_storage = inputs
        .values
        .iter()
        .map(|value| storage(lower, *key, value, &inputs.registers))
        .collect::<NativeResult<Vec<_>>>()?;
    let result_type = type_tree(lower, *key, &result.ty())?;
    let registers = lower.raw.registers.clone();
    let stored = storage(lower, *key, result, &registers)?;
    let mut ordinary = Vec::new();
    let mut names = BTreeSet::from([name.0.clone()]);
    for atom in parameters.iter().flatten().chain(&result_type) {
        if let Atom::Finite(BasisAtom::Enum(origin, _) | BasisAtom::Record(origin, _)) = atom {
            names.insert(origin.module.clone());
        }
    }
    for atom in static_bases.iter().flat_map(|(_, basis)| basis) {
        if let BasisAtom::Enum(origin, _) | BasisAtom::Record(origin, _) = atom {
            names.insert(origin.module.clone());
        }
    }
    if !lower.nominal_modules.borrow().is_subset(&names) {
        return Err(crate::interchange::Error::new(
            "unsupported",
            "intermediate nominal source modules require complete typed dependency transport",
        ));
    }
    lower
        .compiler
        .charge(
            &name.0,
            decl.span,
            parameters
                .iter()
                .map(Vec::len)
                .sum::<usize>()
                .saturating_add(parameters.len() + 1)
                .saturating_mul(65)
                + 64 * 6,
        )
        .map_err(failure)?;
    for node in input_storage.iter().flatten() {
        if let Storage::Ordinary(basis, _) = node {
            ordinary.push(basis.clone());
        }
    }
    let input_rows = ordinary::proposed_rows(&ordinary)?;
    let rows = lower
        .compiler
        .retained_ordinary_type_sources(*key, &name.0, decl.span)
        .map_err(failure)?;
    lower
        .compiler
        .charge(
            &name.0,
            decl.span,
            rows.iter().map(|row| row.0.len() + row.1.len()).sum(),
        )
        .map_err(failure)?;
    let sources = rows
        .iter()
        .map(|row| row.as_ref().clone())
        .collect::<Vec<_>>();
    let fact = lower.compiler.source.effects[key];
    let request = Request {
        selection: if lower.compiler.selected_entry == Some(*key) {
            Selection::Exported
        } else if name.0 == "main" && name.1 == "main" {
            Selection::Project
        } else if !decl.public {
            Selection::Internal
        } else {
            Selection::Exported
        },
        module: name.0,
        declaration: name.1,
        static_bases,
        static_naturals,
        parameters,
        input_storage,
        input_rows,
        result: result_type,
        storage: stored,
        public_effect: fact
            .public_effect()
            .or(fact.asserted())
            .unwrap_or(fact.inferred()),
    };
    let bytes = request.encode()?;
    let proposal = Proposal::from_raw_with_sources(
        raw,
        None,
        crate::interchange::Version::V2,
        None,
        &sources,
    )?;
    let checked = lower
        .compiler
        .kernel
        .check_runtime_root(proposal.artifact(), &bytes)?;
    lower
        .compiler
        .exact_work
        .charge(checked.native_exact_work())
        .map_err(|e| crate::interchange::Error::new("limit", e.to_string()))?;
    Ok(checked.into_program())
}
