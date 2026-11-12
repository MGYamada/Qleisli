//! Propose actual result storage to the fresh native ordinary-root gate.
//! The common source judgment remains separate from source preservation.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::frontend::types::nominal::Body;
use crate::interchange::carrier::{Atom, Origin};
use crate::interchange::native::Proposal;
use crate::interchange::ordinary_root::{Request, Selection, Storage};

pub(super) type NativeResult<T> = std::result::Result<T, crate::interchange::Error>;
fn invalid(message: impl Into<String>) -> crate::interchange::Error {
    crate::interchange::Error::new("format", message)
}
fn limit(message: impl Into<String>) -> crate::interchange::Error {
    crate::interchange::Error::new("limit", message)
}

// Untrusted preparation only: native Lean independently enumerates the original
// finite code and rejects any different/subset/permuted proposed rows.
pub(super) fn proposed_rows(parameters: &[Vec<Atom>]) -> NativeResult<Vec<Vec<bool>>> {
    let (width, labels) = proposed_codes(parameters)?;
    Ok(labels
        .into_iter()
        .map(|label| (0..width).map(|axis| ((label >> axis) & 1) != 0).collect())
        .collect())
}

pub(super) use crate::frontend::ordinary::proposed_codes;

pub(super) fn has_nominal(ty: &Ty) -> bool {
    match &ty.kind {
        Kind::Nominal(_) => true,
        Kind::Q(inner) => has_nominal(inner),
        Kind::Tuple(fields) => fields.iter().any(has_nominal),
        _ => false,
    }
}

fn nominal_origin(ty: &Ty) -> NativeResult<Arc<Origin>> {
    let Kind::Nominal(nominal) = &ty.kind else {
        return Err(invalid("ordinary storage lost its nominal type"));
    };
    Ok(Arc::new(Origin {
        module: nominal.origin.module.clone(),
        declaration: nominal.origin.name.clone(),
        source: nominal.origin.source.to_string(),
    }))
}

pub(super) fn storage(value: &Value) -> NativeResult<Storage> {
    Ok(match value {
        Value::Unit => Storage::Unit,
        Value::EmptyBits => Storage::Bits(vec![]),
        Value::Classical(id) => Storage::Bit(*id),
        Value::Bits(ids) => Storage::Bits(ids.clone()),
        Value::Enumeration(ty, ids) => Storage::Enum(nominal_origin(ty)?, ids.clone()),
        Value::Pair(a, b) => Storage::Pair(Box::new(storage(a)?), Box::new(storage(b)?)),
        Value::Tuple(fields) => {
            Storage::Tuple(fields.iter().map(storage).collect::<NativeResult<_>>()?)
        }
        Value::Record(ty, children) => {
            let Kind::Nominal(nominal) = &ty.kind else {
                return Err(invalid("record lost nominal type"));
            };
            let Body::Record(fields) = &nominal.body else {
                return Err(invalid("record has enum type"));
            };
            if fields.len() != children.len() {
                return Err(invalid("record storage arity"));
            }
            Storage::Record(
                nominal_origin(ty)?,
                fields
                    .iter()
                    .zip(children)
                    .map(|(field, value)| Ok((field.name.clone(), storage(value)?)))
                    .collect::<NativeResult<_>>()?,
            )
        }
        Value::Quantum(..) => {
            return Err(crate::interchange::Error::new(
                "unsupported",
                "ordinary-result root cannot return a quantum owner",
            ));
        }
    })
}

pub(super) fn accept(
    lower: &mut Lowerer<'_, '_>,
    key: &Key,
    parameters: &[Ty],
    input_storage: Vec<Storage>,
    result: &Value,
    raw: &RawProgram,
) -> NativeResult<AcceptedProgram> {
    use crate::interchange::Error;
    let decl = lower.compiler.declarations[key];
    let name = lower
        .compiler
        .source
        .resolution
        .declaration(*key)
        .name
        .clone();
    if !raw.quantum_inputs.is_empty()
        || !raw.quantum_outputs.is_empty()
        || !decl.static_params.is_empty()
    {
        return Err(Error::new(
            "unsupported",
            "typed ordinary native root requires ordinary ports and closed static parameters",
        ));
    }
    let mut describe = |ty: &Ty| {
        crate::frontend::specialize::carrier_description_budgeted(ty, &mut |_, cells| {
            lower
                .compiler
                .charge(&name.0, decl.span, cells)
                .map_err(|e| {
                    crate::frontend::compile::Error::new("limit", decl.span, e.to_string())
                })
        })
        .map_err(|e| Error::new(e.code, e.to_string()))
    };
    let parameters = parameters
        .iter()
        .map(&mut describe)
        .collect::<NativeResult<Vec<_>>>()?;
    let basis = describe(&result.ty())?;
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
                .saturating_add(64 * 6),
        )
        .map_err(|e| limit(e.to_string()))?;
    let input_rows = proposed_rows(&parameters)?;
    let storage_work = result
        .tree_size()
        .nodes
        .saturating_add(result.nominal_equality_work());
    lower
        .compiler
        .charge(&name.0, decl.span, storage_work)
        .map_err(|e| limit(e.to_string()))?;
    let stored = storage(result)?;
    let mut names = BTreeSet::from([name.0.clone()]);
    for atom in parameters.iter().flatten().chain(&basis) {
        if let Atom::Enum(origin, _) | Atom::Record(origin, _) = atom {
            names.insert(origin.module.clone());
        }
    }
    let rows = if lower.nominal_modules.borrow().is_subset(&names) {
        lower
            .compiler
            .retained_ordinary_type_sources(*key, &name.0, decl.span)
    } else {
        lower
            .compiler
            .retained_runtime_body_sources(*key, &name.0, decl.span, raw)
    }
    .map_err(|e| Error::new(e.code.as_str(), e.to_string()))?;
    let bytes = rows.iter().map(|r| r.0.len() + r.1.len()).sum::<usize>();
    lower
        .compiler
        .charge(&name.0, decl.span, bytes)
        .map_err(|e| limit(e.to_string()))?;
    let sources = rows
        .iter()
        .map(|row| row.as_ref().clone())
        .collect::<Vec<_>>();
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
        parameters,
        input_storage,
        input_rows,
        basis,
        storage: stored,
        public_effect: {
            let fact = lower.compiler.source.effects[key];
            fact.public_effect()
                .or(fact.asserted())
                .unwrap_or(fact.inferred())
        },
    };
    let bytes = request.encode()?;
    let proposed = Proposal::from_raw_with_sources(
        raw,
        None,
        crate::interchange::Version::V2,
        None,
        &sources,
    )?;
    let checked = lower
        .compiler
        .kernel
        .check_ordinary_root(proposed.artifact(), &bytes)?;
    lower
        .compiler
        .exact_work
        .charge(checked.native_exact_work())
        .map_err(|e| limit(e.to_string()))?;
    Ok(checked.into_program())
}
