//! Closed substitutions of common checked interfaces; no second source judgment.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.

use super::{BasisBinding, Error, OperationBinding, ParsedProgram, Result, Span};
use crate::frontend::check::{Interface, StaticKind, type_size_budgeted};
use crate::frontend::resolve::{DefId, Failure};
use std::collections::{BTreeMap, BTreeSet};

fn check_bindings<V>(
    actual: &BTreeMap<String, V>,
    expected: &BTreeSet<&str>,
    category: &str,
    subject: &str,
    span: Span,
    charge: &mut impl FnMut(Span, usize) -> Result<()>,
) -> Result<()> {
    crate::frontend::closed::check_named_bindings_budgeted(
        actual,
        expected,
        category,
        subject,
        span,
        &mut |span, cells| charge(span, cells).map_err(crate::frontend::check::SourceError::from),
    )
    .map_err(Error::from)
}

fn visible_definition<'a>(
    program: &'a ParsedProgram,
    path: &str,
    requester: Option<&str>,
    span: Span,
) -> Result<(DefId, &'a Interface)> {
    let resolution = &program.checked.resolution;
    let id = resolution.qualified(path).map_err(|kind| {
        let mut error = ParsedProgram::resolution_error(Failure {
            module: String::new(),
            span,
            kind,
        });
        error.module = None;
        error
    })?;
    let interface = program.checked.interfaces.get(&id).ok_or_else(|| {
        Error::new(
            "static",
            span,
            "a static Nat helper cannot be a runtime entry or operation provider",
        )
        .in_module(&resolution.declaration(id).name.0)
    })?;
    if !resolution.visible(id, requester.and_then(|name| resolution.module(name))) {
        return Err(
            Error::new("visibility", span, format!("dependency {path} is private"))
                .in_module(requester.unwrap_or(&interface.module)),
        );
    }
    if !program.checked.effects.contains_key(&id) {
        return Err(Error::new(
            "type",
            span,
            "entry or provider must be an ordinary runtime function",
        )
        .in_module(&interface.module));
    }
    Ok((id, interface))
}

/// Selected-source capacity remains outside the profile-neutral closer.
pub(super) fn closed_interface_budgeted(
    program: &ParsedProgram,
    id: DefId,
    types: &BTreeMap<String, BasisBinding>,
    naturals: &BTreeMap<String, u32>,
    subject: &str,
    span: Span,
    mut charge: impl FnMut(Span, usize) -> Result<()>,
) -> Result<crate::frontend::closed::ClosedInterface> {
    for binding in types.values() {
        super::basis_binding::validate(binding, program, &mut charge)?;
    }
    let mut source_charge =
        |span, cells| charge(span, cells).map_err(crate::frontend::check::SourceError::from);
    let checked = crate::frontend::closed::CheckedInterface::original(
        &program.checked,
        id,
        span,
        &mut source_charge,
    )
    .map_err(Error::from)?;
    let substitution = crate::frontend::closed::ClosedSubstitution::named_budgeted(
        checked,
        types,
        naturals,
        |basis| &basis.ty,
        subject,
        &mut source_charge,
    )
    .map_err(Error::from)?;
    crate::frontend::closed::close_interface_budgeted(
        substitution,
        subject,
        source_charge,
        |ty, span| {
            super::elaborate::concrete_capacity(ty, span)
                .map_err(crate::frontend::check::SourceError::from)
        },
    )
    .map_err(Error::from)
}

/// A host binding names a public provider from outside the source module.
/// The explicitly supported private binding remains governed by the entry's
/// module visibility; it cannot be used to sharpen a public provider contract.
pub(super) fn host_provider_effect(
    program: &ParsedProgram,
    entry: DefId,
    provider: DefId,
    span: Span,
) -> Result<crate::ir::Effect> {
    let resolution = &program.checked.resolution;
    let context = if resolution.declaration(provider).public {
        crate::frontend::effects::EffectContext::External
    } else {
        crate::frontend::effects::EffectContext::Module(resolution.declaration(entry).module)
    };
    crate::frontend::effects::effect_at(resolution, &program.checked.effects, context, provider)
        .ok_or_else(|| {
            Error::new(
                "effect",
                span,
                "provider has no visible checked source effect",
            )
        })
}

pub(super) fn instantiate(
    program: &ParsedProgram,
    entry: &str,
    types: &BTreeMap<String, BasisBinding>,
    naturals: &BTreeMap<String, u32>,
    operations: &BTreeMap<String, OperationBinding>,
    require_entry_projection: bool,
) -> Result<(DefId, BTreeMap<String, DefId>)> {
    let (entry_id, interface) = visible_definition(program, entry, None, Span::default())?;
    let resolution = &program.checked.resolution;
    let original = &program
        .syntax(&interface.module)
        .expect("retained original")
        .decls[interface.ast_index];
    let span = original.span;
    let mut remaining = 100_000usize;
    let mut charge = |span, cells| {
        remaining = remaining.checked_sub(cells).ok_or_else(|| {
            Error::new(
                "limit",
                span,
                "closed preparation exceeds 100000 concrete cells",
            )
        })?;
        Ok(())
    };
    let result = (|| {
        let closed = closed_interface_budgeted(
            program,
            entry_id,
            types,
            naturals,
            &format!("entry {entry}"),
            span,
            &mut charge,
        )?;
        charge(span, interface.statics.len())?;
        let expected = interface
            .statics
            .iter()
            .filter_map(|formal| {
                matches!(formal.kind, StaticKind::Operation { .. })
                    .then_some(formal.key.name.as_str())
            })
            .collect();
        check_bindings(
            operations,
            &expected,
            "operation",
            &format!("entry {entry}"),
            span,
            &mut charge,
        )?;
        let mut providers = BTreeMap::new();
        let mut nested_operation_provider = false;
        for formal in &interface.statics {
            if let StaticKind::Operation { meaning, .. } = &formal.kind {
                let binding = &operations[&formal.key.name];
                let (provider_id, provider) = visible_definition(
                    program,
                    &binding.definition,
                    Some(&interface.module),
                    span,
                )?;
                charge(span, provider.statics.len())?;
                nested_operation_provider |= provider
                    .statics
                    .iter()
                    .any(|p| matches!(p.kind, StaticKind::Operation { .. }));
                let provider_closed = closed_interface_budgeted(
                    program,
                    provider_id,
                    &binding.types,
                    &binding.naturals,
                    &format!(
                        "operation {} provider {}",
                        formal.key.name, binding.definition
                    ),
                    span,
                    &mut charge,
                )?;
                let effect = host_provider_effect(program, entry_id, provider_id, span)?;
                let required = &closed.operations[&formal.key];
                if effect > required.ceiling() {
                    return Err(Error::new(
                        "effect",
                        span,
                        if required.ceiling() == crate::ir::Effect::Unitary {
                            crate::frontend::effects::unitary_required(&format!(
                                "operation provider {} has caller-visible effect `{effect:?}`; Unitary is required",
                                resolution.path(provider_id)
                            ))
                        } else {
                            format!(
                                "pure operation provider {} has caller-visible effect `{effect:?}`; at most Isometry is required",
                                resolution.path(provider_id)
                            )
                        },
                    ));
                }
                if provider_closed.parameters.len() != 1
                    || !provider_closed.parameters[0].is_quantum_owner()
                    || !provider_closed.result.is_quantum_owner()
                {
                    return Err(Error::new(
                        "type",
                        span,
                        "concrete provider must have one quantum input with the exact output type",
                    ));
                }
                if provider_closed.parameters[0] != required.input
                    || &provider_closed.result != required.output()
                {
                    return Err(Error::new(
                        "type",
                        span,
                        "concrete provider type or tuple/size shape mismatch",
                    ));
                }
                if let Some(meaning_id) = meaning {
                    let target = program.meaning_targets.get(meaning_id).ok_or_else(|| {
                        Error::new("meaning", span, "missing original Meaning target")
                    })?;
                    charge(span, target.cells())?;
                    type_size_budgeted(&target.basis, 4096, 64, true, span, &mut |s, n| {
                        charge(s, n).map_err(crate::frontend::check::SourceError::from)
                    })
                    .map_err(Error::from)?;
                    let crate::frontend::types::Kind::Q(basis) = &provider_closed.result.kind
                    else {
                        unreachable!("quantum provider checked above")
                    };
                    if **basis != target.codomain
                        || provider_closed.parameters[0].quantum_basis() != Some(&target.basis)
                    {
                        return Err(Error::new(
                            "type",
                            span,
                            "provider and Meaning have different exact basis trees",
                        ));
                    }
                    // This checks the requested interface only. All original
                    // bindings need native comparison before hierarchy lowering.
                }
                charge(span, formal.key.name.len() + 1)?;
                providers.insert(formal.key.name.clone(), provider_id);
            }
        }
        if nested_operation_provider {
            return Err(Error::new(
                "unsupported",
                span,
                "concrete providers with operation parameters are unsupported",
            ));
        }
        // Check every closed binding before any requested body eligibility.
        // An unsupported entry/body cannot mask an invalid supplied provider.
        if require_entry_projection {
            program.definition(entry_id)?;
        }
        for provider_id in providers.values() {
            program.definition(*provider_id)?;
        }
        Ok((entry_id, providers))
    })();
    result.map_err(|e| e.in_module(&interface.module))
}

#[cfg(test)]
mod visibility_tests {
    use super::*;

    #[test]
    fn private_definitions_remain_visible_in_their_own_module() {
        let program = ParsedProgram::parse(
            crate::edition::Edition::E2026,
            BTreeMap::from([(
                "local".into(),
                "unitary fn f(q: Q<Bit>) -> Q<Bit> { q }".into(),
            )]),
        )
        .unwrap();
        let span = Span::default();
        assert!(visible_definition(&program, "local::f", Some("local"), span).is_ok());
        for requester in [None, Some("other")] {
            assert_eq!(
                visible_definition(&program, "local::f", requester, span)
                    .unwrap_err()
                    .code(),
                "visibility"
            );
        }
    }
}
