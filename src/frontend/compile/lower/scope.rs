//! Projection from block-local bindings back to the entry scope.
//!
//! `rebound` records direct `let` binders, not quantum slot changes. A new
//! binder can have exactly the old Value (a gate preserves its slot/basis).
//! See the pointwise model in lean/Qleisli/Scope.lean and the refinement ledger.

use std::collections::BTreeSet;

use super::value::{Env, Value};
use crate::frontend::ast::{Pattern, PatternKind, Span};

/// Locate the source binder without changing the ownership/scope projection.
pub(super) fn binding_span(pattern: &Pattern, name: &str) -> Option<Span> {
    let mut pending = vec![pattern];
    while let Some(pattern) = pending.pop() {
        match &pattern.kind {
            PatternKind::Name(ident) if ident.text == name => return Some(ident.span),
            PatternKind::Tuple(a, b) => pending.extend([b.as_ref(), a.as_ref()]),
            _ => {}
        }
    }
    None
}

/// Reject unreturned local quantum owners, then restore the entry scope.
/// Failure leaves `entry` unchanged. The result value and suspended frame are
/// separate holders; this operation never changes the register store or IR.
pub(super) fn close_scope<'a>(
    entry: &mut Env,
    local: &'a Env,
    rebound: &BTreeSet<String>,
) -> Result<(), &'a str> {
    for (name, value) in local {
        if value.as_ref().is_some_and(Value::owns_quantum)
            && (rebound.contains(name) || entry.get(name) != Some(value))
        {
            return Err(name);
        }
    }
    for (name, value) in entry {
        if value.as_ref().is_some_and(Value::owns_quantum)
            && (rebound.contains(name) || local.get(name) != Some(&*value))
        {
            *value = None;
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::compile::Ty;
    use crate::ir::ClassicalId;

    // Unlike the production snapshot algorithm, the oracle keeps explicit
    // lexical identities. Rebinding changes the identity even for equal values.
    #[derive(Clone)]
    struct Binding {
        identity: usize,
        value: Option<Value>,
        linear: bool,
    }

    #[derive(Clone)]
    struct Case {
        entry: Option<Binding>,
        local: Option<Binding>,
    }

    fn cases(slot: u32) -> Vec<Case> {
        let values = [
            (None, false),
            (Some(Value::Unit), false),
            (Some(Value::Classical(ClassicalId(0))), false),
            (
                Some(Value::pair(Value::Unit, Value::Classical(ClassicalId(1)))),
                false,
            ),
            (Some(Value::Quantum(slot, Ty::Unit)), true),
            (Some(Value::Quantum(slot, Ty::Bit)), true),
            (
                Some(Value::pair(
                    Value::Classical(ClassicalId(0)),
                    Value::Quantum(slot, Ty::Unit),
                )),
                true,
            ),
            (
                Some(Value::pair(
                    Value::Quantum(slot, Ty::Unit),
                    Value::Classical(ClassicalId(0)),
                )),
                true,
            ),
        ];
        let entries = std::iter::once(None).chain(values.iter().map(|(value, linear)| {
            Some(Binding {
                identity: 0,
                value: value.clone(),
                linear: *linear,
            })
        }));
        let mut cases = Vec::new();
        for entry in entries {
            // The original binding can survive, or its linear value can move.
            cases.push(Case {
                entry: entry.clone(),
                local: entry.clone(),
            });
            if let Some(binding) = entry.as_ref().filter(|binding| binding.linear) {
                cases.push(Case {
                    entry: entry.clone(),
                    local: Some(Binding {
                        identity: binding.identity,
                        value: None,
                        linear: false,
                    }),
                });
            }
            // Fresh binders include same-value rebinding and a subsequent move
            // (None). Their values may be classical, mixed, or zero-width.
            for (value, linear) in &values {
                cases.push(Case {
                    entry: entry.clone(),
                    local: Some(Binding {
                        identity: 1,
                        value: value.clone(),
                        linear: *linear,
                    }),
                });
            }
        }
        cases
    }

    #[test]
    fn scope_projection_matches_a_finite_lexical_identity_model() {
        let cases_a = cases(0);
        let cases_b = cases(1);
        assert_eq!(cases_a.len() * cases_b.len(), 7_225);
        for a in &cases_a {
            for b in &cases_b {
                let mut entry = Env::new();
                let mut local = Env::new();
                let mut rebound = BTreeSet::new();
                let mut expected = Env::new();
                let mut escaping = None;
                for (name, case) in [("a", a), ("b", b)] {
                    if let Some(binding) = &case.entry {
                        entry.insert(name.to_owned(), binding.value.clone());
                        // An immutable classical binding restores its entry
                        // value. Linear ownership stays only with its original
                        // still-live identity, otherwise it becomes spent.
                        let projected = if binding.linear {
                            case.local.as_ref().and_then(|visible| {
                                (visible.identity == binding.identity)
                                    .then(|| visible.value.clone())
                                    .flatten()
                            })
                        } else {
                            binding.value.clone()
                        };
                        expected.insert(name.to_owned(), projected);
                    }
                    if let Some(binding) = &case.local {
                        local.insert(name.to_owned(), binding.value.clone());
                        if binding.identity == 1 {
                            rebound.insert(name.to_owned());
                            if binding.linear && escaping.is_none() {
                                escaping = Some(name);
                            }
                        }
                    }
                }
                let before = entry.clone();
                let result = close_scope(&mut entry, &local, &rebound);
                if let Some(name) = escaping {
                    assert_eq!(result, Err(name));
                    assert_eq!(entry, before, "rejection must not partly project the scope");
                } else {
                    assert_eq!(result, Ok(()));
                    assert_eq!(entry, expected);
                }
            }
        }
    }
}
