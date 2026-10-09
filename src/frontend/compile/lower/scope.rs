//! Projection from block-local bindings back to the entry scope.
//!
//! Production keys include structural BinderId, so rebinding changes the key
//! even when a gate preserves its slot/basis. `rebound` also supports the
//! historical name-keyed comparison model below; production passes it empty.
//! See the pointwise model in lean/Qleisli/Scope.lean and the refinement ledger.

use std::collections::{BTreeMap, BTreeSet};

use super::value::{Binding, Value};
/// Reject unreturned local quantum owners, then restore the entry scope.
/// Failure leaves `entry` unchanged. The result value and suspended frame are
/// separate holders; this operation never changes the register store or IR.
pub(super) fn close_scope<'a, K: Ord>(
    entry: &mut BTreeMap<K, Binding>,
    local: &'a BTreeMap<K, Binding>,
    rebound: &BTreeSet<K>,
) -> Result<(), &'a K> {
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
            *value = Binding::Consumed;
        }
    }
    Ok(())
}

/// Align only explicitly updated lexical owners before the existing closure
/// check. Fresh/shadowed bindings and changed interfaces are never replacements.
/// Rejection leaves the caller's entry snapshot unchanged.
pub(super) fn close_scope_with_updates<K: Ord + Clone>(
    entry: &mut BTreeMap<K, Binding>,
    local: &BTreeMap<K, Binding>,
    updates: &BTreeSet<K>,
) -> Result<(), K> {
    if updates.is_empty() {
        return close_scope(entry, local, &BTreeSet::new()).map_err(Clone::clone);
    }
    let mut aligned = entry.clone();
    for name in updates {
        let Some(original) = entry.get(name) else {
            continue;
        };
        let (Some(old), Some(new)) = (original.as_ref(), local.get(name).and_then(Binding::as_ref))
        else {
            // A subsequently consumed owner remains spent at scope closure.
            if matches!(local.get(name), Some(Binding::Consumed)) {
                continue;
            }
            return Err(name.clone());
        };
        if !old.owns_quantum() || !new.owns_quantum() || old.ty() != new.ty() {
            return Err(name.clone());
        }
        aligned.insert(name.clone(), Binding::Live(new.clone()));
    }
    close_scope(&mut aligned, local, &BTreeSet::new()).map_err(Clone::clone)?;
    *entry = aligned;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::compile::Ty;
    use crate::ir::ClassicalId;

    #[test]
    fn authorized_update_survives_and_later_consumption_stays_spent() {
        let original = Binding::Live(Value::quantum(0, Ty::bit()));
        let updated = Binding::Live(Value::quantum(1, Ty::bit()));
        let updates = BTreeSet::from(["q"]);
        let mut entry = BTreeMap::from([("q", original.clone())]);
        let local = BTreeMap::from([("q", updated.clone())]);
        assert_eq!(
            close_scope_with_updates(&mut entry, &local, &updates),
            Ok(())
        );
        assert_eq!(entry["q"], updated);
        let local = BTreeMap::from([("q", Binding::Consumed)]);
        assert_eq!(
            close_scope_with_updates(&mut entry, &local, &updates),
            Ok(())
        );
        assert_eq!(entry["q"], Binding::Consumed);
        assert!(
            close_scope_with_updates(&mut entry, &BTreeMap::from([("q", original)]), &updates)
                .is_err()
        );
        assert_eq!(entry["q"], Binding::Consumed);
    }

    #[test]
    fn update_cannot_change_interface_hide_owner_or_admit_fresh_shadow() {
        let original = BTreeMap::from([("q", Binding::Live(Value::quantum(0, Ty::bit())))]);
        for local in [
            BTreeMap::from([("q", Binding::Live(Value::quantum(1, Ty::unit())))]),
            BTreeMap::new(),
            BTreeMap::from([
                ("q", Binding::Live(Value::quantum(1, Ty::bit()))),
                ("shadow", Binding::Live(Value::quantum(2, Ty::bit()))),
            ]),
        ] {
            let mut entry = original.clone();
            assert!(
                close_scope_with_updates(&mut entry, &local, &BTreeSet::from(["q", "shadow"]))
                    .is_err()
            );
            assert_eq!(entry, original);
        }
    }

    // Compare the historical name-keyed projection to explicit lexical IDs.
    // Production now includes that source identity in its map keys as well.
    #[derive(Clone)]
    struct LexicalBinding {
        identity: usize,
        value: Option<Value>,
        linear: bool,
    }

    #[derive(Clone)]
    struct Case {
        entry: Option<LexicalBinding>,
        local: Option<LexicalBinding>,
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
            (Some(Value::quantum(slot, Ty::unit())), true),
            (Some(Value::quantum(slot, Ty::bit())), true),
            (
                Some(Value::pair(
                    Value::Classical(ClassicalId(0)),
                    Value::quantum(slot, Ty::unit()),
                )),
                true,
            ),
            (
                Some(Value::pair(
                    Value::quantum(slot, Ty::unit()),
                    Value::Classical(ClassicalId(0)),
                )),
                true,
            ),
        ];
        let entries = std::iter::once(None).chain(values.iter().map(|(value, linear)| {
            Some(LexicalBinding {
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
                    local: Some(LexicalBinding {
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
                    local: Some(LexicalBinding {
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
        let slot = |value: Option<Value>| value.map_or(Binding::Consumed, Binding::Live);
        let cases_a = cases(0);
        let cases_b = cases(1);
        assert_eq!(cases_a.len() * cases_b.len(), 7_225);
        for a in &cases_a {
            for b in &cases_b {
                let mut entry = BTreeMap::new();
                let mut local = BTreeMap::new();
                let mut rebound = BTreeSet::new();
                let mut expected = BTreeMap::new();
                let mut identity_entry = BTreeMap::new();
                let mut identity_local = BTreeMap::new();
                let mut identity_expected = BTreeMap::new();
                let mut escaping = None;
                for (name, case) in [("a", a), ("b", b)] {
                    if let Some(binding) = &case.entry {
                        entry.insert(name.to_owned(), slot(binding.value.clone()));
                        identity_entry
                            .insert((name, binding.identity), slot(binding.value.clone()));
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
                        identity_expected.insert((name, binding.identity), slot(projected.clone()));
                        expected.insert(name.to_owned(), slot(projected));
                    }
                    if let Some(binding) = &case.local {
                        local.insert(name.to_owned(), slot(binding.value.clone()));
                        identity_local
                            .insert((name, binding.identity), slot(binding.value.clone()));
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
                let identity_before = identity_entry.clone();
                let identity_result =
                    close_scope(&mut identity_entry, &identity_local, &BTreeSet::new());
                if let Some(name) = escaping {
                    assert_eq!(result.map_err(String::as_str), Err(name));
                    assert_eq!(entry, before, "rejection must not partly project the scope");
                    assert_eq!(identity_result.map_err(|key| *key), Err((name, 1)));
                    assert_eq!(identity_entry, identity_before);
                } else {
                    assert_eq!(result, Ok(()));
                    assert_eq!(entry, expected);
                    assert_eq!(identity_result, Ok(()));
                    assert_eq!(identity_entry, identity_expected);
                }
            }
        }
    }
}
