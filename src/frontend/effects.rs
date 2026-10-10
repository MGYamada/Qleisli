//! Principal source effects from typed bodies, never acceptance or Meaning evidence.
//!
//! Both typed consumers use the same lattice, fact and assertion rule. A source
//! annotation is not an inference seed. Facts become public only after the
//! owning source preparation has completed its checks.

use std::collections::{BTreeMap, BTreeSet};

use super::ast::{FnKind, Span};
use super::resolve::DefId;
use crate::ir::Effect;

/// Checked source classification of quantum action at fixed ordinary inputs.
/// This is interface metadata, not an accepted handle or a preservation proof.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FunctionEffect {
    inferred: Effect,
    asserted: Option<Effect>,
}

impl FunctionEffect {
    pub fn inferred(self) -> Effect {
        self.inferred
    }

    pub fn asserted(self) -> Option<Effect> {
        self.asserted
    }

    pub(super) fn checked(kind: FnKind, inferred: Effect) -> Option<Self> {
        let asserted = assertion(kind);
        asserted
            .is_none_or(|bound| inferred <= bound)
            .then_some(Self { inferred, asserted })
    }
}

pub(super) fn assertion(kind: FnKind) -> Option<Effect> {
    match kind {
        FnKind::Unitary => Some(Effect::Unitary),
        FnKind::Iso => Some(Effect::Iso),
        FnKind::Observe => Some(Effect::Observe),
        FnKind::Static | FnKind::Inferred | FnKind::Classical | FnKind::Meaning => None,
    }
}

/// An annotation cannot claim an externally justified effect in place of the
/// supported compositional body rules. Keep both typed consumers' explanation
/// identical and independent of the development tracker.
const EXTERNAL_UNITARY_UNSUPPORTED: &str = "Semantic error: \"externally unitary\" is not supported; an external unitarity claim cannot override the effect inferred from the body";

pub(super) fn unitary_required(context: &str) -> String {
    format!("{context}. {EXTERNAL_UNITARY_UNSUPPORTED}")
}

pub(super) fn assertion_error(name: &str, kind: FnKind, inferred: Effect) -> String {
    let asserted = assertion(kind).expect("failed source effect assertion");
    format!(
        "body effect `{inferred:?}` exceeds asserted `{asserted:?}` effect of `{name}`. \
         {EXTERNAL_UNITARY_UNSUPPORTED}"
    )
}

/// Typed local rules and actual ordinary calls. Names/type widths alone add
/// nothing. Repeated call sites retain the first location and one graph edge.
#[derive(Clone, Debug)]
pub(super) struct BodyEffects {
    local: Effect,
    origin: Span,
    calls: BTreeMap<DefId, Span>,
    required: BTreeMap<DefId, (Effect, Span)>,
}

impl BodyEffects {
    pub fn new(span: Span) -> Self {
        Self {
            local: Effect::Unitary,
            origin: span,
            calls: BTreeMap::new(),
            required: BTreeMap::new(),
        }
    }

    pub fn add(&mut self, effect: Effect, span: Span) {
        if effect > self.local {
            self.local = effect;
            self.origin = span;
        }
    }

    pub fn call(&mut self, id: DefId, span: Span) {
        self.calls.entry(id).or_insert(span);
    }

    pub fn require_unitary(&mut self, id: DefId, span: Span) {
        self.require_effect(id, Effect::Unitary, span);
    }

    /// Requirements are upper bounds, so repeated demands meet at the stricter
    /// ceiling. They never seed, lower or replace principal effect inference.
    pub(super) fn require_effect(&mut self, id: DefId, ceiling: Effect, span: Span) {
        self.required
            .entry(id)
            .and_modify(|(previous, origin)| {
                if ceiling < *previous {
                    *previous = ceiling;
                    *origin = span;
                }
            })
            .or_insert((ceiling, span));
    }

    pub(super) fn first_violation(
        &self,
        inferred: &BTreeMap<DefId, Effect>,
    ) -> Option<(Effect, Span)> {
        self.required.iter().find_map(|(id, &(ceiling, span))| {
            inferred
                .get(id)
                .is_none_or(|actual| *actual > ceiling)
                .then_some((ceiling, span))
        })
    }

    pub fn storage_cells(&self) -> usize {
        1 + self.calls.len() + self.required.len()
    }

    pub fn inferred_with(&self, effects: &BTreeMap<DefId, Effect>) -> Option<Effect> {
        self.calls.keys().try_fold(self.local, |effect, id| {
            effects.get(id).map(|callee| effect.max(*callee))
        })
    }

    /// The caller charges storage before copying these collection-local edges.
    pub fn merge(&mut self, body: &Self) {
        self.add(body.local, body.origin);
        for (id, span) in &body.calls {
            self.call(*id, *span);
        }
        for (id, (ceiling, span)) in &body.required {
            self.require_effect(*id, *ceiling, *span);
        }
    }

    pub fn origin(&self, effects: &BTreeMap<DefId, Effect>) -> Span {
        let strongest = self
            .calls
            .keys()
            .map(|id| effects[id])
            .fold(self.local, Effect::max);
        self.calls
            .iter()
            .find(|(id, _)| effects[id] == strongest && strongest > self.local)
            .map_or(self.origin, |(_, span)| *span)
    }
}

/// Least solution of the finite monotone call graph. Existing type/termination
/// checking decides which graphs are admitted; solving a cycle cannot admit it.
/// Each node rises at most twice, so edge propagation is bounded by the typed
/// graph rather than repeated full-project scans or a recursion-depth guess.
/// Charge actual graph storage and propagation before each operation. Capacity
/// failure is separate from a missing typed callee; neither becomes a fact.
pub(super) fn infer_with<E>(
    bodies: &BTreeMap<DefId, BodyEffects>,
    mut charge: impl FnMut(Span, usize) -> Result<(), E>,
) -> Result<Option<BTreeMap<DefId, Effect>>, E> {
    let mut effects = BTreeMap::new();
    for (id, body) in bodies {
        charge(body.origin, 1)?;
        effects.insert(*id, body.local);
    }
    let mut users = BTreeMap::<DefId, BTreeSet<DefId>>::new();
    for (id, body) in bodies {
        for (callee, span) in &body.calls {
            charge(*span, 1)?;
            if !bodies.contains_key(callee) {
                return Ok(None);
            }
            charge(*span, usize::from(!users.contains_key(callee)) + 1)?;
            users.entry(*callee).or_default().insert(*id);
        }
    }
    let mut pending = BTreeSet::new();
    for (id, body) in bodies {
        charge(body.origin, 1)?;
        pending.insert(*id);
    }
    while let Some(callee) = pending.pop_first() {
        charge(bodies[&callee].origin, 1)?;
        for caller in users.get(&callee).into_iter().flatten() {
            let span = bodies[caller].calls[&callee];
            charge(span, 1)?;
            let joined = effects[caller].max(effects[&callee]);
            if joined > effects[caller] {
                charge(span, 1 + usize::from(!pending.contains(caller)))?;
                effects.insert(*caller, joined);
                pending.insert(*caller);
            }
        }
    }
    Ok(Some(effects))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::{parser::parse_module, resolve::Resolution};

    fn provider() -> DefId {
        let module = parse_module("fn provider(q:Q<Bit>)->Q<Bit>{q}").unwrap();
        Resolution::new([("main", &module)])
            .unwrap()
            .qualified("main::provider")
            .unwrap()
    }

    #[test]
    fn provider_ceilings_meet_without_replacing_principal_effects() {
        let id = provider();
        let iso_span = Span::new(10, 20);
        let unitary_span = Span::new(30, 40);
        for (first, second, expected, origin) in [
            (Effect::Iso, Effect::Unitary, Effect::Unitary, unitary_span),
            (Effect::Unitary, Effect::Iso, Effect::Unitary, iso_span),
            (Effect::Iso, Effect::Iso, Effect::Iso, iso_span),
        ] {
            let mut body = BodyEffects::new(Span::default());
            body.require_effect(id, first, iso_span);
            body.require_effect(id, second, unitary_span);
            assert_eq!(body.required[&id], (expected, origin));
            assert_eq!(body.storage_cells(), 2);
            for actual in [Effect::Unitary, Effect::Iso, Effect::Observe] {
                let inferred = BTreeMap::from([(id, actual)]);
                assert_eq!(body.first_violation(&inferred).is_some(), actual > expected);
            }
            assert_eq!(
                body.first_violation(&BTreeMap::new()),
                Some((expected, origin))
            );
        }
        let mut actual = BodyEffects::new(iso_span);
        actual.add(Effect::Iso, iso_span);
        let modules =
            parse_module("fn provider(q:Q<Bit>)->Q<Bit>{q} fn caller(q:Q<Bit>)->Q<Bit>{q}")
                .unwrap();
        let resolution = Resolution::new([("main", &modules)]).unwrap();
        let caller_id = resolution.qualified("main::caller").unwrap();
        // DefId is collection-local; obtain the provider from this same collection.
        let id = resolution.qualified("main::provider").unwrap();
        let mut caller = BodyEffects::new(Span::default());
        caller.call(id, iso_span);
        caller.require_unitary(id, unitary_span);
        let inferred = infer_with(
            &BTreeMap::from([(id, actual), (caller_id, caller.clone())]),
            |_, _| Ok::<(), ()>(()),
        )
        .unwrap()
        .unwrap();
        assert_eq!(inferred[&caller_id], Effect::Iso);
        assert_eq!(
            caller.first_violation(&inferred),
            Some((Effect::Unitary, unitary_span))
        );
    }

    #[test]
    fn merging_regions_keeps_the_strictest_original_provider_demand() {
        let id = provider();
        let first = Span::new(10, 20);
        let second = Span::new(30, 40);
        let mut outer = BodyEffects::new(first);
        outer.require_effect(id, Effect::Iso, first);
        let mut region = BodyEffects::new(second);
        region.require_unitary(id, second);
        region.add(Effect::Observe, second);
        outer.merge(&region);
        assert_eq!(outer.required[&id], (Effect::Unitary, second));
        assert_eq!(outer.inferred_with(&BTreeMap::new()), Some(Effect::Observe));
        assert_eq!(outer.origin(&BTreeMap::new()), second);
        assert_eq!(outer.storage_cells(), 2);
    }
}
