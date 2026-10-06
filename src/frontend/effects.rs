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
    pub unitary: BTreeMap<DefId, Span>,
}

impl BodyEffects {
    pub fn new(span: Span) -> Self {
        Self {
            local: Effect::Unitary,
            origin: span,
            calls: BTreeMap::new(),
            unitary: BTreeMap::new(),
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
        self.unitary.entry(id).or_insert(span);
    }

    pub fn storage_cells(&self) -> usize {
        1 + self.calls.len() + self.unitary.len()
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
        for (id, span) in &body.unitary {
            self.require_unitary(*id, *span);
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
