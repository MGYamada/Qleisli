//! Principal source effects from typed bodies, never acceptance or Meaning evidence.
//!
//! Both typed consumers use the same lattice, fact and assertion rule. A source
//! annotation is not an inference seed. Facts become public only after the
//! owning source preparation has completed its checks.

use std::collections::BTreeMap;
#[cfg(test)]
use std::collections::BTreeSet;

use super::ast::{FnKind, Span};
use super::resolve::{DefId, ModuleId, Resolution};
use crate::ir::Effect;

/// Checked source classification of quantum action at fixed ordinary inputs.
/// This is interface metadata, not an accepted handle or a preservation proof.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FunctionEffect {
    inferred: Effect,
    asserted: Option<Effect>,
    public: Option<Effect>,
    quantum: bool,
}

impl FunctionEffect {
    pub fn inferred(self) -> Effect {
        self.inferred
    }

    pub fn asserted(self) -> Option<Effect> {
        self.asserted
    }

    /// Checked exported contract, never a substitute for implementation checking.
    /// Private declarations and temporary concrete assertion facts have none.
    pub fn public_effect(self) -> Option<Effect> {
        self.public
    }

    /// Internal typed quantum use, including zero-width owners and checked callees.
    /// External callers use the stable permission of an explicit public effect
    /// prefix, not this implementation diagnostic.
    pub fn uses_quantum(self) -> bool {
        self.quantum
    }

    /// Check a concrete expansion's assertion only. This creates no exported
    /// source contract; completed declarations use `checked_declaration`.
    pub(super) fn checked(kind: FnKind, inferred: Effect) -> Option<Self> {
        let asserted = assertion(kind);
        asserted
            .is_none_or(|bound| inferred <= bound)
            .then_some(Self {
                inferred,
                asserted,
                public: None,
                quantum: false,
            })
    }

    pub(super) fn checked_declaration(
        kind: FnKind,
        public: bool,
        uses_quantum: bool,
        inferred: Effect,
    ) -> Result<Self, DeclarationEffectError> {
        let mut fact =
            Self::checked(kind, inferred).ok_or(DeclarationEffectError::ContradictoryBound)?;
        let quantum = uses_quantum || inferred != Effect::Unitary;
        if public && quantum && fact.asserted.is_none() {
            return Err(DeclarationEffectError::MissingPublicAnnotation);
        }
        fact.public = public.then_some(fact.asserted.unwrap_or(inferred));
        fact.quantum = quantum;
        Ok(fact)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum DeclarationEffectError {
    MissingPublicAnnotation,
    ContradictoryBound,
}

/// Context belongs to the actual immutable source collection. Host-selected
/// public providers use External, not a claimed same-module caller identity.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum EffectContext {
    Module(ModuleId),
    External,
}

pub(super) fn effect_at(
    resolution: &Resolution,
    facts: &BTreeMap<DefId, FunctionEffect>,
    context: EffectContext,
    callee: DefId,
) -> Option<Effect> {
    let fact = facts.get(&callee)?;
    match context {
        EffectContext::Module(module) if module == resolution.declaration(callee).module => {
            Some(fact.inferred())
        }
        EffectContext::Module(_) | EffectContext::External => fact.public_effect(),
    }
}

pub(super) fn assertion(kind: FnKind) -> Option<Effect> {
    match kind {
        FnKind::Unitary => Some(Effect::Unitary),
        FnKind::Isometry => Some(Effect::Isometry),
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
    quantum: bool,
    origin: Span,
    calls: BTreeMap<DefId, Span>,
    required: BTreeMap<DefId, (Effect, Span)>,
}

impl BodyEffects {
    pub fn new(span: Span) -> Self {
        Self {
            local: Effect::Unitary,
            quantum: false,
            origin: span,
            calls: BTreeMap::new(),
            required: BTreeMap::new(),
        }
    }

    pub fn add(&mut self, effect: Effect, span: Span) {
        self.quantum |= effect != Effect::Unitary;
        if effect > self.local {
            self.local = effect;
            self.origin = span;
        }
    }

    pub fn mark_quantum(&mut self) {
        self.quantum = true;
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

    #[cfg(test)]
    pub(super) fn first_violation(
        &self,
        inferred: &BTreeMap<DefId, Effect>,
    ) -> Option<(Effect, Span)> {
        self.first_violation_using(|id| inferred.get(&id).copied())
    }

    pub(super) fn first_violation_using(
        &self,
        mut lookup: impl FnMut(DefId) -> Option<Effect>,
    ) -> Option<(Effect, Span)> {
        self.required.iter().find_map(|(id, &(ceiling, span))| {
            lookup(*id)
                .is_none_or(|actual| actual > ceiling)
                .then_some((ceiling, span))
        })
    }

    pub fn storage_cells(&self) -> usize {
        1 + self.calls.len() + self.required.len()
    }

    #[cfg(test)]
    pub fn inferred_with(&self, effects: &BTreeMap<DefId, Effect>) -> Option<Effect> {
        self.inferred_using(|id| effects.get(&id).copied())
    }

    pub(super) fn inferred_using(
        &self,
        mut lookup: impl FnMut(DefId) -> Option<Effect>,
    ) -> Option<Effect> {
        self.calls.keys().try_fold(self.local, |effect, id| {
            lookup(*id).map(|callee| effect.max(callee))
        })
    }

    /// Dependencies have already completed their independent body and bound
    /// checks. The only admitted back edge is a checked decreasing self-call;
    /// joining the node with itself does not change its least effect or use.
    pub(super) fn inferred_from<E>(
        &self,
        owner: DefId,
        resolution: &Resolution,
        facts: &BTreeMap<DefId, FunctionEffect>,
        mut charge: impl FnMut(Span, usize) -> Result<(), E>,
    ) -> Result<Option<(Effect, bool, Span)>, E> {
        let owner_module = resolution.declaration(owner).module;
        let context = EffectContext::Module(owner_module);
        let mut inferred = self.local;
        let mut quantum = self.quantum;
        let mut origin = self.origin;
        for (callee, span) in &self.calls {
            charge(*span, 2)?;
            if *callee == owner {
                continue;
            }
            let Some(effect) = effect_at(resolution, facts, context, *callee) else {
                return Ok(None);
            };
            let Some(fact) = facts.get(callee) else {
                return Ok(None);
            };
            let callee_quantum = if resolution.declaration(*callee).module == owner_module {
                fact.uses_quantum()
            } else {
                // An explicit checked public effect permits quantum work even
                // behind a currently classical interface/body. Its permission
                // stays fixed across body-only changes; unannotated classical
                // public declarations cannot conceal quantum work.
                fact.asserted().is_some()
            };
            quantum |= callee_quantum || effect != Effect::Unitary;
            if effect > inferred {
                inferred = effect;
                origin = *span;
            }
        }
        Ok(Some((inferred, quantum, origin)))
    }

    /// The caller charges storage before copying these collection-local edges.
    pub fn merge(&mut self, body: &Self) {
        self.add(body.local, body.origin);
        self.quantum |= body.quantum;
        for (id, span) in &body.calls {
            self.call(*id, *span);
        }
        for (id, (ceiling, span)) in &body.required {
            self.require_effect(*id, *ceiling, *span);
        }
    }

    #[cfg(test)]
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
#[cfg(test)]
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
    fn public_bounds_are_checked_separately_and_concrete_assertions_export_nothing() {
        for kind in [FnKind::Unitary, FnKind::Isometry] {
            assert_eq!(
                FunctionEffect::checked_declaration(kind, true, true, Effect::Observe),
                Err(DeclarationEffectError::ContradictoryBound)
            );
        }
        assert_eq!(
            FunctionEffect::checked_declaration(FnKind::Unitary, true, true, Effect::Isometry),
            Err(DeclarationEffectError::ContradictoryBound)
        );
        assert_eq!(
            FunctionEffect::checked_declaration(FnKind::Inferred, true, true, Effect::Unitary),
            Err(DeclarationEffectError::MissingPublicAnnotation)
        );
        let public =
            FunctionEffect::checked_declaration(FnKind::Observe, true, true, Effect::Unitary)
                .unwrap();
        assert_eq!(public.inferred(), Effect::Unitary);
        assert_eq!(public.public_effect(), Some(Effect::Observe));
        assert!(public.uses_quantum());
        let private =
            FunctionEffect::checked_declaration(FnKind::Inferred, false, true, Effect::Unitary)
                .unwrap();
        assert_eq!(private.public_effect(), None);
        let classical =
            FunctionEffect::checked_declaration(FnKind::Classical, true, false, Effect::Unitary)
                .unwrap();
        assert_eq!(classical.public_effect(), Some(Effect::Unitary));
        assert!(!classical.uses_quantum());
        let temporary = FunctionEffect::checked(FnKind::Observe, Effect::Unitary).unwrap();
        assert_eq!(temporary.public_effect(), None);
    }

    #[test]
    fn original_module_projection_keeps_transitive_external_boundaries() {
        let library = parse_module(
            "pub observe fn exported(q:Q<Bit>)->Q<Bit>{q} fn private(q:Q<Bit>)->Q<Bit>{q}",
        )
        .unwrap();
        let client = parse_module(
            "pub observe fn wrapper(q:Q<Bit>)->Q<Bit>{q} fn caller(q:Q<Bit>)->Q<Bit>{q}",
        )
        .unwrap();
        let resolution = Resolution::new([("library", &library), ("client", &client)]).unwrap();
        let exported = resolution.qualified("library::exported").unwrap();
        let private = resolution.qualified("library::private").unwrap();
        let wrapper = resolution.qualified("client::wrapper").unwrap();
        let caller = resolution.qualified("client::caller").unwrap();
        let library_context = EffectContext::Module(resolution.module("library").unwrap());
        let client_context = EffectContext::Module(resolution.module("client").unwrap());
        let mut facts = BTreeMap::from([
            (
                exported,
                FunctionEffect::checked_declaration(FnKind::Observe, true, true, Effect::Unitary)
                    .unwrap(),
            ),
            (
                private,
                FunctionEffect::checked_declaration(FnKind::Inferred, false, true, Effect::Unitary)
                    .unwrap(),
            ),
        ]);
        assert_eq!(
            effect_at(&resolution, &facts, library_context, exported),
            Some(Effect::Unitary)
        );
        assert_eq!(
            effect_at(&resolution, &facts, client_context, exported),
            Some(Effect::Observe)
        );
        assert_eq!(
            effect_at(&resolution, &facts, EffectContext::External, exported),
            Some(Effect::Observe)
        );
        assert_eq!(
            effect_at(&resolution, &facts, client_context, private),
            None
        );
        let span = Span::new(10, 20);
        let mut body = BodyEffects::new(span);
        body.call(exported, span);
        let (effect, quantum, _) = body
            .inferred_from(wrapper, &resolution, &facts, |_, _| Ok::<(), ()>(()))
            .unwrap()
            .unwrap();
        assert_eq!(effect, Effect::Observe);
        assert!(quantum);
        facts.insert(
            wrapper,
            FunctionEffect::checked_declaration(FnKind::Observe, true, quantum, effect).unwrap(),
        );
        let mut local = BodyEffects::new(span);
        local.call(wrapper, span);
        let (effect, _, _) = local
            .inferred_from(caller, &resolution, &facts, |_, _| Ok::<(), ()>(()))
            .unwrap()
            .unwrap();
        assert_eq!(effect, Effect::Observe);
        local.require_unitary(exported, span);
        assert_eq!(
            local.first_violation_using(|id| effect_at(&resolution, &facts, client_context, id)),
            Some((Effect::Unitary, span))
        );
        assert_eq!(
            local.inferred_using(|id| effect_at(&resolution, &facts, client_context, id)),
            Some(Effect::Observe)
        );
    }

    #[test]
    fn checked_self_effect_is_least_and_missing_dependencies_or_capacity_fail() {
        let module = parse_module("fn f(q:Q<Bit>)->Q<Bit>{q} fn g(q:Q<Bit>)->Q<Bit>{q}").unwrap();
        let resolution = Resolution::new([("main", &module)]).unwrap();
        let id = resolution.qualified("main::f").unwrap();
        let other = resolution.qualified("main::g").unwrap();
        let span = Span::new(10, 20);
        let mut body = BodyEffects::new(span);
        body.mark_quantum();
        body.call(id, span);
        assert_eq!(
            body.inferred_from(id, &resolution, &BTreeMap::new(), |_, _| Ok::<(), ()>(()))
                .unwrap(),
            Some((Effect::Unitary, true, span))
        );
        body.add(Effect::Observe, span);
        assert_eq!(
            body.inferred_from(id, &resolution, &BTreeMap::new(), |_, _| Ok::<(), ()>(()))
                .unwrap(),
            Some((Effect::Observe, true, span))
        );
        body.call(other, span);
        assert_eq!(
            body.inferred_from(id, &resolution, &BTreeMap::new(), |_, _| Ok::<(), ()>(()))
                .unwrap(),
            None
        );
        assert_eq!(
            body.inferred_from(id, &resolution, &BTreeMap::new(), |_, _| Err::<(), _>(
                "capacity"
            )),
            Err("capacity")
        );
    }

    #[test]
    fn provider_ceilings_meet_without_replacing_principal_effects() {
        let id = provider();
        let iso_span = Span::new(10, 20);
        let unitary_span = Span::new(30, 40);
        for (first, second, expected, origin) in [
            (
                Effect::Isometry,
                Effect::Unitary,
                Effect::Unitary,
                unitary_span,
            ),
            (Effect::Unitary, Effect::Isometry, Effect::Unitary, iso_span),
            (
                Effect::Isometry,
                Effect::Isometry,
                Effect::Isometry,
                iso_span,
            ),
        ] {
            let mut body = BodyEffects::new(Span::default());
            body.require_effect(id, first, iso_span);
            body.require_effect(id, second, unitary_span);
            assert_eq!(body.required[&id], (expected, origin));
            assert_eq!(body.storage_cells(), 2);
            for actual in [Effect::Unitary, Effect::Isometry, Effect::Observe] {
                let inferred = BTreeMap::from([(id, actual)]);
                assert_eq!(body.first_violation(&inferred).is_some(), actual > expected);
            }
            assert_eq!(
                body.first_violation(&BTreeMap::new()),
                Some((expected, origin))
            );
        }
        let mut actual = BodyEffects::new(iso_span);
        actual.add(Effect::Isometry, iso_span);
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
        assert_eq!(inferred[&caller_id], Effect::Isometry);
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
        outer.require_effect(id, Effect::Isometry, first);
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
