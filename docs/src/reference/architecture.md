# Policy, constitutional harness and execution

**Policy as Theorem. Constitution as Harness. Compiler as Executor.**

This is Qleisli's top-level architecture principle, specified by
[Issue #254](https://github.com/MGYamada/Qleisli/issues/254). It is subordinate to
[the authority hierarchy](authority.md), the ratified Constitution and the
recorded human interpretations. It defines no new mathematical interpretation
or discharged guarantee.

## Policy as Theorem

A policy affecting constitutional acceptance must become a formal proposition
or evidence obligation whose discharge can be checked independently. An
implementation convention, a theorem name, a test or a successful compilation
cannot supply that authority.

The natural-human Constitution Guardian determines the binding constitutional
interpretation for a defined case: what must be proved, the applicable scope
and premises, and how the requirement relates to existing guarantees. Lean or
the designated independent proof checker establishes derivability of the
resulting proposition under its actual definitions and recorded assumptions.
Human interpretation and mathematical verification remain separate judgments.
Ordinary maintainers select language and implementation designs within those
requirements; routine covered maintenance needs no new interpretation.

QS, PR and quantitative RS are three permanent, distinct proof obligations.
Their binding meanings come from the adopted interpretations; this chapter
freezes no predicate or theorem type. Evidence must connect the claimed property
to the actual production acceptance and current accepted artifact. A source
claim additionally requires its source-preservation link; a realization claim
requires correspondence to the actual output; a resource claim requires the
specified bound for the actual behavior or realization. Those links cannot be
replaced by a proof about a convenient unused predicate.

The [initial interpretations](../design/initial-interpretations.md) and
[scoped guarantees](../design/initial-guarantees.md) record current coverage.
Only ordinary QLV1 root ownership and classical scope have been admitted as
scoped guarantees. Broader QS, PR, quantitative RS and the EXACT supplement
retain pending duties. Passing a compiler check does not discharge them.
The Fundamental Theorems do not themselves prove the Rust frontend, native
compiler, decoder, simulator or exporter correct; each claimed correspondence
retains its own obligations and assumptions.

## Constitution as Harness

The Constitution fixes permanent obligations, human interpretive authority,
recording procedures and continuity. Discharged guarantees accumulate for
their recorded scopes and premises. A future syntax, provider, backend,
representation, release or tool cannot escape an applicable obligation by
renaming or moving its acceptance path. Changed representations require the
appropriate checked semantic transport; old proof files alone are insufficient.
Edition identifies this constitutional regime. Syntax and release compatibility
remain separate.

The harness must reach executable boundaries. Prefer making a prohibited
operation unrepresentable, untypable, unverifiable or explicitly rejected.
External prompts, coding conventions and author identity cannot be the only
protection for an accepted guarantee. Identity, continuity, production coverage
and required evidence belong in mechanical enforcement, with their actual
limitations exposed. Current CI checks implement parts of that harness;
[constitutional CI](https://github.com/MGYamada/Qleisli/issues/141) and the
[release gate](https://github.com/MGYamada/Qleisli/issues/142) retain their
unfinished requirements.

Pre-v1 proof maturity permits truthful disclosure of incomplete coverage. It
never permits withdrawing an admitted guarantee, treating a failed check as
successful or advertising an unproved scope as constitutionally certified.

## Compiler as Executor

**The compiler executes policy; it does not create policy.**

The language and ecosystem are the executable surface of these constraints.
Parsing, name resolution, type/effect/ownership preparation, evidence generation
and lowering apply the authorized contracts. Native Lean checking supplies new
semantic accepted handles under the [production boundary](production-boundary.md).
Rust proposals, authored source and external IR all remain subject to the
applicable independent checks. Native absence, incompatibility or failure rejects
without fallback to another acceptance authority.

| Boundary | Enforcement and user-visible meaning |
| --- | --- |
| Ordinary values and quantum owners | `T` and `Q<T>` remain distinct. Preparation and measurement are explicit; expected typing cannot insert either. |
| Ownership, axes and phase | Every owner, including zero-width owners, is accounted for. Width is not interface identity; permutation and nontrivial phase remain explicit. |
| Effects and capabilities | A body cannot downgrade Observe to Unitary, and unitarity alone supplies no inverse or control API. Declared evidence and access obligations must be checked. |
| Workspace and temporary access | Clean/dirty and access features must enforce their adopted all-input/reference contracts when admitted; planned syntax or a successful known-input test is not such evidence. |
| Source and external artifacts | An external provider or schema cannot manufacture semantic authority. Independently checking valid output IR alone does not prove its source or target correspondence. |
| Qrate, module and toolchain | Explicit identities and closed substitutions govern checking; ambient names or a plausible provider are not evidence. |

The [type model](type-model.md), [primitive boundary](primitive-boundary.md) and
[realization contracts](realization.md) state current rules and remaining profile
limits. This table does not implement the unfinished access, workspace,
realization or surface proposals.

Crossing a protected boundary must fail closed and explain the violated rule.
A safe expressible alternative may be suggested when one exists. Unsupported
constructs, missing evidence and failed native checks must never silently become
weaker semantics, hidden discard/reset, implicit physical coercions or unchecked
backend acceptance. A diagnostic may explain a proof gap; it cannot waive it.

## Diagnostics and inspectable recovery

Diagnostics are constitutional pedagogy: they make an enforced boundary visible
to humans and coding agents. A useful rejection identifies the boundary, the
likely classical assumption, the canonical Qleisli construct where available,
and a recovery that preserves the contract. For example, a missing explicit
Op provider names the unresolved binding; it does not search for a convenient
implementation. A quantum wildcard must not silently consume an owner.
Text and JSON describe the same failure and source location.

An unfamiliar derived stdlib abstraction should have an inspectable recovery
path: read its signature, inspect the ordinary checked `.qli` implementation,
then follow its calls to language rules and specified primitives. Derived code
must undergo the same applicable checking as user code. Source location,
first-party status and documentation generation confer no semantic authority.
Sealed primitives require their canonical contracts and independent checks;
reading an implementation cannot reconstruct or authorize a different meaning.
The [primitive inventory and current limitations](primitive-boundary.md) separate
this policy from the unfinished complete stdlib migration.

QLT, QDB and QCP are Qleisli-native discovery targets, rather than concepts a
reader should guess from a classical name. They and qargo, qlidoc and other
tools remain subordinate interfaces: they may expose programs, facts, diagnostics
or evidence, but cannot adopt interpretations, waive proof, create a parallel
acceptance path or weaken accepted meaning. Their implementation is later work;
this chapter installs none of those tools. mdBook is the separate documentation
build environment and creates no language or API-introspection authority.

The [canonical discovery contract](discovery.md) under
[#253](https://github.com/MGYamada/Qleisli/issues/253) defines discovery and
correction paths. This principle
alone is not evidence that those paths or a zero-prior authoring benchmark are
complete.

## Required review of future designs

Every major language or tooling design document must identify how it preserves:

1. the applicable adopted interpretation, scope, premises and existing guarantees;
2. formal obligations, actual acceptance/artifact bindings, checked evidence and
   remaining proof gaps;
3. authorized source rules, lowering, ownership/effects, exact phase/axes and
   fail-closed behavior;
4. diagnostic recovery, inspectable derived source and explicit tool discovery;
5. the distinction between human interpretation, formal verification and execution.

Use the existing constitutional impact procedure and GitHub decision record.
An unresolved new constitutional case requires the concrete human judgment;
ordinary implementation within existing interpretations remains maintenance.
No design document gains constitutional authority by completing this checklist.

Related decisions: [Constitution #129](https://github.com/MGYamada/Qleisli/issues/129),
[production boundary #136](https://github.com/MGYamada/Qleisli/issues/136),
[theorem jurisdictions #139](https://github.com/MGYamada/Qleisli/issues/139),
[checked stdlib #167](https://github.com/MGYamada/Qleisli/issues/167),
[external authority #169](https://github.com/MGYamada/Qleisli/issues/169),
[surface boundary #196](https://github.com/MGYamada/Qleisli/issues/196),
[diagnostic pedagogy #224](https://github.com/MGYamada/Qleisli/issues/224),
[diagnostic harness #225](https://github.com/MGYamada/Qleisli/issues/225),
and [inference/discovery #253](https://github.com/MGYamada/Qleisli/issues/253).

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
