# Learning by structure and explicit discovery

**What can be inferred should be reliably inferable; what cannot be inferred
should be reliably discoverable.** A reader or coding agent should not need
prior Qleisli knowledge before it can learn Qleisli. This is the design contract
of [Issue #253](https://github.com/MGYamada/Qleisli/issues/253), subordinate to
the [authority hierarchy](authority.md) and [architecture](architecture.md).
It is an intended recovery contract, not a measured zero-prior LLM benchmark.
Naming, a diagnostic or an informed study supplies no semantic evidence.

Start with `qleisli --help` or `qleisli help`. Both point to
`qleisli help ecosystem`, which prints this exact chapter from the installed
binary. It works without a project, network or native kernel and introduces
native concepts before requiring their names. Shared usage/unknown-command
responses point to this path, including existing JSON usage errors. These help
requests are text-only: execution options, unknown topics or `--format=json`
remain usage errors. Help produces documentation, never acceptance or analysis.

## Four recovery categories

| Category | Recoverable information | Required path |
| --- | --- | --- |
| Zero-prior inferable structure | A uniquely specified conceptual role from familiar organization, consistent names and deterministic diagnostics. | Infer the role, check actual help/availability and read its canonical contract. Similar spelling alone is insufficient. |
| Inspectable derived source | An unfamiliar abstraction's behavior through its declared contract and ordinary checked implementation. | Signature → `.qli` source → called definitions → language rules and specified primitives. |
| Explicitly discoverable native concept | A role generic programming prior cannot reliably determine. | Ordinary compiler help → this introduction → canonical design/contract and actual availability. Do not guess an acronym's semantics. |
| Specification-only authority | Meaning or evidence that source reading and analogy cannot establish. | Normative contract, applicable human interpretation, independent checks and actual artifact bindings. |

These categories grant no conversion, provider choice, proof, inverse/control
access or alternative acceptance path. An ambiguous guess must reject or lead
to discovery.

## Language and ecosystem map

| Concept | Category and intended role | Correction/discovery and status |
| --- | --- | --- |
| Qleisli compiler/checker | Inferable checking workflow with Qleisli-specific duties. | `qleisli --help`; [production boundary](production-boundary.md). Rust proposes; the required native checker issues semantic accepted handles. |
| `qargo` | Inferable Cargo-style project/package orchestration. | [qargo's own repository](https://github.com/MGYamada/qargo) and help/contracts. It is separately distributed; this compiler supplies no qargo alias or external-release compatibility claim. |
| `qrate`, `Qargo.toml` | Inferable package/project structure with explicit Qleisli identity. | [Project introduction](../introduction.md), schema-2 `[qrate].edition = "2026"` and the actual source-root contract. A source tree is not automatically a complete named qrate. |
| `qlippy` | Inferable lint-tool role, not a proof checker. | qargo's tooling contracts and availability; no standalone qlippy command is supplied here. |
| `qlifmt` | Inferable formatter role, not semantic coercion/repair. | qargo's tooling contracts and availability; no standalone qlifmt command is supplied here. |
| `qlidoc` | Inferable Qleisli API-documentation role. | [Documentation responsibilities](../building.md). Current `qleisli doc <source-file>` emits source Markdown; it is not the complete future qlidoc interface. |
| `qleisliup` | Inferable installer/toolchain-selection role outside language acceptance. | Its own distribution/selection contract. Help here installs nothing and substitutes no verifier. |
| `Q<T>` and `T` | Inferable explicit quantum/classical boundary after correction; exact semantics require reading. | [Type model](type-model.md): ownership and observation/preparation remain explicit. Familiar generics imply no conversion. |
| `if`/`qif`, `for`/`qfor`, `match`/`qmatch` | Intended structural boundary where the counterpart is specified and supported. | [Source text](source-text.md) and type/profile contracts. Proposed pairs promise no availability; current static folds/branches do not automatically become qfor/qmatch. |
| Derived stdlib | Inspectable ordinary checked source with one mathematical home. | [Semantic namespaces and contracts](stdlib.md), signature, implementation and called [primitive contracts](primitive-boundary.md). Reserved family identities do not imply available APIs. |
| QLT | Explicit native discovery: mathematical testing. | Introduction below and [#50](https://github.com/MGYamada/Qleisli/issues/50). Not implemented in this alpha; `qleisli test` is not a QLT runner. |
| QDB | Explicit native discovery: mathematical diagnosis/navigation. | Introduction below and [#51](https://github.com/MGYamada/Qleisli/issues/51). Not implemented in this alpha. |
| QCP | Explicit native discovery: circuit/resource profiling. | Introduction below and [#103](https://github.com/MGYamada/Qleisli/issues/103). Not implemented in this alpha. |
| Sealed primitive | Specification-only semantic contract. | [Primitive inventory/admission](primitive-boundary.md). Names/implementations cannot authorize a different phase, axis order, effect or owner transition. |
| External provider/artifact | Specification/evidence boundary despite familiar format/API. | [Realization](realization.md), independent checks and actual input/output identity. Format validity proves no source preservation or physical certification. |
| mdBook | Inferable external documentation renderer. | [Pinned build environment](../building.md). It creates neither language acceptance nor Qleisli API introspection authority. |

Tool names designate responsibilities, not the complete public command topology.
The later [#232](https://github.com/MGYamada/Qleisli/issues/232) decides that
topology; this chapter reserves no analysis-command aliases. Release version,
constitutional edition, qrate identity and protocol/profile identity differ.
A familiar name establishes no compatibility.

## Introduce the native analysis pillars

The planned pillars answer different questions about an identified checked
subject; generic Rust/Cargo prior does not determine these meanings:

| Tool | Problem | Relationship and limit |
| --- | --- | --- |
| QLT — Qleisli Test Suite | Does the implementation satisfy the requested mathematical assertions? | Explicit evaluator/profile limits; test observations are not automatically admitted constitutional guarantees. |
| QDB — Qleisli Debugger | Which claim/obligation failed, why and where did it originate? | Navigates source/Core provenance, witnesses and missing evidence, including QLT failures. It cannot inspect or clone a live quantum state. |
| QCP — Qleisli Circuit Profiler | What resources are required under a stated circuit model or target? | Structural quantities, bounds or conditional estimates can inform QLT budgets and QDB navigation. Counts are no quantitative RS proof or hardware promise. |

All three remain planned at their existing later targets, subordinate to the
ordinary verifier and actual subject/result identities. Successful help does
not execute them. Names alone do not determine profiles, schemas or assumptions.

## Deterministic correction without choosing physics

Diagnostics provide the repair channel in
[#224](https://github.com/MGYamada/Qleisli/issues/224),
[#225](https://github.com/MGYamada/Qleisli/issues/225) and
[#237](https://github.com/MGYamada/Qleisli/issues/237): identify the boundary,
supported canonical form, original location and required explicit choice.
These recovery instructions are not automatic source edits:

| Predictable failure | Safe recovery | Unacceptable false friend |
| --- | --- | --- |
| Treat `Q<T>` as copyable ordinary data | Read ownership; account for every owner explicitly. | Copy, discard or reset an owner merely to make source compile. |
| Expect ordinary/quantum expected-type conversion | Choose specified preparation/observation explicitly only if that is the intended meaning. | Insert measurement or preparation because a result type is expected. |
| Guess an omitted Nat or Op | Missing/extra diagnostics identify entry/provider and unresolved names; provide the intended exact bindings. | Rank identity/X providers or invent a size to satisfy the checker. |
| Equate equal widths or familiar tuple layouts | Read exact trees, axes and admitted explicit maps. | Flatten, reorder or adjust phase as an ordinary coercion. |
| Try unavailable analysis/lint commands | Usage leads to `qleisli help ecosystem`, honest status and canonical contracts. | Report source checking as QLT testing or manufacture a profiler result. |
| Encounter an unfamiliar derived function | Follow signature and checked source recursively, stopping at specified primitives. | Reconstruct a sealed meaning from an implementation or first-party name. |

Current explicit-binding diagnostics/tests are actual correction examples.
Full diagnostic pedagogy and future forms retain their separate Issues. A fixed
informed study proves no reliable zero-prior model learning. An unavailable
construct must be discovered as unavailable, never rewarded as a plausible guess.

## Naming and future design review

Every future first-party concept must declare its recovery category, intended
semantic role, canonical first correction/discovery path and availability.
Classical analogies must identify the shared role and its limits. Superficial
q-prefix spelling cannot substitute for a contract. Forbid misleading
pseudo-analogues, semantic false friends and discovery requiring prior knowledge
of the concept's name.

Major designs must follow the [architecture review](architecture.md#required-review-of-future-designs),
provide recovery for predictable mistakes, distinguish inspectable source from
sealed/external authority, and separate observation, checking and human adoption.
Discovery creates no semantic authority.
[#167](https://github.com/MGYamada/Qleisli/issues/167),
[#169](https://github.com/MGYamada/Qleisli/issues/169) and
[#196](https://github.com/MGYamada/Qleisli/issues/196) retain the actual stdlib,
artifact and language-boundary implementation obligations.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
