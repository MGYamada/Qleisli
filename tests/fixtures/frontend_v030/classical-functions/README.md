# Total classical functions, ordinary calls and explicit source migration

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.

The [ordinary implementation contract](https://github.com/MGYamada/Qleisli/issues/22#issuecomment-6010679334)
follows the maintainer's `classical fn` name selection. `basis input as pattern
{ expression }` remains the coherent construct. The earlier `basis fn` proposal
was withdrawn before production changes; its [first sources and refusals](../../authoring_sessions/basis-runtime-v030/README.md)
remain historical inputs, not an adopted API or successful implementation.

The new declaration has the existing total finite expression grammar. Ordinary
calls lower original expression nodes through shared ordinary operations;
static/Meaning and coherent uses retain their independent finite checks.
The borrowed view preserves original identifiers and spans and charges each
consumer's work/allocation budget. It creates no cloned source tree, native
acceptance, inverse/control access or evidence. Noninjective ordinary functions
remain legal. Arguments evaluate eagerly in order; their effects remain in the
caller. Live `Q<T>` cannot be passed as ordinary `T` without observation.

`source-map.json` records 86 current executable file derivatives (38,563 bytes),
each changing only `basis fn` to `classical fn`. Prior maps, first sources,
diagnostics and immutable verification/corpus baselines remain unchanged.
[Corpus migration](../../../../corpus/migrations/classical-functions-v030/validation-summary.json)
separately selects ten production projects and eight fault/rejection projects.
The current discovery guard retains 87 logical corpus roots and 14 examples;
current leaves are four namespace snapshots and ten classical snapshots.

The [classical first-source session](../../authoring_sessions/classical-runtime-v030/README.md)
retains eight pre-change parser refusals and thirteen post-change observations.
The [two-example type study](../../authoring_sessions/ordinary-types-few-examples-v030/README.md)
retains the observer's invalid namespace prompt and its twelve name refusals,
plus a new independent corrected-context first response and twelve observations.
The invalid prompt does not count as type/ownership validation or first-attempt
execution success. These are bounded studies, not general LLM benchmarks.

## Verification and remaining duties

[Actual command records](validation/validation-summary.json) distinguish repaired
failures from successful checks. The independent eleven-test suite checks the
exact coherent image and reference action, noninjective ordinary AND, Unit and
ordered trees, eager observation, private/unused definitions, lexical dependency
cycles, old spelling refusal, Meaning's nonruntime category, and existing exact
computed cleanup. Meaning/refinement and coherent admissibility remain separate
from ordinary execution.

Latest Rust has 331 passing tests across 30 exercised targets and five existing
ignores. MSRV 1.85.0 has 63 focused passes. Both all-target Clippy runs pass.
Scoped corpus replay has 716 probes over ten cases, detects seven type-correct
semantic faults and retains four negative refusals. mdBook 0.5.4 builds; 28 HTML
pages, 1,162 local links and 440 anchors, including print, pass inspection.

Selected CoherentLift, finite register/entry and other profile restrictions are
explicit. The selected CLI records still report `source_meaning_verified:false`.
The existing native binary is reused under its recorded identity; this unit
does not perform a fresh Lean build/audit/replay. The two admitted ordinary QLV1
guarantees retain their scopes and premises. Broader QS, PR, quantitative RS,
EXACT, general source preservation and release gates remain pending. Edition
2026, product version 0.3.0-alpha, dependency versions and native rules are
unchanged. Generic QFT remains outside the goal. Full hosted validation of the
new commit is a separate pending check; no Issue closure or release is claimed.
