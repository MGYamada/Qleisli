# Semantic namespace integration evidence

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.

This packet records implementation and bounded verification of the 21 applicable
criteria of [#317](https://github.com/MGYamada/Qleisli/issues/317). Generic QFT
implementation, public integration, fixed/generic correspondence and its proof
completion are excluded by the maintainer; those exclusions earn no completion
credit. Existing fixed QFT source and regressions retain their bounded contracts.

The [normative Reference](../../../../../docs/src/reference/stdlib.md) defines
the semantic admission/naming rules, nine public interfaces, exact contracts
and migration. `source-migration.json` preserves the starting snapshot and its
then-pending validation status. Later results do not rewrite that first record.
An atomic integration commit, recorded in GitHub, binds the completed work;
worktree checks alone are not a committed integration or release gate.

## Actual checks and retained failures

| Evidence | Actual result and limit |
| --- | --- |
| `rust-validation-01.json` | MSRV: 130 passed, one stale-import diagnostic test failed. |
| `rust-validation-02.json` | Repaired MSRV review target: eight passed; latest Rust: all 131 tests across 13 affected targets passed. Both all-target Clippy checks and formatting passed. No full all-target test run. |
| `reporting-correction-01.json` | Corrects mistaken prose aggregates of 140/141 in two captures using their actual libtest summaries. Raw captures and earlier failures remain unchanged. |
| `frontend-types-validation-01.json` | Three frontend type tests passed on each Rust version after fixing four stale debug-format expectations. Type distinctions and checker behavior were unchanged. |
| `python-regressions-02.json` | Final selector/provenance tests passed: 62 corpus tests and 21 fixture tests. First failures and review fixes have separate records. |
| `corpus-oracles-01.json` | Six tiny corpus comparisons passed 340 semantic probes (2–4 qubits), but the aggregate stage failed on one outdated negative diagnostic expectation. It remains failed. |
| `negative-diagnostic-review-01.json`, `negative-validation-02.json` | Independently reviewed expectation correction; all four unchanged negative sources subsequently passed their rejection expectations. No whole 340-probe rerun. |
| `negative-derivative-03.json`, `negative-selection-validation-04.json` | Final inventory checking found that the original negative manifest was a frozen baseline. Its original bytes were restored; the exact separately selected current derivative retains all four cases/sources. All four final rejection expectations passed; an initial missing-kernel driver failure is preserved separately. |
| `negative-selector-regressions-03.json` | All 68 pure corpus/selector tests passed after six new negative-derivative guards. The combined tool result is identified accurately; separate stdout/stderr was not captured for this invocation. |
| `corpus-consumers-selection-after-01.json`, `corpus-consumers-selection-final-01.json` | Rust corpus smoke (two tests) and accepted-view roundtrip (five tests) passed with 101 logical projects, 87 finite corpus executions and exactly six selected snapshots. Both final all-target Clippy checks and formatting passed with unchanged source identities. The actual first old-root failure is retained. |
| `native-source-selector-repair-01/summary.json` | Python native comparisons passed 267 process checks and 84 existing small clients, including all six current snapshots through both native selections. The actual first run failed on the old root after 112 observations. Benchmark validation is source-selection-only; no performance run. |
| `fixed-source-client-01.json`, `qpe-source-clients-01.json` | Two fixed QFT clients and two QPE instrument clients passed their independent bounded checks, including wrong reversal and dephased controls. Source-only checks; no fresh Lean build or replay. |
| `policy-validation-01.json` | Documentation, authoring, edition, corpus metadata, inventory, production coverage and constitutional identity checks passed; constitutional (63), coverage (14) and CI profile (6) regression tests passed. |
| `book-validation-01.json`, `book-validation-02.json` | Pinned mdBook 0.5.4 build passed. A first link-check invocation failed on an incorrect command-line argument; corrected invocation checked 24 HTML pages, 968 local links and 362 anchors successfully. |
| `quickstart-validation-01.json` | Existing rebuilt CLI quickstart checks passed outside the checkout, including embedded std source. This is not a fresh installation or package check. |
| `post-comment-validation-03.json` | Final embedded Fourier-only comment correction rebuilt the CLI; all 11 documentation tests and four unchanged first-client checks passed. Earlier larger suites retain their prior-comment source/binary bindings. |

Independent library and selector reviews retain their exact reviewed identities
and findings. The completion review maps each criterion to evidence, including
the final comment correction. Complete source snapshots, predecessor identities,
missing-map rejection and path containment are checked before current fixture
or corpus selection. An explicit derivative never changes the old first source.

The first completion review missed active corpus-root selection in Rust roundtrip,
Rust corpus smoke and Python native comparisons. Final integration checking found
those omissions before committing. Their maintained execution roots are corrected
explicitly, with failed first observations and follow-up results retained. The
performance benchmark's source selection is also corrected; the benchmark itself
is not executed. Final consumer review and results are separate from review01.
`validation-overview.json` retains the earlier candidate's identities;
`validation-overview-02.json` identifies the completed integration candidate.

## Constitutional impact and remaining duties

QS-2026-01, PR-2026-01, RS-2026-01 and EXACT-2026-01 apply. Namespace relocation
changes source compatibility and ordinary bundled-source selection. It changes
no mathematical function body, complete interface, phase, owner transition,
primitive, native representation, acceptance definition or Lean proof. Namespace
placement grants no effect assertion, independent Meaning or trusted exception.
All bundled declarations and local arithmetic use ordinary checking and fresh
native acceptance. Independent formulas retain their original mathematical logic.

The two human-admitted QLV1 ownership/classical-scope guarantees retain their
recorded meanings, premises and current evidence; all broader obligations and
the exactness supplement remain pending. Identity checks use trusted commit
`faa5cfb5e7ea1cf3b39a43b80f7f2345e89197c2`. They are not a fresh Lean replay,
source/runtime preservation theorem, mathematical specification adoption,
guarantee admission or release approval. No new Guardian judgment is claimed.
No dependency, release version or edition change is part of this unit.

Final policy identities are rechecked after integration preparation and recorded
separately. Hosted CI on the preceding commit failed its Rust/distribution tests;
its successful native producer checks do not make that aggregate run successful.
The next commit requires its own CI. Same-commit full CI, package, installation,
native bundle, tagging and publication remain separate release duties.
