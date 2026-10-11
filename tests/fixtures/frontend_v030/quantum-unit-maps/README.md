# Explicit quantum Unit maps

This bounded integration implements the next contract recorded in Issue #43:
`std::quantum::unit` takes one ordinary Unit argument and produces a fresh
Q<Unit> owner; `std::quantum::finish` consumes that owner and returns ordinary
Unit. Both have exact coefficient +1 and Unitary quantum action. They use the
existing checked hierarchy pack_unit/unpack_unit constructors, with no new
native acceptance rule, wire, observation or constitutional guarantee.

The first 22 complete projects and 44 actual baseline observations remain in
`tests/fixtures/authoring_sessions/quantum-unit-maps-v030/`. Their original
missing-name diagnostics are retained. Negative projects rejected at that
earlier boundary do not establish downstream type, owner or effect behavior.

## Independent equations and actual source correspondence

`independent-expectations.json` fixes the intended equations before the new
tests: both round trips have coefficient +1, scalar work survives elimination,
two eighth phases give i, and four controlled scalar applications give Z.
The twelve integration tests also check left/right separate-owner products,
arbitrary complex reference coefficients, twenty isolated type/arity/ownership
cases, complete argument evaluation, unused declarations and zero folds.
No case exceeds two system qubits. These explicit owner-product maps do not
complete the packaged-tree Q<(Unit,A)> unitor requirement.

Fixed native requests use independently authored operators and coefficients;
transport labels and call placement were obtained from the existing lowering
interface. No emitted comparison request was copied into an oracle. The first
test source and its hash are retained in `first-test.rs.txt` and `first-test.json`.
The six additional translations are identified in `independent-tests.md`.

The private source-event regression is preserved before its first execution in
`first-private-preservation.rs.txt`. It substitutes a separately authored,
native-accepted coefficient-omega implementation with the same Unit boundary
and a consistent producer request. The source-event checker must reject its
claim to implement the original canonical +1 map. This exercises both creation
and elimination without using malformed JSON as the rejection reason.

The aggregate input manifest initially overstated its pre-execution timing.
`independent-inputs.initial.json` preserves that initial metadata; the corrected
`independent-inputs.json` distinguishes the separately frozen source/test and
expectation bytes from subsequently assembled notes. No source, test or
observation was changed by this correction.

## Current validation

Actual Rust 1.98.1 and actual 1.85.0 each pass 149 checks. `latest-first/` and
`msrv-first/` record 144: 125 across twelve integration targets, 17 sized library
tests, and two explicitly run native CLI tests. `latest-native/` and
`msrv-native/` each add five small Fourier/QPE/gate regressions, accounting for
all seven default-ignored tests in the selected targets. Both toolchains pass all-target
Clippy, warnings-denied library rustdoc and formatting. Every command succeeds
on its first recorded run for these inputs. The seven explicit predicate-domain
tests and three frontend-type tests are included in those totals.

The selected 531-input manifest is
`79c8fa5ce183daa04f4efc9483b19ce30012b92faf4e53604049143e4cbcfa08`.
Selected sources and the reused native checker remain stable within each run.
The checker hash is
`39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85`;
no new local Lean build, audit or proof replay is claimed.

`cli-first/` separately records a real CLI build and 44 checks of the untouched
first projects. Ten selected-source cases now accept. Type/arity/owner/effect
counterexamples reject at the corresponding rules; the observing Unit result
and packaged tuple still expose their stated profile boundaries. All 22 finite
results, including stdout, stderr and exit code, remain byte-identical to the
baseline. Finite checking of an empty main is not execution of an open helper.

`policy-docs/` records passing constitutional continuity against reviewed commit
e01e98a42a00c04892617205307f2db76b5c404e, inventory/coverage, authoring, scheduler
and documentation checks. The pinned mdBook 0.5.4 build and rendered-link check
pass (20 HTML pages, 753 local links, 277 anchors). This source-only evidence
does not replace a fresh proof replay or human judgment.

The pushed e01e98a CI exposed one additional stale Q<Unit>-unsupported assertion
in `tests/frontend_types.rs`. Exact hosted output and the previous test are
retained in `tests/fixtures/review_v030alpha/hosted-unit-profile-37254752247/`.
The repaired test accepts Unit and separately rejects the unsupported packaged
tuple; production acceptance was not changed to satisfy that assertion.
The completed hosted run failed, including its required aggregate gates; the
successful Lean, native-comparison, macOS, interop and docs producer jobs do not
constitute a successful full run. Distribution's source-test failure is
tracked separately with the hosted evidence.

These focused results are not same-commit full CI, release approval, general
source preservation, or completion of #43/#32. Finite/Raw parity, packaged
quantum products and general Basis support remain required. All local builds
reuse one bounded external target with incremental compilation and debug
information disabled and two build jobs.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
