# Selected-source CLI execution

This is a bounded implementation unit within
[Issue #32](https://github.com/MGYamada/Qleisli/issues/32), not completion of
frontend convergence or the release. Edition 2026, version 0.3.0-alpha and
native protocols remain unchanged. The authority Reference records the separate
EXACT-2026-01 adoption; this CLI change does not discharge that interpretation.

## Contract and implementation

Explicit `--module` and `--entry` selection for `check`, `run`, `sample` and
untrusted `emit-proposal` shares one execution plan with the retained `sized`
adapter. All supplied declarations are source checked; native checking applies
to the selected specialization. Project-wide commands retain their own scope.
The plan selects Raw or hierarchy before native checking. A typed hierarchy
ineligibility permits Auto to select Raw; a real source/checking error remains
terminal. An explicit independent request or named provider requires hierarchy.
No lowering, native rejection or execution failure retries through Raw.

Raw execution requires no declared runtime parameters and no quantum result.
Even a Unit parameter needs an explicit argument, which this invocation does
not yet provide. Open proposals remain checkable/emittable. Hierarchy retains
its existing basis-input convention. An explicit Raw basis option, including
zero, rejects before native checking. Selected sampling retains the 1024-shot
limit; the project command's independent one-million-shot limit is unchanged.

The result reports entry, IR profile, declaration/native scopes and the existing
verification scope. Raw runs use a fresh native handle and independent source
step matching, without claiming complete source-meaning preservation. Hierarchy
retains producer/caller/named-provider distinctions. Untrusted emission does not
claim native verification. `--format=json` wraps results and errors in the
existing v1 envelope; legacy output and its write-error description remain.

## Sources, failures and independent expectations

The [first Unit-parameter study](../../authoring_sessions/selected-source-cli-v030/session.json)
preserves the exact initial program and four actual pre-change observations.
Existing mixed, ordinary and runtime-parameter studies remain unchanged.
`current-unit/` records the same four invocations after this implementation:
both selected and legacy forms check the open Unit-parameter proposal, while
both reject execution without an explicit runtime argument. Each observation
binds the original source, manifest, current executable and native checker.

`latest-first/` records two real CLI failures: a stale usage golden and a changed
legacy write-error description. The current usage derivative lives here;
the old v0.2.9 golden remains untouched. `latest-repair/` preserves the next
run and three incorrect newly authored test expectations. The exact first
driver and first selected-source test remain as `.txt` snapshots. See
`repair-history.json` for the corrections; failed observations are not rewritten.

The corrected tests explicitly select Raw for Raw capability negatives,
distinguish unsupported Q<Unit> from supported ordinary Unit/zero-width Bits,
and supply the proper closed operation interface to an independent QPE request.
Its expected meaning fixes omega = exp(i*pi/4) and its eight coefficients
independently of generated lowering. A separately fixed H request rejects X;
the fixed QPE request rejects a changed candidate provider. Logged native calls
establish pre-native rejection and exactly one hierarchy call on those failures.
Other bounded cases cover Bell correlations, pending entangled arguments,
eager effects, zero/one/two static folds, phase, sampling and unused declarations.

## Validation and limits

Both `latest-final/` (Rust 1.98.1) and `msrv-final/` (actual Rust 1.85.0) pass
107 tests across eleven focused integration targets, the two existing ignored
native CLI tests, all-target Clippy with warnings denied, and formatting.
The three other ignored sized-source tests were not run. Each run binds the
same 234 selected files with source-manifest SHA-256
`974db80591484bb804b5cdf82b76b4133271284c37ab4f09eb835443f85bc031`.
This selected manifest is not a complete dependency/input closure; remaining
retained inputs are at the recorded Git base. The final selected CLI test hash
is `9df52b807d7e22d4db31326484b4d90bd506c54d04f46fb23eb89ee0bd9ac29e`.

Both runs reuse native checker
`39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85`.
No Lean source changed and no fresh Lean build, audit or replay is claimed.
Local Rust builds share one bounded external target, disable incremental/debug
output and use two jobs. No new maximum-size quantum case was generated.
Source validity, step agreement, semantic proofs, full CI and release readiness
remain distinct. The live CI for an earlier pushed commit is not validation of
this implementation.

`metadata-final/` records inventory, production coverage, authoring, edition,
Markdown, pinned mdBook 0.5.4 and rendered/print-page checks. It covers 20 HTML
files, 753 local links and 277 anchors. Constitution/release changes have their
own evidence packet; this CLI packet makes no new Lean replay claim.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
