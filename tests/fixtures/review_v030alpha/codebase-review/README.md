# Codebase review checkpoint

This is a review/evidence checkpoint for the approved CI-stabilization and
whole-codebase cleanup plan. It is **not a completed whole-codebase review**,
release approval, or a proof of QS/PR/RS. GitHub Issues remain the work tracker.
The feature-goal count remains 24/111; this maintenance does not close feature
issues by substitution.

Reviewed implementation revision: `ed462c8bc8db16cbb17e66a3770628dfc45ab530`.
The untracked `corpus/migrations/operation-counterexamples-v030/` experiment
was preserved and excluded from these commits. The main-checkout Rust result
binds its complete working inputs separately from the clean MSRV checkout.

## Confirmed findings

| Finding | Disposition and evidence |
| --- | --- |
| Migration counts were independently hard-coded in Rust consumers. | Fixed in `8e374b09`; current leaf selection retains independent logical-project enumeration. See the adjacent [source review](../ci-source-selection/README.md). |
| Observation comparisons discarded or prohibited current dependency evidence. | Fixed in `8e374b09`; original artifact bytes go to native acceptance, while both dependency implementations and specifications enter the independent exact oracle. |
| Current compiler output was byte-compared with immutable historical IR. | Fixed in `8e374b09`; verify each artifact and compare exact meanings; do not regenerate history to make the comparison pass. |
| Python accepted boolean/float protocol versions and ambiguous JSON. | Fixed in `df3e6912`; strict integer version, duplicate-field/nonfinite/deep-response rejection. Host regression, installed Python and installed PyQIR paths passed. |
| Native CI task scratch directories survived child timeout. | Fixed in `b56b7d98`; parent-owned temporary directories are reclaimed on success, failure and timeout. This is not complete process-tree containment. |
| Shared Lean audit command used the wrong working-directory-relative input. | Fixed in `ed462c8b`; both initial failed preparation reports remain failed. Corrected Rust/MSRV runs passed independently. |
| Python timeout leaves descendants, including an actual Rust-launched native checker, running. | **Open**, [#343](https://github.com/MGYamada/Qleisli/issues/343). A native checker uses a separate process group; a single parent-group kill is insufficient. |

## Inspected contracts and scope

The paths below identify substantive code review, not merely test execution.
A checked path does not imply every neighboring module or every proof has been
reviewed. No additional confirmed defect was found in the listed inspections
beyond the findings above.

| Area | Inspected behavior | Remaining review scope |
| --- | --- | --- |
| Corpus, fixtures and migration | `current_source_fixtures.py`, migration/provenance validation, `tests/common`, `input_corpus`, `native_roundtrip`, current observation dependency projection and historical/current oracle separation. Missing, duplicate, multistage and stale source selection retain checks. | Final integration records and the effect of subsequent source changes; the local repair unit has its own completed record. |
| Frontend and CLI | Common AST/lexical identities, source/edition loading, finite/sized entry selection, effects without annotation-based authority, original declaration interfaces, static normalization, body ownership/branch/fold checks, finite scope projection and branch phi lowering. `source_plan` selects one route without retrying a different route after a lowering failure. | Full operation/special-form checking versus all finite/sized lowering cases, diagnostics, and public-path negative examples. |
| IR, native boundary and execution | Original bytes/root/request and retained function evidence; private accepted handles and sealed execution entry; native response framing, version/work bounds and process transport; hierarchy runtime and finite leaf binding. Exact arithmetic, simulation circuit gates, ensembles, sampling, branch renaming and protected-use paths were inspected for phase, axis order and budget propagation. | Remaining hierarchy execution/bridge cases, independent matrix extractors and all codec/operation cases; process lifetime finding #343 remains open. |
| Lean and constitutional checks | Actual `Protocol.Validity.check`, ordinary QLV1 ownership/scope success theorems, original decoded-root binding, the native theorem bridge, compiled declaration audit and current guarantee identity/continuity verification. | Complete review of other acceptance families and their independent meanings/proof correspondence; whole-QS/PR/RS discharge remains outside this repair. |
| Distribution, stdlib and documentation | Source archive/package/fresh-install pipeline, native bundle/replay/relocation, version synchronization boundaries, four bundled ordinary stdlib source modules, Python host and bounded PyQIR reader. | Complete public-documentation/example consistency and the final exact-commit release/CI check. |
| Experimental research | `research/semantic-kernel/src/kernel.rs` and `adapter.rs`: backward references, exact type/phase identity, frozen requirements, bounded matrix leaves, raw-snapshot binding and absence of execution/release authority. | This experimental inspection does not grant production acceptance or a constitutional guarantee. Julia/QFT experiments remain outside the feature scope. |

Potential concerns were checked before classifying them as defects. In particular,
empty function-evidence circuits have expansion cost at least one, so their
shared dependency graph does not provide an uncharged exponential expansion in
the inspected simulator. The experimental adjoint/control/repeat proof rules
retain the required unitary/type/encoding premises; their receipts are not
production accepted handles.

## Validation and limits

`validation.json` binds compact results to their original local report hashes.
The corrected shared Rust and MSRV plans both passed on `ed462c8b`: 960 passing
all-target tests each, 52 existing ignored tests each, over 102 targets. The
Rust plan additionally passed the dialect/primitive-omission/doc checks. The
52 ignored tests are not successes. Native preparation builds and audits the
pinned checker before its consumers.

Earlier complete native-manifest and distribution checks passed on their
recorded earlier revisions. They are not relabeled as final-commit checks.
The installed Python connection tests passed 12 cases; installed PyQIR/native
tests passed 10 with no optional skip. External parser tests passed 4 using
local LLVM 22.1.6, which does not substitute for CI's LLVM 18 lane. Fixed mdBook
0.5.4 build and generated/print-page link checks passed separately.

Constitutional continuity was checked against reviewed base
`38baae7d19535602b21270e11e97617d45205b37`. QS-2026-01, PR-2026-01,
RS-2026-01 and EXACT-2026-01 retain their broader pending duties. Both admitted
QLV1 ownership/scope guarantees retain their exact scope and current bindings.
This identity check is not a fresh proof replay or a human adequacy judgment.

No new hosted run has checked the local repair commits. The approved final
condition—every required context passing for one exact commit without replacing
failures by retries—has not been met. Review completeness, regression success,
formal proof coverage and release readiness remain distinct.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
