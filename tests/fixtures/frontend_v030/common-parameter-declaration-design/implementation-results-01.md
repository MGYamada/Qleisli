# Completed bounded parameter-name implementation

The three-file implementation factors spelling insertion and iterative runtime
parameter-name traversal into private helpers consumed by finite and sized
declaration checking. Sized checking obtains the original common declaration
through the actual resolved module and AST index, with complete parameter-count
assertions before ordinal association. Existing type/kind/premise/access,
static-shadow, value/owner and whole-project stages retain their order. This
does not finish a common declaration/body checker or adopt a new language rule.

The concrete contract and ten first projects were preserved before code. Root
ran forty finite/selected text/JSON checks: four successes, thirty-six
rejections and forty-four native calls. A separate after capture matched all
raw stdout/stderr, statuses and native argv/counts without normalization.
The original thirty-four first files and complete two-hundred-file before
packet remain unchanged. No source repair, runtime, emit or algorithm oracle
was part of that experiment. Earlier profile/projection failures remain distinct
from downstream declaration failures. See the separate
[before](../../authoring_sessions/common-parameter-declaration-v030/results-before.md)
and [after](../../authoring_sessions/common-parameter-declaration-v030/results-after.md)
observations.

Root's actual Rust 1.98.1 and MSRV 1.85.0 runs each completed eight stages:
118 tests passed, zero failed, three existing sized ignores; formatting,
all-target compilation, Clippy with warnings denied and CLI build passed.
Two unrelated 3000-file import stress cases were explicitly skipped. Each run
retained 714 declared input identities; those maps are incomplete build/fixture
closures. The comparison used the observed latest CLI; the subsequent MSRV
build changed the shared executable and is not substituted for that comparison.
No failed compiler stage occurred in these two runs. Raw outputs and actual
commands are preserved in [validation (archived)](validation/README.md) (`validation/README.md`).

The [independent implementation review](independent-implementation-review.md)
found no actionable defect in the stable three-file diff. The reviewer did
not author production code, but did author the earlier design candidate; the
candidate follow-up is explicitly self-review. Technical review, execution,
specification authority and proof remain separate.

The current metadata review found stale source identity before refresh
(inventory exit 1), then inventory and coverage passed after refreshing only
three source hashes and the derived aggregate. All 253 source identities
remained stable; public surfaces, acceptance routes, criteria and proof/status
fields were not expanded. Historical 17/14 metadata mutation results were
retained separately and were not rerun for this unit.

Root then executed the fixed [policy driver](policy-validation/driver.py): all
13 commands and 66 regression tests passed, with 817 declared input identities
unchanged. Pinned mdBook 0.5.4 built the Book; rendered checks covered 23 HTML
files, 920 local links and 343 anchors, including print pages. The generated
3,854,939-byte tree was removed only after its file hashes and check logs were
saved. Source documentation checking covered 1,921 links, 19 Markdown anchors
and 206 Lean roots. Authoring checks inspected 35 records, 50 snapshots and
678 observations without executing recorded commands. These checks did not
fetch external URLs, run Cargo/native/Lean commands or create release receipts.

Constitutional continuity passed against the previously reviewed
`faa5cfb5e7ea1cf3b39a43b80f7f2345e89197c2`. Current source/evidence identity
checks preserve both scoped ordinary QLV1 guarantees; they are not fresh Lean
replay or human guarantee admission. QS-2026-01, PR-2026-01, RS-2026-01 and
EXACT-2026-01 retain their broader pending obligations. No protected record,
Lean/native/stdlib source, dependency version or edition changed.

All original frozen maps remain separate from additive final packet maps.
Six exact captured patch/libtest paths have scoped Git attributes preserving
their raw bytes; maintained-source whitespace rules remain active. No hidden
Git override or blanket fixture exception is used.

This is local component evidence. Hosted run 37336154083 checks the different
merge commit `7549cecca246b9335a3e1b8f9e4a176df8827d0a`
and must not be attributed to this local change. The exact merge identity is
recorded in its separate checkpoint; no full-CI or release-readiness result is
claimed here. Source/runtime preservation, analytic Fourier/family proofs,
canonical std migration, all #32/#317 conditions and same-commit release gates
remain required. Confirmed whole-plan completion remains 14/111 (12.61%).

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
