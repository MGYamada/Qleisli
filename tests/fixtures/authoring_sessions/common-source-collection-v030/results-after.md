# Actual source-collection replay

The authorized [after-final capture](after-final/summary.json) completes all
23 original commands using the rebuilt CLI. [Exact comparisons](after-final/comparison.json)
find **zero differences** in exit status, original stdout/stderr bytes, native
invocation count and proposal presence. The one emitted helper proposal is also
byte-identical: 16,831 bytes, SHA-256
`25eea53f22c07a944a1043b816e7744a6d5ee8365ca0727ce50a660e2f4f1deb`.

The five successful commands and eighteen rejections retain their scopes.
Finite bundled-QFT checks invoke the unchanged native checker 22 times each;
sized helper checks invoke it once each; untrusted proposal emission invokes it
zero times. All negative check/emission commands reject before native checking
and produce no proposal. Earlier profile rejection still precedes a later parse
failure, while the reverse-order control still reports the earlier parse error.
No diagnostic-order change is waived.

[Captured after identity](after-final/identity.json) records CLI SHA-256
`9906ea86e6a88086476558d95ce3ac4b34636c4467402e055adbe84ddcb1db5d`.
The native checker remains
`39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85`;
all retained Lean-kernel and stdlib source/manifest hashes match the baseline.
The current production Rust map records the new `src/frontend/source.rs` and
changes in `mod.rs`, `project.rs`, `sized/check.rs` and `sized.rs`. The current
Source Text and Primitive Boundary References are separately captured rather
than silently rebound to their baseline hashes. Protected constitutional and
governance text is unchanged.

HEAD remains the record-only
`5aee1b3cfde51e347cbff83c76526d22cf249d33`; the changed Rust work is uncommitted
in that capture. This record does not claim that this HEAD contains the new
implementation or cryptographically attest compilation. The observed CLI,
current source and contract identities stay fixed throughout the replay.
The separate wrapper verifies the full original input/output baseline before
and after; original source bytes, first records and proposal are unchanged.

These results corroborate this bounded private collection refactor. They do
not establish general source preservation, common checker completion, canonical
generic stdlib QFT exposure, independent semantic requests, mathematical proof,
new guarantee admission or release readiness. No quantum execution, maximum
case, Cargo/Lean build, Git mutation or Issue mutation is performed by this replay.
Subsequent MSRV work may replace the current CLI; these recorded bytes retain
the actual replay identity without a later executable being substituted.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
