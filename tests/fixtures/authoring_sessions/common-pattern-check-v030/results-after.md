# Shared runtime-pattern comparison

The fixed after driver ran only after the actual Rust 1.98.1 CLI rebuild
recorded in `../../frontend_v030/common-pattern-design/validation/latest-attempt-02/`.
Its selected binary SHA-256 was
`58acd18d36849646e4d3d7819651fbb98128c3f5436f86e737b769b86c67c969`.
The original first source, driver, session and all 191 baseline records remain
unchanged. [after/summary.json](after/summary.json) retains the 40 new observations.

All 40 comparisons match exactly: exit, raw stdout, raw stderr, native argv
and count, proposal presence and exact bytes. No output-path substitution was
needed. Eight checks and two untrusted proposal emissions succeed; thirty
commands reject. The selected native binary remains
`39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85`.
There are 86 actual native invocations in each capture, including the finite
unused-invalid sibling's earlier per-entry check before whole-project rejection.
The empty-register finite case retains its earlier profile rejection; it is
not evidence that finite lowering ran the zero-width wildcard rule.

Every command guards 235 current source/contract inputs and the fixed CLI and
native identities. This declared map is incomplete compilation/runtime closure,
and binary identity does not attest a Git commit. Emission is untrusted;
native producer consistency does not prove source correspondence. The study
does not run/sample programs, establish a new mathematical oracle, complete
common checking or expose canonical std/QFT. Broad QS/PR/RS/EXACT duties and
both ordinary QLV1 scoped guarantees retain their recorded statuses.

The first compiler validation failed on ambiguous `Self::Name`; the separate
design packet retains that actual failure and the explicit `BindingName`
repair. The repaired 1.98.1 validation passes 118 tests, with three existing
ignores and two explicit unrelated import-depth exclusions. MSRV validation
is separately recorded when completed; this comparison does not claim it.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
