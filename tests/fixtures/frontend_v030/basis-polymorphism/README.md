# Opaque Basis implementation checkpoint (#44)

This packet records bounded ordinary implementation under the adopted
QS-2026-01, PR-2026-01, RS-2026-01 and EXACT-2026-01 requirements. It changes
untrusted common source preparation, explicit type/provider binding and selected
CLI input. Native constructors, checker modes, protected meanings and actual
human adoptions are unchanged. Edition is 2026; the product is 0.3.0-alpha.

The [Reference](../../../../docs/src/reference/type-model.md) specifies ordered
opaque Basis parameters, exact substitutions and generic/instance duties.
The [authoring record](../../authoring_sessions/basis-polymorphism-v030/README.md)
retains first programs and real diagnostic history. Six original abstract
negatives now reach type, ownership or access checking before specialization.
The same original repeat body accepts distinct Bit and Bits types; a separately
bound opaque provider forwards the exact caller type after a manifest repair.

The tests preserve Unit/Bit/Bits tags, tuple order/nesting, provider-local
substitutions and complete specialization keys. Generic checking still covers
unused declarations, both static arms and zero-iteration bodies. Host and source
type bindings obey the same closed capacity even when a parameter is unused.
No width-only substitution, implicit coherence, runtime type reflection or
quantum preparation of an opaque type is introduced.

## Validation and retained failures

- `generic-first-check/`: six tests pass, two fail. The test incorrectly expected
  a type error from dropping a quantum owner, and used the wrong public
  reference-amplitude order. Original test text and actual output are retained.
- `generic-repaired/`: the corrected four-target run passes 37 tests.
- `cli-first-check/`: eight tests pass; the new CLI test incorrectly expects a
  modern IR-profile JSON field on the legacy adapter. Original test text and
  actual tool observation are retained.
- `cli-repaired/`: the driver selects the wrong environment variable for the
  native checker, so seven tests pass and two fail before native use.
  `cli-native-repaired/` supplies QLEISLI_KERNEL and passes 71 tests.
- `final-latest-focused/` and `final-latest-library/`: Rust 1.98.1 passes 136
  integration and 57 frontend library tests. Four existing ignored tests and
  51 filtered library tests remain; no ignored test is activated.
- `final-msrv-focused/`: Rust 1.85.0 passes the nine selected targets, 72 tests
  with two existing ignored tests. This is not a full MSRV runtime run.
- Both final all-target Clippy runs and the final format check pass. All six
  final Rust records identify the unchanged checked inputs and selected native
  binary. The bounded target directory is reused with incremental/debug output
  disabled and two build jobs.
- `documentation/`: source/API inventory, production routes, coverage-checker
  tests, editions, authoring records, documentation and constitutional continuity
  pass. mdBook 0.5.4 builds the book. The corrected offline HTML validator checks
  23 pages and 743 local links/anchors, including print.html. Its first failure
  incorrectly resolves the generated 404 page's site-root link as filesystem
  root; that result remains. External/deployed links are not checked.

The independent small complex oracle uses one system bit or a Unit scalar and
a two-dimensional external reference for repetitions zero through four.
Its explicit expected X permutations and eighth-turn scalar phases are separate
from the producer's comparison request. Fresh native acceptance of that request
is a consistency check; it is not an independent algorithm specification or a
generic/source preservation theorem. No new maximum-size quantum case is
generated or executed. The nine-field capacity rejection emits no IR.

## Limits and remaining work

`inventory-review.json` records reviewed source/API/constructor deltas and the
unchanged original corpus/fault pins. The native executable is reused at
SHA-256 `39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85`;
this packet contains no fresh Lean build, audit or replay. Constitutional
continuity is checked against reviewed commit
`faa5cfb5e7ea1cf3b39a43b80f7f2345e89197c2`.

#44 remains open. General `Op<A,M>`/Meaning refinement, final project-profile
convergence and the issue's complete preservation/evidence criteria remain
unfinished. The two human-admitted ordinary QLV1 guarantees keep their exact
scopes; broader QS/PR/RS and EXACT obligations remain pending. Local checks do
not certify same-commit full CI, a release, a new guarantee or an Issue closure.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
