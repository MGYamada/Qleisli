# Rust-boundary diagnostics: bounded implementation and review

This unit implements the [ordinary #68 decision](https://github.com/MGYamada/Qleisli/issues/68#issuecomment-6009785277)
on the public source baseline `f5081d175bb6287107b4feea3ffac0538501851f`.
It explains an existing rejection; it does not add Rust destructors, change
accepted source, select a physical repair, or complete the parent or child
Issues. The [current Reference](../../../../docs/src/reference/rust-boundary.md)
distinguishes implemented behavior from remaining access/place/failure designs.

The source change attaches conditional explanations to unresolved
`drop`/`forget`, `clone`/`copy` and `default`, and to five existing implicit
quantum-owner-loss branches. Ordinary Bit/Unit and purely ordinary products
remain reusable and ignorable. Resolved user functions named `drop` remain
ordinary functions; local callable-category errors retain their original
priority. Quantum-containing products, including nested zero-width owners,
remain linear. Reset returns a fresh owner, which must itself be accounted for.
There is no invented standalone release API.

## First sources and corrections

- [Before-source observation](observed-before-01.json) and the exact original
  body/source-scope files preserve the public baseline before production edits.
- [Prepared independent tests](prepared-01.rs.txt) and
  [test plan](prepared-test-plan-01.json) precede their first executions. The
  same four tests remain in `tests/rust_boundary_diagnostics.rs`.
- [After-source observation](observed-after-02.json) corrects the earlier
  observation's manually written timing sentence. Original
  `observed-after-01.json` remains unchanged; the correction changes no source
  or executable digest field.
- [Invocation observations](invocation-observations-01.json) retain the two
  incorrect nonexistent-script invocations and the real inventory identity
  refusal before review. Those commands are not successful verifier runs.
- [Reference correction](reference-review-correction-01.json) retains the
  initial prose and the independent finding: mere separation is insufficient
  for exact return to the specified fixed pure state. The corrected Reference
  states factorization with that same fixed-state factor under the adopted
  all-input channel premises; this is no new interpretation.
- [Inventory refresh](inventory-refresh-01.json) retains the original VM-22
  inventory and changes only the reviewed body source digest. Public surface,
  constructors, boundaries, capacities and coverage groups remain unchanged.

## Actual validation

The [validation directory](validation-01/) retains explicit argv, environment,
exit status, elapsed time and the hashes of actual raw streams. The runner
accepts newly supplied commands and refuses record overwrite; it never
executes commands read from retained evidence.

| Check | Actual result |
| --- | --- |
| Rust 1.98.1 and MSRV 1.85.0 | 23 tests each: 13 body-effect, 3 functional-boundary, 4 diagnostic and 3 scope tests; all passed. |
| Cargo Clippy, both toolchains | All targets with `-D warnings` passed. This compiles tests; it is not a full all-target runtime run. |
| CLI build and format | Passed, using the reused bounded target and two build jobs. |
| Public first-source study | Nine unchanged projects, 42 actual before/after calls, zero source repairs; original public codes, spans, exits and three small run distributions agree. |
| VM-22 / VM-29 | Reviewed source inventory and production coverage passed; wider Soundness duties remain open. |
| Constitution | Continuity passed against trusted `faa5cfb5e7ea1cf3b39a43b80f7f2345e89197c2`; no protected record changed. |
| mdBook 0.5.4 | Both initial and corrected Reference builds passed; rendered-link inspection includes the print page. |
| Authoring / edition records | Integrity and explicit edition-2026 coverage passed; recorded commands are not replayed by integrity checks. |

The [separate informed study](../../authoring_sessions/rust-boundary-diagnostics-v030/README.md)
retains two original prediction mistakes (`name` versus public `unknown_name`),
all first source files, raw results and the comparison. Five designated
rejection explanations change; eleven paired observations keep both raw
streams exactly. This is bounded evidence, not universal source equivalence.

The selected local native executable digest is
`39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85`.
The before/after CLI digests are respectively
`bd9219f7847f1a7a52a3bd1346d39e8455edf0988e04582595471ae439b5feef`
and `d140ae375e1319f3cc353fe475178357355f921b5dae515a98a785b06ca8bb5d`.
These identify local bytes, not an authenticated complete build closure.

No fresh local Lean build, axiom audit or proof replay is claimed for this
error-message-only change. QS/PR/quantitative RS/EXACT remain pending beyond
the two protected ordinary QLV1 ownership/classical-scope guarantees. Generic
QFT work and maximum-size generation remain excluded. External qlippy
diagnostics are omitted with the maintainer's permission; actual Qleisli
diagnostics and Cargo Clippy are checked. Full hosted CI, packaging, fresh
installation and exact-commit release gates remain separate.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
