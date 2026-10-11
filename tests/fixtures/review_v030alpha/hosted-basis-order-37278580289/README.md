# Hosted ordered-kind fixture repair

Run 37278580289 failed MSRV all-target testing because an active positive fixture
put `static U: Op<Bits<n>>` before `static n: Nat`. #44's recorded 2026-10-04
contract and its 2026-10-05 before-code unit require parameter kinds to depend
only on earlier parameters. The current Reference repeats that rule. The checker
therefore correctly rejects the original source with `static: unknown natural
name n`; this failed run remains failed.

Migrate only the two active fixture declarations and positional call arguments
to `[n,U]`. Preserve the original complete test source and actual hosted/local
failure logs. Keep the existing forward-kind negative in
`tests/basis_polymorphism.rs`, along with size and Controlled-access forwarding
negatives in `tests/sized_source.rs`. This changes no source grammar, compiler,
primitive, native checker, semantic representation, capacity or acceptance rule.

The relevant QS/PR/RS and EXACT interpretations still apply; both admitted QLV1
ownership/scope guarantees retain their exact scope and meanings. No new Guardian
act, discharge, release readiness or completed Issue is claimed. The selected
scope remains 110 and verified completion 13/110 (11.82%).

## Performed validation

The original focused test was reproduced with actual Rust 1.85.0: exit 101,
`static: unknown natural name n`, one failed test and forty filtered. The
`before/` record remains unchanged. The migrated fixture and existing Basis
tests pass with each actual Rust 1.98.1 and 1.85.0: 48 passed, three existing
native-only tests ignored. Both focused Clippy runs and formatting pass.
Constitutional continuity against reviewed faa5cfb5e7ea1cf3b39a43b80f7f2345e89197c2,
verification inventory and production coverage pass. No source/checker file
changed, and no fresh local Lean build/replay was run.

The first complete `after/` validation retained a documentation-check failure:
the unmodified GitHub Issue transcript used a `.md` extension and its source
fragment was interpreted as a local Markdown link. The same raw Issue bytes are
now `issue-44-before.txt`; maintained Book sources and link checks are unchanged.
`doc-format-repaired/` records the subsequent actual docs check and diff check.
All runtime source-file bindings were verified unchanged after this file-format
repair. The failed first docs result is not overwritten or recorded as passing.

The complete decoded latest-Rust and MSRV hosted logs identify the same active
fixture failure on actual PR checkout d152df1f4bb9c662eaefbdecb056c85474f51127
for branch head dc3c8c633b959c9acbbffd29bbfe70f13e032491. The distribution
job log records failure of source all-target Cargo testing with exit 101;
its detailed archived source-test output was not downloaded here. Docs,
interop, both Lean and macOS producers succeeded. This is an unsuccessful
hosted run and cannot certify a new candidate. Producer observation predates
terminal aggregate jobs and does not claim their success.
