# Exact Unit pattern integration

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

This implements the bounded ordinary Unit pattern unit recorded in
[Issue 43](https://github.com/MGYamada/Qleisli/issues/43), under the existing
[type contract](../../../../docs/src/reference/type-model.md). It does not
complete the parent Issue, general parameter patterns, pure quantum Unit
introduction/elimination, or a source-preservation theorem.

The [first study](../../authoring_sessions/finite-unit-pattern-v030/README.md)
preserves 19 inputs and actual baseline diagnostics before implementation.
Seven desired forms originally reached the finite profile rejection; three
named controls passed; eight counterexamples and one desired runtime parameter
pattern rejected. Those original bytes and observations remain unchanged.

The implementation shares one exact immediate shape judgment across finite
basis/runtime and sized symbolic/concrete binding. Empty patterns match only
ordinary Unit. Coherent basis matching still emits the checked quantum lift;
ordinary runtime matching cannot erase a Q<Unit> owner. Ordinary function
parameters remain names, including a fail-closed check of constructed ASTs.

## Actual bounded validation

- Rust 1.98.1 and the actual Rust/Cargo/Clippy 1.85.0 each passed 33 integration
  tests across four targets, one constructed-AST library regression, and
  Clippy for the new integration target with warnings denied. See
  [latest result](latest-final/result.json) and [MSRV result](msrv/result.json).
  Each record binds 241 source inputs and verifies their stability.
- The [eight new tests](../../../unit_patterns.rs) inspect exact accepted
  scalar meaning, coherent-control interference, retained effectful Unit
  computations, shape/owner/effect/arity rejections, and sized execution with
  two-dimensional reference inputs. The scalar multiplication loop is an
  algebraic consequence of coefficient equality, not separate native reference
  executions. Its independent expected coefficient is the exact eighth root
  of unity; the control probabilities come from its analytic phase.
- [CLI observations](cli-after.json) retain 25 actual calls: the 19 original
  checks now give ten expected successes and nine expected rejections, and
  three unchanged small programs emit byte-identical IR under the original
  and new executables. The new CLI came from the recorded MSRV build.
- Both builds reused the same existing audited native checker; no new Lean
  build, audit, replay or guarantee admission is claimed. Edition 2026 and
  product/dependency versions are unchanged.
- Current source inventory, production coverage, edition/authoring/constitution
  identity, native scheduler, formatting and documentation checks passed.
  The pinned mdBook 0.5.4 build passed; its 20 HTML files, 741 local links and
  266 anchors include the print page. These checks are summarized in
  `metadata-validation.json`; summaries without raw logs are labelled there.

## Retained failures and repair scope

[The first test run](latest/result.json) found the now-unused finite `fields`
helper and pre-cutover negative expectations in `tuple_shapes.rs`. The latter
incorrectly rejected ordinary Bit discard, Q<Bit> identity and basis Bit
identity. They are now explicit positive cases; actual coercion, nested-Q and
finite-register-profile negative cases remain.

[The second test run](latest-fixed/result.json) passed all prior targets but
one new simulation assertion required exact floating equality after Hadamard:
the actual probability was 1.0000000000000002. The corrected assertion requires
exactly the expected output key and probability within 1e-12. Exact IR equality
and exact scalar checks retain exact equality. The subsequent successful
records remain separate from these failures.

The [first CLI observer failure](cli-first-failure.json) omitted emit-ir's
required output path and failed before retaining child output. Its original
driver is preserved; the corrected driver saves every command result and
compares emitted artifact bytes. No missing transcript is fabricated.

## Disk and evidence limits

The validation reused one fixed `/private/tmp/qleisli-bounded-validation-target`
with incremental compilation and debug information disabled. After both
toolchains it occupied about 361 MiB; repository `target/` remained about
13 MiB and available disk space about 26 GiB. No repository copies, native
builds, maximum-size corpus cases or historical temporary-tree deletions were
performed. The fixed output directory is reusable, not a new directory per run.

`inventory-delta.json` changes only seven reviewed current source rows and
their public coverage identity; historical pin values are unchanged.
The fixtures record bounded implementation evidence, not all-target CI,
full release readiness, publication or new constitutional guarantees.
