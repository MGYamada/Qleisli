# Shared physical Raw state and mixed Boolean execution

This checkpoint implements mixed quantum/ordinary execution within
[Issue #32](https://github.com/MGYamada/Qleisli/issues/32). It does not finish the
common frontend, public invocation/CLI integration or the 108-Issue plan.
Edition 2026, product version 0.3.0-alpha, native schemas and dependencies are
unchanged. No Lean definition or human adoption record changed.

## Implemented behavior

Finite and sized Raw emission share one physical register map, operation list
and fresh token/wire/classical/slot supplies. Initialization, single-bit gates,
CNOT, measurement and Boolean emission use the same transitions. Existing finite
source type/effect/ownership judgments, charging and diagnostics remain in their
adapters. Branch snapshots restore registers/operations, never fresh supplies;
the whole state has no Clone implementation. Existing computed/certified bodies,
branch phi handling and zero-width phase semantics are retained.

The sized Raw API now supports exact Unit/Bit/Q<Bit>/products, specialized
ordinary calls and static folds, Boolean operations, init0/H/X/CNOT/measure_z and
representable dyadic phases. Source-ID environments are per-call activations;
the physical state spans pending arguments and suspended callers. Quantum reads
consume source bindings while classical values remain copyable. Measurement
consumes its owner and produces the Bit used by subsequent ordinary computation.
Whole source argument/result trees remain beside the separated Raw interfaces.

A dyadic phase retains the existing k<=8 and j<2^k source domain. Raw emission
requires 8*j/2^k to be integral, then emits exactly that many T gates. The zero
case retains its source step/owner transfer while emitting no gate. Angles are
never rounded. The existing hierarchy accepts the frozen fine phase [1,4]; the
Raw rejection of that same program is its target limitation, not a language or
edition change. Providers, controlled-phase primitives, Bits and other quantum
bases, runtime branches, open invocation and CLI convergence remain required
work. No failed native decision is retried under a weaker request.

The independent source-step matcher does not call the emitter or RawState. It
checks exact source trees, ordered gates/CNOT/measurement/Boolean instructions,
fresh physical identities, source binding consumption, per-call suspended
frames, all final live owners and full instruction consumption. Both paths
retain bounded calls/cells/operations and the existing global 16-live-wire
limit. Source-step agreement is not a proof of AST elaboration or native/runtime
correspondence. Only the existing native gate grants accepted handles.

## First sources and review

The [mixed authoring study](../../authoring_sessions/mixed-boolean-v030/session.json)
froze twelve complete projects before thirty-five baseline observations. Its
28-file first-source manifest is
33a52701db444ded0f561284e6fd74402659059dbd018ef318fa596a0ef27ad7;
the complete 68-file study manifest is
879a4eaef0b3e31f721c3a6101b8e911c96d987389d3a7412e1b8df4667db5bc.
Original sources and observations remain unchanged. The old binary accepted
both exact and fine phase through hierarchy, while rejecting mixed sized CLI
examples. Finite closed Bell and pending-argument probes already matched the
independent expectations.

Independent source review found and fixed a BasisShape constant spelling and
lost error module/call-site locations before execution. A separate test review
found an invalid [9,3] positive phase draft; first-test.rs.txt preserves that
**unexecuted** draft and test-repair.json/test-repair.patch explain its correction
to a located elaboration rejection. No fictitious failing execution is claimed.
The first actual latest/MSRV test runs both succeeded. Independent reviews of
state extraction, mixed emission, matcher/frame invariants and test oracles are
recorded in review.json; these are assistant reviews, not Guardian judgments.

## Actual validation

Each of actual Rust/Cargo/Clippy 1.98.1 and 1.85.0 passes:

- 84 tests across ten focused integration targets;
- five direct source-step replay tests, including four new mixed tests;
- all-target Clippy with warnings denied and formatting.

Both successful runs bind the same 280 selected source files with manifest
5ea09289c92af27cb5e5c0cc1118d90221eb288cf0abf5277eded2871dd1d133.
This selected manifest is not a complete dependency/input closure; other
retained fixtures remain at the recorded Git base. This is not all-target
runtime validation or a new Lean build/audit/replay. The existing native checker
was reused with hash 39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85.

Independent expectations cover eager 0-and-measurement effects, Bell (a,a xor b)
outcomes 00/10 at one half, and a pending q argument while its entangled r is
measured before X(q), yielding 10/01 at one half. Repeated helpers and static
zero/one/two folds preserve fresh identities. Four exact phase representations
are checked against independently requested diagonal meanings, actual exact
matrix coefficients and H-T-H interference. Existing source-call/branch,
computed/certified and Q<Unit> tests also pass.

The independent matcher tests author Raw instructions directly. Native-valid
mutations of H, CNOT direction, measured owner, unused quantum work and output
order are rejected by the matcher after native acceptance. Open mixed input and
output order, retained caller frames and nested exact/zero phase are covered.
These tests distinguish native validity from source-step correspondence and
from the immutable proposal's outer byte identity.

cli-build.json binds the rebuilt current CLI to its sources and hash
ba2913eb473aef4387f24b59cfba68d6476d83c793d64d6f8e3af18d520b1462.
observe_cli.py constructs commands itself, never executing historical command
strings. All 35 baseline CLI observations have identical exits/stdout/stderr;
three previously stored named-control IR artifacts are byte-identical. Sized
CLI routing remains unchanged: these observations do not claim it invokes the
new mixed Raw API. The Rust tests establish the new execution behavior.

Inventory/coverage, 14 coverage and 15 scheduler regressions, authoring,
constitutional/edition identities and documentation checks pass. The native
manifest now has 67 groups / 86 commands and includes the mixed integration suite;
its existing raw_source_replay filter runs all five library tests. Pinned
mdBook 0.5.4 builds 20 HTML files; rendered/print checks cover 741 links / 266 anchors.

All local compilation reuses one fixed external target with incremental
compilation/debug information disabled and two build jobs. No new full source
snapshot, large Lean build, maximum-size quantum case or historical bulk
removal was performed. Full same-commit CI and release validation remain open.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
