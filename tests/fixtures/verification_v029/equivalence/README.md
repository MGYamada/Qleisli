# Historical independent verifier acceptance comparison

On 2026-10-03, **799 distinct artifact/request pairs agreed: 263 accepted and
536 rejected, with zero acceptance disagreements or expected-result failures**.
All 19 ordinary `RawOp` constructors have accepted coverage. This is finite
differential evidence for ordinary QIRF validity, not a proof of universal
Rust/Lean equivalence, quantum semantics or source preservation.

The [record](results.json) binds the actual sources, binaries, toolchains,
decisions and input hashes. The [original inputs](inputs.jsonl.gz) retain one
JSON object per case; `artifact` and non-null `request` contain base64-encoded
original bytes. Duplicate inputs are executed once and retain their other
fixture/source names as `aliases`.

## Independent decisions

The historical two-verifier harness (removed after the Lean cutover) invoked:

```text
qleisli verify-ir ARTIFACT --format=json [--against=REQUEST]
qleisli-kernel --qirf-dual
```

The native command receives QLV1 framing of the **same original artifact and
request bytes**. Rust does not select or validate the inputs sent to Lean.
Both run even when the other rejects. The combined `--lean-kernel` CLI route
is deliberately not used to measure either independent decision: its logical
intersection could conceal a disagreement.

Known positives and negatives also assert their independent expected outcome,
so two always-rejecting verifiers cannot pass. Fixed-seed field mutations assert
agreement without assuming every mutation is invalid. Process failure,
timeout, malformed protocol or a missing/mismatched request flag fails the run;
none is counted as an ordinary matching rejection. Counterexamples are saved
as standalone artifacts/requests and cause a nonzero exit.

## Coverage

| First-origin family, after deduplication | Distinct pairs |
| --- | ---: |
| Frozen VM22 QIRF1/2 and source artifacts | 20 |
| Current small corpus and selected source fixtures | 78 |
| Pure raw bodies, including generated small circuits and faults | 94 |
| Observing/classical bodies and ownership/scope faults | 55 |
| Independent meaning, exact phase, type shape and source requests | 50 |
| Malformed JSON/profiles and valid serialization variations | 20 |
| Seeded nested-field mutations | 482 |
| **Total** | **799** |

The generator freshly compiled all 84 current corpus clients with at most four
qubits and two VM29 fixtures, then deduplicated identical IR. Pure and observing
bodies reuse the existing independent small-component fixtures; those bodies
are wrapped as production QIRF. Component-only runtime values, separate matrix
requests, altered budgets and retained-component schemas are not silently
treated as ordinary validity premises. Retained evidence in actual source
artifacts remains in the original bytes and in the mutation pool.

Negative coverage includes dead/duplicated quantum owners, missing Unit owners,
wire/axis changes, dirty cleanup, invalid effects, classical SSA reuse, lexical
scope escape, invalid unselected arms, phi ordering, dangling evidence, wrong
global phase, tuple shape and source binding. Mutations use seed `2903102026`;
512 attempts yield 482 additional distinct byte pairs, including valid changes.
No new maximum-size case is generated or executed.

## Diagnostic differences and limits

Acceptance agrees, but **294 rejected pairs use different diagnostic codes**:
289 are Rust `format` versus Lean `invalid_ir`; five are Rust `invalid_ir`
versus Lean `contract`. The native protocol intentionally uses coarse error
categories. These differences are retained, not normalized into a claim of
identical diagnostics. Work counters, messages and execution outputs are not
the comparison predicate.

User review on 2026-10-03 classified the 294 diagnostic-code differences as a
bug follow-up for the v0.3.1 TODO in
[Issue #275](https://github.com/MGYamada/Qleisli/issues/275).
The observed v0.2.9 acceptance result remains
799 agreements and zero disagreements; this follow-up concerns classification.

This is ordinary QIRF1/2 acceptance with optional supported requests. Hierarchy
protocols, arbitrary resource limits, source/runtime equivalence, compiler
correctness and exhaustive inputs remain separate obligations. All S05 gates
remain open; production authority and enabled schemas are unchanged.

## Reproduction and performed checks

Use a **new** record directory on each run; existing evidence is not overwritten:

```sh
cargo build --locked --offline --bin qleisli
(cd lean-kernel && lake build)
python3 scripts/test_verifier_equivalence.py --record /tmp/qleisli-equivalence-new
python3 scripts/test_test_verifier_equivalence.py
```

The saved run uses the debug CLI, matching the new native CI group, and the
Lean 4.30.0 native executable on macOS arm64 with Rust 1.98.1. A preliminary
release-CLI run produced the same 799 decisions. Local checks also passed:
seven harness regressions, thirteen native-runner regressions, six CI-profile
regressions, the 107-module source policy, the compiled audit of 11,425
kernel/transport declarations, and the unchanged production coverage gates.
The compiled audit used only `propext`, `Classical.choice` and `Quot.sound`.

[Native CI](../../../../.github/ci/native-comparisons.json) now builds the host
and runs this comparison as its own group; harness regressions run in the
workflow too. Hosted CI has not been run for this uncommitted workspace.
The Rust/Lean production implementation and proof sources were not changed for
this test addition; full release replay was not rerun.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.

After cutover, replay the unchanged original inputs and decisions using
[the native replay harness](../../../../scripts/test_native_acceptance_replay.py).
There is no current Rust semantic verifier to compare against.
