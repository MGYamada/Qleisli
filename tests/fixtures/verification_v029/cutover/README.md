# Native-only production cutover validation

Recorded 2026-10-03 in the unpublished v0.2.9 working tree, under
[decision #276](https://github.com/MGYamada/Qleisli/issues/276). This is a fixture
validation record, not a replacement migration plan or a release declaration.

`src/verify.rs`, the root `verify`/`VerifiedProgram` API and `interchange::dual`
are removed. The former migration-plan document is deleted without an archive
copy. Native `Kernel` acceptance now covers raw/source/QIRF, CLI, Python/foreign,
function-evidence DAGs, encoded contracts, finite leaves and hierarchy adapters.
Only a fresh native decision constructs an accepted handle. Rust generates
bounded proposals and decodes the exact immutable accepted bytes for execution;
post-rejection matrix calculations only explain a failed decision.

Select the matching checker explicitly with `QLEISLI_KERNEL`, a CLI
`--lean-kernel=PATH`, or a Rust `Kernel`. The launcher supplies product version
0.2.9; malformed replies, version mismatch, failure, absence and capacity errors
cannot authorize execution. Cargo compilation/documentation requires no Lean.
The native runtime is Mathlib-free and pinned to Lean 4.30.0. A selected path is
deployment identification, not cryptographic executable attestation.

## Recorded checks

| Check | Observed result |
| --- | --- |
| [Original-input replay](replay/results.json) | 799 original pairs: 263 accepted, 536 rejected, no mismatches; one empty proposal rejected at the size boundary. Source/binary hashes are bound before and after replay. |
| [Source-generated handles](examples-handles.json) | All 14 example projects emitted intact QIRF and obtained native accepted handles, including the four multi-program evidence/source-table cases in #277. |
| [Example execution](examples-execution.json) | All 14 examples ran and sampled successfully; this record is a smoke check, not an independent probability proof. |
| Source regressions | Four `test_source_kernel.py` tests passed. The retained-evidence test checks all four #277 examples against their authored deterministic outcomes, including phase-bit order. Existing `qli_corpus`, `iterative_qpe` and operation/evidence tests retain independent semantic oracles. |
| [Public routes](public-paths.json) | 241 native/CLI checks, including 84 existing corpus clients of at most four qubits, malformed binding, missing checker and wrong version. Both selection mechanisms use the same native implementation. |
| [Python/foreign routes](interop.json) | All 10 tests passed with PyQIR installed, including QIR text/bitcode, all CLI actions, immutable output binding and failure envelopes. |
| Contracts/handles | Focused function, finite-leaf, encoded-contract, native-handle, source-binding and negative-equation tests passed. Compile-fail doctests reject unchecked execution and external implementation of the sealed simulation trait. |
| Rust suite | The broad run completed 72 targets: 574 passed, two old capacity expectations failed, 49 ignored. The failing `review_v020` target was then updated as described below and rerun: two passed, four explicitly ignored. This is not reported as a wholly passing broad command. |
| Build/lints/docs | Cargo check/build, Clippy with warnings denied, rustdoc with warnings denied and doctests passed. |
| Native proofs/policy | Fresh build, declaration audit, reductions and `leanchecker` replay of `QleisliKernel`/`Main` passed. The native audit covered 11,441 declarations; only `propext`, `Classical.choice`, `Quot.sound` occurred as axioms. |
| Schema/model maintenance | Both Lean packages rebuilt/audited; registry refreshed with three internal entries and zero externally enabled schemas. |
| [Native bundle](native-bundle.json) | Fresh macOS arm64 bundle, full native proof lane, source/binary hashes, licenses and relocation smoke passed. |
| [Installation](installation.json) | Offline Cargo package verification and fresh Cargo installation passed. Installed CLI plus relocated native checker passed Bell/QFT/negative ownership outside the checkout with an empty helper-tool PATH. |
| Inventory/policy | 232 constructor variants, 233 source snapshots, 36 groups and 20 public boundaries reviewed. Inventory, coverage, CI runner/profile, packaging/distribution and documentation unit checks passed. |

[Validation metadata](validation.json) and [logs](logs/) distinguish initial
failures from later focused successes. The initial broad run also encountered
transient checker replacement during rebuilding; it is retained as a failed
run and is not acceptance evidence. The final replay binds the final production
sources; other records retain their actual earlier executable identities.

## Capacity differences retained explicitly

The former Rust admission and work counters are not a promise that every large
program fits the native profile. Native JSON/combined program-evidence depth,
10,000,000 work units per decision, shared caller budgets and a 60-second
process deadline apply. Repeated fresh checks charge source transport again.
Large shared-source receipt tests exhausted work, and long gate/expansion tests
hit the process deadline before their former Rust-specific diagnostic.

Ten historical stress tests remain in source with explicit `ignore` reasons:
two raw scaling cases, one maximum evidence-chain case, one export-capacity
case, four v0.2.0 large-source/trajectory/expansion cases and two 256-receipt
cases. Their capacity and coverage recovery is tracked in
[#278](https://github.com/MGYamada/Qleisli/issues/278), targeted for v0.3.1.
Initial failures are retained in the logs; maximum-size reruns were
deferred under the small-system validation instruction. Small shared-receipt,
round-trip, source-binding and simulation tests remain active. This is a known
capacity/performance limitation, not a solved stress regression or a proof that
batching alone will fix every timeout. Process batching remains
[#274](https://github.com/MGYamada/Qleisli/issues/274); diagnostic differences
remain [#275](https://github.com/MGYamada/Qleisli/issues/275).

The complete clean-checkout native comparison lane, MSRV, other platform
bundles and full release distribution validation were not rerun here. Existing
CI jobs retain those gates. There is no tag, publication or release claim.
Full-profile Soundness, source/native compiler/decoder/runtime correspondence,
hierarchy semantic composition and independent specification review remain
open. External schemas remain disabled; old inputs, counterexamples and proof
components have not been discarded with the Rust verifier.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
