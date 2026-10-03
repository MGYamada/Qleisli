# First native accepted-handle migration slice

Historical snapshot: the limitations, commands and results below describe the
first slice. The [completed production cutover](../cutover/README.md) replaces
its execution view and removes the Rust verifier and dual API. The original
source-review, replay and validation records below remain unchanged.

[Decision #276](https://github.com/MGYamada/Qleisli/issues/276) adopts the
exceptional v0.2.9 migration. This record covers its first bounded executable
slice, not completion of the cutover or the v0.5.0 Soundness obligations.

The desired source is the existing Bell quickstart: prepare H/CNOT, then measure
both qubits. A second client measures the first qubit and conditionally flips
the second. Independent expectations are respectively equal-probability 00/11
and 00/10. Tests construct their raw proposals directly, with asymmetric wire
IDs and both branch arms, without first obtaining a Rust verification receipt.

`interchange::native::Proposal` owns untrusted artifact/request bytes.
`Kernel::accept` obtains a fresh native decision; only its private constructor
creates `AcceptedProgram`. The decoder reads the exact ticket's bytes and never
calls the old importer, verifier or equation checker. `sim::run_closed` and
`sim::sample_closed` consume the immutable execution view through a sealed trait;
external code cannot implement that trait for unchecked raw IR. Compile-fail
examples reject proposal/legacy-handle conversions and external trait bypasses.
Returning original `artifact()` bytes requires no reserialization.

Supported view: QIRF1/2, one program, all existing raw constructors, no retained
function-evidence entries or source table. Independent requests still reach
Lean. This is an execution-decoder limit, not a new semantic acceptance rule.
The independently written [T contract](t-contract.qirf) is accepted by Lean but
explicitly rejected as an unsupported view until evidence DAGs migrate. There
is no legacy fallback. `NativeChecked` records the canonical executable path;
this is deployment identification, not cryptographic binary attestation.

The original 799-pair archive is retained under the earlier equivalence record.
All 263 accepted inputs happen to fit this slice's view. Replay invokes only
the new example and native checker, compares the frozen original decisions,
and requires a native rejection response for negative cases. Empty input is
separately classified as a proposal-bound rejection. Crashes, timeouts,
malformed replies and unsupported views cannot count as matching rejections.

```sh
QLEISLI_DUAL_KERNEL=lean-kernel/.lake/build/bin/qleisli-kernel cargo test --test native_acceptance -- --include-ignored
cargo test --doc --locked --offline
cargo build --example native_acceptance --locked --offline
python3 scripts/test_native_acceptance_replay.py --record /tmp/qleisli-native-replay
python3 scripts/test_test_native_acceptance_replay.py
```

The replay record destination must be new. CI runs the four native integration
tests, builds the example and replays the retained inputs in its own record
directory. The harness tests ensure transport failures cannot mask disagreement.
[Source review](source-review.json) binds the first implementation and its new
public boundary. [Replay results](replay/results.json) retain all 799 outcomes:
263 accepted, 536 rejected, zero failures; one empty input rejected at the
proposal size boundary. Original input/decision files are unchanged. The report
binds the source and executable hashes before/after replay.

[Validation](validation.json) records successful ordinary Rust tests, four new
native integration tests, three retained dual tests, compile-fail/doc tests,
documentation generation, harness/coverage/CI tests, kernel source and compiled
policy tests, the full kernel proof/reduction replay, and rebuilt schema/model
audits. The native comparison manifest retains every prior command and adds the
new three-command group. The complete 68-group comparison run, platform bundle
builds and clean registry installation were not repeated for this initial slice;
they remain cutover/release requirements, not claimed results.

Remaining ordered work: native evidence DAG/contract/finite-leaf handles,
frontend and all public caller migration, exact checker compatibility and
platform distribution, removal of legacy acceptance, and full release checks.
Cargo builds/docs still need no Lean; default CLI/library behavior remains
transitional until those callers migrate. Existing proofs/audits stay in place.
No general theorem, native compiler/decoder/runtime preservation or release is
claimed by these tests. External schemas remain disabled.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
