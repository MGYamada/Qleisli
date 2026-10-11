# Positive accepted-evidence supplement (#288)

This packet appends eleven small accepted artifacts to the retained v0.2.9
comparison evidence. It does not alter or rebaseline the original 799
artifact/request pairs. Those pairs still contain zero accepted artifacts with
function evidence and no QIRF2 `meaning` entries; replaying them alone cannot
establish positive coverage of these paths.

`tests/native_roundtrip.rs` supplies four explicit circuit-evidence cases:

| Case | Retained paths | Independent root matrix |
| --- | --- | --- |
| `nested-shared-dag` | Two distinct parents share a T receipt, in the implementation of one and specification of the other | diag(1, -1) |
| `certified-use-and-logical` | The same T receipt occurs in both actual use steps and specified logical steps | diag(1, zeta_8) |
| `branch-true` | Both arms remain present: nested ApplyUnitary evidence and CertifiedCompute evidence | diag(1, i) |
| `branch-false` | The same two arms, with the other classical choice selected | diag(1, zeta_8) |

Every case starts from a raw proposal, obtains a fresh native acceptance, and
requires byte-identical re-encoding of the decoded execution view. The test
counts actual receipt edges in both branch arms and both retained snapshots,
requires each named path to be nonempty, and compares every reachable receipt's
implementation matrix with its cached meaning. Separate explicit 2x2 matrices
check the T/S receipts and complete selected root, including cleanup. The four
cases contain eight distinct receipts in total, counted separately per artifact.
Only one data qubit and, for CertifiedCompute, one ancillary qubit are used.

The seven existing QIRF2 meaning cases cover T, S, Z, two X implementations,
low-control CNOT and CZ. Each requires a real `meaning` entry and a successful
native decision. Re-export with the same independently supplied table must
restore the original artifact bytes. Plain re-export intentionally produces a
circuit entry: the execution view alone does not retain the meaning-table tag.
The existing wrong-phase and wrong-control-axis cases remain rejection tests.

`record.py` runs the complete four-test Rust target, requires all eleven named
positive cases, preserves the exact emitted proposals, and independently
replays each one directly through the native process. It refuses an existing
record directory and checks source/binary stability and both frozen baseline
hashes. Source discovery includes the actual `.qli` and `Qargo.toml` inputs
under examples, corpus and stdlib, and is repeated after the run to detect
newly added or removed files. Run it with a new directory:

```sh
python3 tests/fixtures/review_v030alpha/roundtrip-coverage/record.py \
  --output /private/tmp/qleisli-roundtrip-new
```

The final `isolated-complete/` record uses the immutable commit identified by
`isolated-source-complete.json`, plus only the new test and recorder files. The source
archive and the two additions have explicit identities. This separates the
reviewed fix from the concurrent frontend migration; it does not claim a
successful build of that later working tree. `results.json` records the actual
source hashes, process results, toolchains and artifact hashes.
The ordinary `cargo test --all-targets` run includes the target; the dedicated
native acceptance CI task also requires it, alongside the unchanged 799 replay.
`checks-complete.json` records the final observations. The earlier `isolated/`
record remains intact: independent review found that its recorder's stability
check did not enumerate frontend input files, although the source archive
already contained them. The final recorder closes that gap and binds 1,128
source/input files. Both runs passed all four tests and all eleven native
replays; the final Rust run took 60.20 seconds.

The `current-integration/` record additionally passed against the common-parser
working tree before the proof-only schema registry refresh. Its source manifest
retains that earlier registry identity. `current-schema-integration/` repeats
the four-test target and eleven direct native replays after the refresh, binding
the integrated sources; neither local record alone establishes hosted full CI.

The first local run (`observed/`) passed all four Rust tests in 58.30 seconds;
its recorder initially failed to account for libtest's progress prefix on the
first output line. The recorder was fixed. A second attempt (`validated/`)
encountered the concurrently changing frontend AST and failed during compilation
before running any tests. Both original stdout/stderr streams are retained;
neither attempt is presented as a completed validation record.

These are bounded correspondence and coefficient tests. They do not prove
universal verifier equivalence, source preservation, compiler/runtime
correctness, or any new constitutional guarantee. No maximum-size case was
newly generated, and no frozen comparison evidence was rewritten.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
