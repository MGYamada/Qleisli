# Distribution CI follow-up

The initial full candidate run
[37137322408](https://github.com/MGYamada/Qleisli/actions/runs/37137322408)
tested commit `47f86c7087f794f9ea5c6a2832ddfccf6194859c` and failed.
The compressed `ci-*.log.gz` files preserve its original diagnostics; `files.json`
records the decompressed hashes. The initial macOS source/distribution and
Mathlib proof jobs passed, but this did not make the full candidate releasable.

Corrections preserve Lean's decisions: QIRF envelope errors regain diagnostic
pointers only after native rejection; sampling and contract golden expectations
follow the adopted counters/categories; finite-leaf work tests account for
native reconstruction. The named-QPE mock delegates finite-leaf invocations to
the real checker, so altered QPE obligations remain the tested failure. Nested
`{record}/...` paths now expand inside each CI task's output directory rather
than create an untracked directory in the checkout. Frozen whitespace logs
retain their original bytes under the existing targeted attribute policy.

The component comparison records explicitly retain three public-boundary
differences: empty source labels, depth-32 graphs and 524288 expanded steps.
The component accepts those inputs; the production QIRF envelope/graph/work
bounds reject them. The fixtures still test both results, and do not claim
component/public acceptance equivalence. The retained 799-pair replay remains
263 accepted, 536 rejected, zero decision mismatches.

Local follow-up evidence includes 43 targeted Rust tests, 12 installed Python
connection tests, 14 CI-runner tests, installation with an empty helper-tool
PATH, Clippy, QPE host/transport checks, shared-gradient QFT, 146 raw component
cases and 51 branch component cases. Component matrices stay at two or three
qubits; no new maximum-size corpus or deferred stress suite was introduced.
These targeted results require a subsequent full CI run on the corrected
commit before publication. The earlier bundle and public-path records remain
historical snapshots; neither this correction nor packaging completes Soundness.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
