# 0.2.4 review follow-up

[Issue 160](https://github.com/MGYamada/Qleisli/issues/160) tracks the compatible
repairs requested on 2026-10-01. Published 0.2.4 artifacts are immutable; these
are unreleased fixes. The submitted review's fuzzing/sampling totals are external
observations, not locally rerun results. This packet records curated regressions,
not a controlled authoring study or model benchmark.

| Finding | Repair and checking experiment |
| --- | --- |
| S/S†/T† emit repeated T gates | Fold adjacent exact diagonal words at the terminal target. Preserve scalar phase and controls; do not commute across another action. Emission uses S/S†/T† without changing public IR. |
| Negative controls and controlled phases block QFT export | X conjugation, exact controlled-H/phase decompositions and explicitly uncomputed conjunction workspace. QFT2 uses two physical qubits; QFT3 uses four, including one clean synthesis qubit. Workspace counts toward the existing twelve-qubit target limit. |
| QFT's final axis permutation is rejected | Track equal-width bit-axis permutations as ordered wires. Arbitrary LiftBasis permutations/injections remain unsupported. |
| Unrelated source-tree contents break qrate checking | Opt-in `--qrate` selects explicit `[source].root`; old default loading remains unchanged. Escape/target/linked source paths reject. All files within the selected source root are still checked. This is not full qargo dependency management or reachable-module loading. |
| Unknown manifest metadata is silent | Ordinary source CLI commands report `project` warnings for unused keys in text/JSON. Validity and successful exits remain unchanged. |
| Wrong module import gives no repair | Suggest actual public declarations, including `std::transforms::qft2`; private declarations are excluded. |
| Nested register pattern hides actual type | Report the actual immediate type/arity and the additional split needed. |
| Misused cnot tuple points only at later use | Point to the tuple binding, name its type, retain the use location in the message and suggest destructuring. Correct named tuple results remain legal. |
| Current corpus counts become stale constants | Generate the README inventory from manifests; validate actual projects, provenance and authoring coverage rather than a fixed per-source census. Historical snapshots keep their original identities. |
| User compositions need a check before QLT | Document the existing finite `apply_contract(provider, expected, q)` form and test H∘H against identity, plus a phase-sensitive invalid provider. Whole-instrument/source-preservation obligations remain distinct. |

The [Rust regressions](../../review_v024.rs) check rejection and successful
repairs. The [independent target oracle](../../../scripts/test_review_v024.py)
decodes emitted gates without using Qleisli arithmetic/import/simulation and
compares every complex column, exact phase, output axes and zero-return workspace
for small QFT/control cases. The
[external format gate](../../../scripts/test_interop_external.py) additionally
uses the reference OpenQASM parser and LLVM verifier. These numerical checks do
not establish a transformation theorem or a Resource Safety certificate.

The installed [Python connection tests](../../../scripts/test_connections.py)
compare ordered outcomes within the numerical tolerance and validate each
circuit's own work totals. Exact phase folding changes floating evaluation order
and reduces the emitted work; source and target counters must not be equated.
The initial CI failure and its repair are recorded in the validation file.

Breaking/future obligations are recorded with concrete experiments in their
existing Issues: [borrowing 29](https://github.com/MGYamada/Qleisli/issues/29),
[prelude 58](https://github.com/MGYamada/Qleisli/issues/58),
[source expectations 46](https://github.com/MGYamada/Qleisli/issues/46),
[pipeline/generic rules 131](https://github.com/MGYamada/Qleisli/issues/131),
[realizability/workspace 120](https://github.com/MGYamada/Qleisli/issues/120),
[exact/approximate domain 123](https://github.com/MGYamada/Qleisli/issues/123) and
[LiftBasis synthesis 132](https://github.com/MGYamada/Qleisli/issues/132).
[Issue 165](https://github.com/MGYamada/Qleisli/issues/165) tracks phase-aware IR
and target-dependent non-Clifford costs at 0.3.0. A LiftBasis checker alone does
not prove Giles–Selinger's general exact-unitary synthesis theorem. Raw T-word
counts are literal IR costs, not optimal physical T counts.

Do not move or delete required source/provenance/counterexample evidence to
implement the review's suggestion about external logs. Current inventory views
and frozen validation records have different roles; archived reports are not
acceptance rules. [Validation](validation.json) records performed and skipped
checks, with source identities, without duplicating command logs.
