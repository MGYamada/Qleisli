# Repository QLI inspection

2026-10-03, selected development version v0.2.9. This is an inspection of the
existing sources during the migration adopted in
[Issue 276](https://github.com/MGYamada/Qleisli/issues/276).
No `.qli` source was modified. No unexpected source regression was found in
the checked scope; the new accepted-handle path still has the limits below.

[Results](results.json) retain the source/parser classifications, diagnostic
messages, all project comparisons, semantic probe counts, native handle results,
test suites, executable hashes and skipped scope.
[Source hashes](sources.sha256) bind all 1,041 files: 764 corpus, 232 test,
41 example and 4 bundled-library sources. These hashes matched again after
inspection. Every source had an enclosing schema-2, edition-2026 manifest.

The ordinary parser accepts 959 files and rejects 82. The rejections consist
of 52 historical authoring snapshots, 26 sized-dialect files and four deliberate
syntax counterexamples. There are 505 frozen authoring files in total; they
are historical evidence, not a set of currently runnable examples.
All 25 positive sized sources pass their own generic frontend with their
imports, in coherent/measured module maps. The remaining sized source is the
retained `unguarded_take` counterexample: its unconstrained size permits zero,
so generic checking correctly rejects the index with diagnostic `size`.

All 14 example projects, 84 finite corpus projects of at most four qubits,
62 type-correct semantic faults and four source rejection cases have matching
results through ordinary `check` and `check --lean-kernel=...`: 164 project
comparisons, no unexpected outcome or diagnostic difference. Both source paths
still use the transitional frontend; this is not a claim of legacy removal.
The independent corpus oracle passes 3,253 phase/probability probes, detects
all 62 selected semantic faults and confirms all four negative diagnostics.
The finite oracle run uses sampled interference rows, not every matrix entry.
[Small sized results](sized-small.json) additionally retain six positive widths,
four detected semantic faults, 16 source rejections and two IR rejections.

The 14 example artifacts also pass Lean-selected emission. The new native
`AcceptedProgram` accepts ten. Four remain explicitly `unsupported` because
they retain multiple programs, function evidence and source tables:

- `examples/function_contracts`
- `examples/iterative_phase_estimation`
- `examples/operation_algorithms`
- `examples/operation_contracts`

These are valid existing source clients and concrete targets for the next
evidence-DAG migration step, tracked by
[Issue 277](https://github.com/MGYamada/Qleisli/issues/277) for v0.2.9.
Do not weaken their contracts, flatten away their
evidence or add a legacy fallback to make this inspection pass.

The directly attempted `check stdlib --qrate` reproduces the documented
reserved `basis` module failure tracked by
[Issue 96](https://github.com/MGYamada/Qleisli/issues/96).
The supported embedded-library route passes with the example checks and library
regressions. This observation does not justify renaming `std::basis`.

The selected Rust suites pass 245 tests; eight optional tests are ignored.
Three source/native integration tests, provenance/snapshot checks and document
checks also pass. The results record contains the exact suite list and temporary
parser probe sources. The first sized probe's mistaken expected diagnostic was
corrected to the existing regression's `size` code; repository sources did not
change. No proof completion or source-preservation theorem is claimed.

Execution skips the five-qubit finite cases `phase_lock`, `equals2`,
`less_than2`, their excluded `low_bit_equality_only` fault, and maximum-sized
generic instantiations. Their files are included in syntax/hash/provenance
inspection. Historical command logs are not replayed, and standalone fixtures
are checked through their test contexts where selected, not treated as one
combined project. Full native CI, platform installation and release checks
were not rerun for this source inspection.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
