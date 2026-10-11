# Semantic namespace migration

Issue #317 reclassifies ordinary bundled source by mathematical meaning.
These six finite corpus projects import `std::transform` instead of
`std::transforms`. The two affected preparation clients import `hadamard2`
from `std::transform`; the Grover client imports `reflect_uniform2` from
`std::reflection`.

`migration.json` follows the complete ordinary-type migration. Its twelve
entries preserve both source files for each affected project, with exact
predecessor and derivative hashes. Only the six kernels' import paths change;
all six `main.qli` files remain byte-identical. The original shipped source,
authoring attempts, earlier migration snapshots, pinned upstream files,
licenses, copyright and modification notices remain unchanged. The manifest's
original case records and limitations remain historical descriptions.

The Qualtran reflection keeps `I - 2|s><s|`, the negative of the bundled
`std::reflection::reflect_uniform2` contract `2|s><s| - I`. Its predicate and
protected-body source are unchanged. The retained fixed `qft2` and `qft3`
calls keep their original tuple trees, little-endian axes, positive Fourier
phase and output reversal. This migration adds no generic QFT implementation
or fixed/generic equivalence requirement.

The derivative sources live under `sources/<project>/`. Active validation
must explicitly select the latest migration snapshot instead of executing
the unchanged original case directory. A migration hash alone does not select
an execution path or establish source preservation.

**Validation status: six actual CLI/native checks passed.**
The [checks](checks.json) bind the real commands, outputs and source identities.
The explicit `source_selection = snapshot` metadata selects these complete
projects for maintained validation, with predecessor and derivative identity
checks. Original sources and earlier observations remain unchanged.

The integration evidence at
`tests/fixtures/frontend_v030/stdlib-semantic-namespaces/implementation-01/`
records six successful tiny-case semantic comparisons (340 probes, 2–4 qubits).
The first aggregate oracle run nevertheless failed on an outdated negative
diagnostic expectation. After the independently reviewed metadata correction,
all four unchanged negative sources were checked again and passed their rejection
expectations. The failed aggregate capture remains intact; no complete oracle
rerun is claimed. A later embedded-source comment correction was rebuilt and
checked with four unchanged first clients. The separate records identify the
binary and source state used at each stage.

Final inventory checking required the original negative manifest to remain
byte-identical. `negative/current-manifest.json` now carries the current
diagnostic expectations, explicitly selected and hashed by `manifest.json`;
all four final rejection checks passed through that selection. Current Rust
corpus/roundtrip and Python native clients likewise select the six complete
namespace snapshots instead of executing their frozen original directories.

No maximum-size case was generated or checked. Native checking and bounded
semantic regressions remain distinct from a preservation proof, constitutional
guarantee admission and release approval.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
