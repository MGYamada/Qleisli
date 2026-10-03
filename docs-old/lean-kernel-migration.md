# Rust frontend and Lean verification kernel

Rust retains acceptance until S05. [VM22–29](../docs/verification-migration-v0.2.md) schedule implementation. Mathlib-free [kernel](../lean-kernel/README.md) and independent [mathematical bridges](../lean/README.md) remain separate. Rust handles parsing/diagnostics/transport/generation/simulation/search; Lean reconstructs artifacts against independent requests. Semantics import neither checker nor transport; [trust partition](../TRUSTBOUNDARY.md) fixed.

## Pipeline migration with a stable IR verification boundary

Each migrated pass needs actual-transform proof or independent translation validation, recording IR/direction/coverage/assumptions. Reverify boundaries, preserve phase/types/effects/entry/cleanup. Accepted IR or moving code proves no source correspondence; Python remains an oracle. Component results do not complete R14/H1–H5 or source/runtime binding.

## External search and the LeafRealizer checker

Untrusted norm-equation search proposes circuits/witnesses. Future LeafRealizer binds actual realization to independent operation/gate/domain/interface/error requests. Solved auxiliary equations prove no realization; exhaustion no impossibility. Reference-sensitive approximation needs composition bounds and never substitutes for exact cleanup. No current LeafRealizer API.

## Backend execution must match kernel definitions

By v1 implement substantive proved Lean transforms/realization/emission. Reject project axioms, unsafe/partial, extern/implemented_by, noncomputable/native_decide/holes, including private/unreachable/generated helpers. Source/import and compiled-origin audits check unsafe/partial/runtime-replacement metadata; axiom-only audits are insufficient. Audit metaprograms stay outside runtime closure. Future backend packages inherit gates.

## Staged migration

| Stage | Advancement gate |
| --- | --- |
| K0 | Reproduce seed/VM22 inventory; new M2 rules disabled until actual proofs/binding/H1–H5. |
| K1 | VM23/24 exact arithmetic/equations/reconstruction, complex interpretation, phase/trees/axes/binding and failure/work/capacity preservation; raw extraction needs K2. |
| K2 | VM25–29 every raw/hierarchy variant, actual proofs without Rust-checker substitutes; immutable input, either rejection/disagreement fails, native/adversarial/platform tests and coverage audit. |
| K3 | v0.5 all S05 proofs/review/reproduction/artifact binding/audited packaging/compatible migration; then authority transfer, no fallback. |
| K4 | v0.6–v1 actual source/backend lowering/optimization/realization/emission, CPTP dilation/synthesis, PR/RS and cost translations. Exact/approximate/device/runtime assumptions explicit; versioned removal of duplicate acceptance. |

Stages are gates, not deadlines/PATCH-break permissions. v0.3 types/v0.4 review remain.

## First executable slice

Phase256 proves actual cyclic normalization/acceptance with both phases and independent requests, not full IR/ownership/instrument/native/source adequacy or production receipts. The fixed protocol retains canonical ASCII, all byte/token/gate bounds, JSON/exit agreement and five-second fail-closed transport.
<a id="experimental-wire-contract"></a>

## Audit and remaining trust

[CI lanes](../.github/ci/README.md) retain native build/source+compiled audit/tests; changed proofs compile; release/manual-full/policy risks replay proofs/schema binding. Only propext/Classical.choice/Quot.sound transitive axioms permitted. Compiler/runtime/standard primitives/OS/adapter correspondence remain assumptions, not finite-test theorems.

VM25/26 original-complex/reference/cleanup/CP/TNI/TP and VM27 graph/root/leaf/pair/H proofs have scoped evidence in the VM plan. VM27 native work shares 10M exact operations; compatibility handles have a separate equal budget. Analytic reader→Operator, universal decoder/compiler, schema/source/runtime binding and production transfer remain open; VM27/S05 incomplete.
