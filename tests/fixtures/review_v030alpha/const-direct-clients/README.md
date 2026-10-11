# Direct client parameter-header migration

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

Issue [#33](https://github.com/MGYamada/Qleisli/issues/33), following
`7e0d594346583ed37d2b1d5a7c2bbece1855e92d`.

The CLI differential source generator now writes `const U: Op<Bit>`.
The seed, 96 cases, generation order, maximum four live qubits, analytic oracle
and fresh public CLI calls remain unchanged. `first-before.qli` preserves the
first old generated source; `first-desired.qli` is its sole marker change.
The complete earlier generator is retained in the stated Git baseline.

Before and after generators produced exactly the same 96 oracle objects and
source bodies after the single header-marker substitution. All 96 public runs
passed for each variant on latest and MSRV: 384 CLI invocations, no acceptance
cache. The maximum probability error remained exactly
`4.218847493575595e-15` in all four runs. Three independent analytic calibrations
also passed. These are numerical regression comparisons, not general source
preservation, full soundness or constitutional discharges.

Ten direct permission fixtures now use the existing hash-bound selector and
complete current copies. Originals and their authoring-session records remain
unchanged. All five permission tests passed before and after on each toolchain;
Apply, Adjoint, Controlled, unused-provider requirements, source locations and
the explicit unsupported finite barrier retain their original checks. Their
selected-source and finite adapters remain separately exercised.

`validation.json` records outcomes, binary identities, generated source digests
and elapsed times. CLI durations were 110.72/115.12 seconds on latest and
117.13/121.11 seconds on MSRV (before/after). Other local validations ran during
these observations; they are not a controlled benchmark. Permission-test time
increased from 0.01 to 0.23/0.24 seconds because the existing selector now checks
ten fixture hash chains in child Python processes. Production Rust/Lean code
did not change. Both all-target Clippy checks, fmt, 55 fixture-selection tests
and all five shared source-integrity checks passed. Full CI and the unchanged
4,000-case ownership suite are not claimed by this unit.
