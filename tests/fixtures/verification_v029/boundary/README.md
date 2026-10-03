# Compatible VM29 boundary validation

This local macOS record covers the compatible migration selected on 2026-10-03.
Default Rust acceptance and public legacy leaf-handle APIs remain; selected
native hierarchy execution no longer invokes the old finite-leaf acceptance
path. Source/backend preservation, full EffectSound/CPTP, analytic Operator
closure, native compiler/decoder correctness and S05 transfer are not claimed.

The [validation record](validation.json) binds commands, outcomes, source hashes
and binaries. Compressed logs preserve full transcripts. The source/API review
is in [source-review.json](source-review.json). Earlier v0.2.9 maintenance records
remain unchanged and are not presented as validation of these later changes.

Performed checks include:

- Rust all targets: 582 passed; 38 opt-in tests excluded from that ordinary run.
  Relevant opt-in raw, hierarchy, sized and named-QPE suites run separately.
- Clippy with warnings denied, Rust documentation tests, documentation/source
  inventories, CI routing and schema/source registry checks.
- Ordinary selected CLI: 240 process checks over 84 existing small corpus cases.
- Native/compatibility hierarchy execution: 19 cases, 912 complex coefficients,
  768 seeded outcomes; source initialization binding and QPE transport faults.
- Foreign/Python selection: 10 tests and 230 recorded subprocess calls, including
  actual PyQIR text and bitcode; no optional-reader skip in this recorded run.
- Library-only, unused-body, concrete generic-instance and qrate regressions.
- Mathlib-free and Mathlib proof builds/compiled audits; fresh kernel replay,
  retained reduction/equivalence tests and compiled escape-hatch rejections.

Initial validation caught the stale help snapshot and a test expecting generic
calls to lower to direct gates. The test now targets the actual retained-call
shape, and the help fixture is versioned under VM29. A direct invocation of the
hierarchy Rust suite omitted its generated independent-oracle directory; the
proper Python harness subsequently generated the small oracles and passed.
Disk pressure required clearing regenerable Cargo build caches before the final
Rust rebuild. These initial failures are retained in the validation record.

No maximum-size algorithm case was generated or checked. Hosted Linux/macOS CI,
an MSRV rerun, package publication, tagging and the remaining unrelated opt-in
comparison groups were not run locally for this change. CI now includes the
new source/foreign routes and optional QIR against the audited relocated bundle.

Primary agent: Rust transport/public-path integration and independent examples.
Verification agents: native hierarchy parity/semantic oracles, foreign/Python
fault tests, and Lean definition/theorem review. Julia is not used in this Rust
repository; exact existing finite oracles supply the opposite computational
checks. Certificates/schemas enabled: none. Formal addition: independent
classical ScopeSafe and global SSA uniqueness composed with packet acceptance.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
