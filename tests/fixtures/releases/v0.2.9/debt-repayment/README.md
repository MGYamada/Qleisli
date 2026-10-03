# Maintenance validation: reports, docs, native builds and migration coverage

[Results](validation.json) record the completed local checks:

- 163 tooling regression tests across 18 test/check commands.
- 87 corpus cases, 15,889 semantic probes, 63 detected semantic faults and four
  source rejections, with no upstream framework execution.
- All 66 native comparison groups / 72 manifest commands in one successful run.
- A fresh copied kernel build, compiled/axiom audit, retained proof/equivalence
  tests, fresh replay of both roots and compiled policy counterexamples.
- Full rebuilt schema type/audit validation; no external schema enabled.

[Tooling](tooling-validation.json), [corpus](corpus-validation.json),
[native results](native-results.json) and [schema validation](schema-validation.json)
retain their separate scopes. The [native build binding](native-build.json) and
[copied source identities](native-source-map.json) record the compiled dependency
and exact validation snapshot. The snapshot commits are local validation records,
not release commits or tags. No Lean definition changed between audit and rerun.

Two initial local attempts failed six commands before their tests started:
Homebrew Cargo cannot interpret Rustup's `+1.98.1` proxy argument. The runner now
checks actual tool versions and normalizes only that identical pinned selector;
other selectors reject. It records and verifies both requested and executed
commands. The final complete run passed. [Phase results](native-phases.json)
retain the failed attempts rather than presenting them as successful validation.
[Storage identities](log-storage.json) bind every retained raw log/record to its
lossless gzip file, including the initial failures.

The [source-binding review](source-binding-review.json) updates four frozen
comparison-harness hashes after reviewing their build-only changes. Request
construction, independent oracles and comparison checks are retained. The new
shared builder compiles fresh test drivers against one current native library;
it never reuses test decisions. Source, compiled-module, archive or toolchain
drift fails the run.

The [VM29 audit](../../../verification_v029/README.md) accounts for public paths
and legacy-removal conditions. S05-C1–C5 remain open; this maintenance does not
transfer Rust authority or prove source/native/runtime correspondence. Hosted
CI, Linux validation, publication and new maximum-size corpus experiments were
not performed. Full ordinary Rust/MSRV tests were not rerun for this follow-up,
which changes tooling/documentation rather than Rust implementation bodies.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
