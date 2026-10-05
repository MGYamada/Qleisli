# Planned bounded validation driver

**Status: prepared for root review; no command has run through this driver.**
Run only after the final code barrier. Keep root's 40-observation after replay
between the latest run and the MSRV run; never rebuild the shared CLI during
that replay. This directory owns only new validation records, not production,
active inventory/coverage metadata, Reference, Issues or Git state.

Exact invocations from the repository root:

```sh
python3 tests/fixtures/frontend_v030/common-pattern-design/validation/driver.py latest attempt-01
python3 tests/fixtures/frontend_v030/common-pattern-design/validation/driver.py msrv attempt-01
```

Root executes them separately. The latest uses explicit Homebrew Cargo/rustc
1.98.1. MSRV uses `/opt/homebrew/bin/rustup run 1.85.0 cargo` and `rustc`; it does
not pass `+1.85.0` to Homebrew Cargo. The driver checks actual versions before
building, uses only `/private/tmp/qleisli-bounded-validation-target`, jobs 2,
incremental 0 and dev/test debug 0, and selects the existing native binary
whose SHA-256 is `39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85`.
It invokes no Lean build/replay and raises no checking limit.

[Selection](selection.json) records the inspected existing tests and the bounded
exclusions. Eleven genuine integration suites cover finite/sized exact Unit
and tuple patterns, runtime argument trees, zero-width ownership, effects,
lexical identities, complete unused declarations, source collection and
selected public CLI/native paths. Four existing shared-type library tests
exercise type-tree distinctions, zero-width linearity and size-error order.
The driver also checks formatting, all-target compilation and all-target
Clippy with denied warnings, then builds the CLI for the separate root replay.
It never executes argument lists read from stored metadata.

The two excluded project tests are
`long_acyclic_import_chain_loads_on_a_small_stack` and
`deep_import_cycle_reports_the_back_edge_and_cycle_path`: each creates 3,000
files to stress import traversal, which this pattern factor does not change.
The three existing sized native tests remain ignored; no `--ignored` is used.
The unrelated 4,000-source ownership differential is outside this bounded run.
These exclusions do not satisfy, remove or weaken their independent CI/release
criteria. No maximum-qubit corpus case is newly generated.

Each actual run creates a unique mode/attempt directory and captures current
inputs only after code has frozen. It preserves raw stdout/stderr, actual exits,
version/postcondition failures, launch failures (no fabricated child exit),
timeouts, real test-result counts and before/after identities. Source changes or
native changes stop the run. A retry needs a new attempt directory; original
failures and their logs are never overwritten. The advisory target lock covers
these drivers only; root remains responsible for excluding other Cargo builds
and keeping the CLI fixed during its replay.

The source/fixture map is explicitly incomplete: it includes all production
Rust, the selected test sources/common helper, declared source-fixture trees,
stdlib, kernel source/identity, Cargo and constitutional records. All-target
checks also compile test inputs beyond that declared fixture map; this is not
a complete build-input closure, artifact attestation or Git-commit binding.
Passing Rust checks and native-valid output remain distinct from source
preservation, QS/PR/RS/EXACT discharge and full CI/release approval. The two
ordinary QLV1 guarantees retain their original scopes/premises.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
