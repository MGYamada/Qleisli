# CI scheduling and evidence

`profiles.json` selects validation conservatively. Executable, proof, normative
and unknown changes run every suite; tags, release branches and manual runs are
always full. Required contexts aggregate all selected suites against the exact
checkout. Dependency archive misses take the normal validation path. Cargo
`target`, Lean project outputs and prior validation reports are never cached.

## Native comparisons (#206)

`native-comparisons.json` retains all 65 comparison groups (66 commands) from
the v0.2.6 workflow, including small independent complex/rational/source oracles
and existing capacity cases. No new maximum-size corpus benchmark is added.
The inventory regression pins the original command/environment coverage; only
the four explicit record destinations change to isolated task directories.

The kernel job first builds from source, runs source/compiled declaration
policies, axiom/runtime-replacement audits, reduction/equivalence tests, fresh
`leanchecker` replay of both roots and compiled negative tests. Only then does
`run_native_ci.py` schedule every independent comparison with at most four
workers in the same checkout. Native harnesses remain freshly compiled in
their own temporary projects. No verification result is transferred across
jobs or reused to skip checks. Each group has a separate log/record directory,
and any missing, duplicate, failed or timed-out group fails the job. Source,
actual toolchain and command inventory identities accompany the timings.

The model job's unchanged `check_schema_registry.py` still builds and audits
both Lean packages, replays the kernel and binds exported schema types to exact
sources. Only the redundant outer model build/audit is removed. Cross-job
duplication is retained; neither Rust authority nor external-schema gates change.

Manual full runs expose `native_workers=1` for an independently fresh serial
comparison, or `2`/`4` for bounded parallel execution. `cache=disabled` bypasses
Cargo dependency archives, not verification. Lean Action's pinned Mathlib
dependency cache is separate; project build caching remains disabled. Compare
job/step times and total runner wall seconds, reporting queue separately and
distinguishing observed archive hits/misses/disabled states. A single run is
observational evidence, not a statistical benchmark.

Successful comparison artifacts retain all task IDs, commands, exit codes,
timings and logs. They are diagnostic records, never an acceptance shortcut.
Release/manual validation still checks its exact final source independently.
