# CI scheduling and evidence

`profiles.json` selects docs-only versus executable validation conservatively.
Executable, proof, normative and unknown changes still run every selected suite.
`ci_profiles.py` separately selects proof maintenance without treating tests as
proof evidence. Required contexts aggregate all selected suites against the
exact checkout; missing/unknown lanes and failed/skipped selected jobs reject.
Dependency archive misses take the same validation path. Cargo `target`, Lean
project outputs and prior validation reports are never cached.

## Progressive test-oriented CI (#223)

| Lane | Selection | Work |
| --- | --- | --- |
| `tests` | Ordinary known implementation/test changes; explicit manual tests | Native kernel build, source/compiled policy and Audit, all native positive/negative/differential comparisons; registry source identity and policy tests. |
| `model` | Changed mathematical proofs or normative contracts | Tests plus Mathlib package build and compiled declaration audit. |
| `full` | Tags, release branches, default manual runs, policy/toolchain/registry changes, missing diff or unknown inputs | Tests plus both packages' proofs, retained reductions/equivalence, fresh kernel/Main replay and rebuilt schema-type binding. |

The native kernel's existing proofs necessarily typecheck in its ordinary
build. Their statements are retained; no theorem is downgraded to a test claim.
The deliberate first step is to remove whole-project Mathlib/reduction/fresh
replay from routine implementation CI, not to delete proofs or complete every
future harness migration. No authority, public acceptance or schema gate moves.
Tests and full validation operate on the same source/toolchain binding. A
registry update changing only `source_revision` uses the exact current-source
identity check without forcing full replay; exported types, domains, enablement
or other registry fields changing (or unavailable/invalid previous data) force
`full`. Both sides are parsed with duplicate-field rejection. This prevents
routine kernel source edits from accidentally selecting full via their required
source-hash refresh.

`validation=tests` is explicitly weaker than release proof validation. Only
`validation=full` (or the forced full tag/release route) satisfies the full
release lane. Rollback is to select `full` in `ci_profiles.py` for all executable
changes; the retained full commands require no reconstruction.

## Native comparisons (#206)

`native-comparisons.json` retains all 65 comparison groups (66 commands) from
the v0.2.6 workflow, including small independent complex/rational/source oracles
and existing capacity cases. No new maximum-size corpus benchmark is added.
The inventory regression pins the original command/environment coverage; only
the four explicit record destinations change to isolated task directories.
Direct native VM-27 request, lossless decoder and named-QPE host-fault
regressions are added (69 commands total). Full hierarchy execution also compares native-only
decisions and named-QPE residual/reference coefficients against independent
small-system oracles. These tests do not claim a universal parser/compiler proof.

The kernel job first builds from source, runs source/compiled declaration
policies, axiom/runtime-replacement audits and compiled negative tests.
The `full` lane additionally runs reduction/equivalence tests and fresh
`leanchecker` replay of both roots. Then
`run_native_ci.py` schedule every independent comparison with at most four
workers in the same checkout. Native harnesses remain freshly compiled in
their own temporary projects. No verification result is transferred across
jobs or reused to skip checks. Each group has a separate log/record directory,
and any missing, duplicate, failed or timed-out group fails the job. Source,
actual toolchain and command inventory identities accompany the timings.

In the `full` lane, the unchanged `check_schema_registry.py` still builds and
audits both Lean packages, replays the kernel and binds exported schema types to
exact sources. Its `--source-only` check in routine CI is explicitly not proof
or compiled correspondence. Neither Rust authority nor external-schema gates change.

Manual full runs expose `native_workers=1` for an independently fresh serial
comparison, or `2`/`4` for bounded parallel execution. `cache=disabled` bypasses
Cargo dependency archives, not verification. Lean Action's pinned Mathlib
dependency cache is separate; project build caching remains disabled. Compare
job/step times and total runner wall seconds, reporting queue separately and
distinguishing observed archive hits/misses/disabled states. A single run is
observational evidence, not a statistical benchmark.

Successful comparison artifacts retain all task IDs, commands, exit codes,
timings and logs. They are diagnostic records, never an acceptance shortcut.
Release/manual-full validation still checks its exact final source independently.
