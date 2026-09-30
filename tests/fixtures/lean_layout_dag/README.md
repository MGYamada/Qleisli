# Shared typed-call development record

This informed CD-3 implementation exercise belongs to Qleisli (Apache-2.0), not
the three-source external corpus. It is not a controlled model benchmark.
The [contract](../../../docs/lean-layout-dag-slice.md) was written before the
new acceptance path. The first source and desired artifact were saved before
their [baseline checks](baseline.json): Rust already accepted the ordinary
two-call source, while the preceding Lean executable rejected `--layout-dag`
as an unsupported command (exit 2).

## Retained attempts and repairs

- [First source](first_source/main.qli), [shared artifact](shared.qhd) and
  [independent identity request](identity.qhr) are unchanged from the baseline.
  The source required **zero revisions**.
- [First Lean attempt](LayoutDag-first.lean.txt) and [actual first diagnostics](first-lean-diagnostics.txt)
  retain a reserved constructor-alternative spelling and unused simp arguments.
  The repaired implementation quotes the `then` alternative. Subsequent proof
  elaboration required unfolding `Except.mapError` for both success and error.
- [Actual compiled-audit failure](first-audit-diagnostics.txt) identified the
  generated `denoteFrom._unsafe_rec` partial declaration. An intermediate
  explicit `List.rec` attempt failed compilation with “code generator does not
  support recursor `List.rec` yet”. Both graph evaluators now use the standard
  total `List.foldlM`; the compiled audit succeeds. The rule was not relaxed.
- [First reduction diagnostics](first-reduction-diagnostics.txt) exposed the
  ambiguity between the phase and layout `Definition` names; the test now uses
  `LayoutDag.Definition`. Elaboration-error placeholders in that failed run are
  diagnostics, not admitted final proofs.
- [First native diagnostics](first-native-diagnostics.txt) retain a test-driver
  mistake: an empty program was emitted with entry -1, causing syntax rejection
  before the intended capacity check. The test now explicitly supplies entry 0.

These are retained diagnostic checkpoints and repair descriptions, not a full
editing transcript or a measured total repair count. Source-body duplication
and manual source conversions are unchanged. No `.qli`-to-layout-DAG producer
exists yet. The removed checker burden is expanded shared layout bodies and
manual assurance about callee/adapter meaning. Generation time and whole-compiler
authoring cost were not measured.

## Independent semantic and scale checks

The [fresh-process suite](../../../scripts/test_lean_layout_dag.py) executes small
graphs owner by owner, without reading call/composition result claims. It checks
joint reference coefficients, noncommuting permutations, exact tuple shape,
zero-width owners, both call boundaries/inverses, stale receipts, graph and
resource limits. It has **9 tests / 147 process decisions**. The
[wrong callee](wrong_callee.qhd) is valid against its [actual meaning](callee_actual.qhr)
but fails the separately retained [intended contract](callee_expected.qhr).

[After observations](after.json) retain actual commands, outputs and source/binary
hashes. [Regression outputs](regressions.json) cover the previous phase/layout
profiles, Rust exact comparison and document/distribution helpers.

| Artifact | Stored definitions / references | Charged work | Expanded applications | Dense dimension |
| --- | --- | --- | --- | --- |
| `shared.qhd` | 3 / 3 | 6,927 | 6 | 0 |
| [Depth 64](depth64.qhd) | 64 / 126 | 13,568 | 9,223,372,036,854,775,808 | 0 |
| [16 axes plus Bits0 owner](sixteen_axes.qhd) | 2 / 1 | 27,046 | 3 | 0 |

Each call includes its two adapters in expanded application accounting.
These are static costs, not a promise of a measured wall-clock bound or an
execution benchmark. The 16-axis case is a layout call, not shared QPE/QFT.
The first source is accepted by both installed primary and MSRV Rust binaries;
both CI jobs replay it. That establishes compatibility, not source translation.

The [isolated package record](clean-build-record.json) uses a fresh copy without
`.lake` or external packages, clears Lean search/toolchain overrides, and records
build, reductions, compiled audit, fresh `Main` replay and all native typed-call
tests. It does not constitute clean Git release-distribution validation.
Remaining gates and performed checks are in the
[release checkpoint](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/releases/v0.2.0.md#shared-typed-layout-checkpoint-2026-09-29).
