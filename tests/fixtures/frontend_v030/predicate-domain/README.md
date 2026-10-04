# Explicit predicate-domain migration (#25)

This record implements the [posted contract](contract.md): both `with_computed`
forms require one explicit parameter of the register's exact basis type and a
`Bit` result. Ordinary basis calls keep their argument-list arity. Predicates
may be noninjective; coherent basis lifting keeps its separate injectivity rule.
No native acceptance rule, schema, quantum capacity or guarantee is changed.

## First sources and observed migration

[initial-study](initial-study/session.json) preserves all 109 files from the
26-case study before implementation. [Preservation hashes](first-study-preservation.json)
bind the original bytes, diagnostics and observer commands. Its observer was
built during the preceding multi-declaration unit; the session records the
then-current source identities rather than claiming a clean commit checkout.
Cases distinguish flat, left-nested and right-nested three-input domains,
nullary versus explicit `Unit`, both computed forms, Meaning and ordinary calls.

[Current observations](validation/study-comparison.json) rerun the same source
bytes: 10 accept and 16 reject, versus the initial 14/12. The eight legacy
predicate uses now report `arity`, including four previously accepted cases.
Unary matching trees, Meaning and ordinary-call outcomes are retained. Unary
mismatched trees still reject; the restricted-form message now says **exact
source basis type**, consistently with the certified form. The source observer's
exit code zero includes diagnostic rejections and is not native acceptance.

## Explicit active and historical translations

[Migration plan](migration-plan.json) binds the original and current identities
of 11 active files (15 predicates): stdlib, examples, six corpus algorithms and
the intentionally incorrect majority/parity semantic fault. [active-before](active-before)
preserves their earlier bytes. Bodies, pinned upstream references and notices
are unchanged. The VQE `flip` and `swap_excitation` functions remain ordinary
multi-argument basis calls; only `occupied` becomes a unary predicate.
[The pre-migration inventory](active-inventory-before.json) separates active
sources, negative cases and authoring history.

[Current translations](current-translations.json) explicitly maps two retained
QLI authoring positives, the phase-mismatch negative and the historical Grover
attempt to [current source copies](current). The original files retain their
paths and bytes. Each Rust harness checks the original's new `arity` failure,
then executes or rejects the separately named current translation for its
original semantic reason. No input is silently repaired or omitted.

The [recorded derivative comparison](validation/summary.json) uses the preserved
`fae0` baseline CLI and the current CLI. Three positive projects have identical
complete run distributions and identical **non-source** proposal fields:
programs, evidence, exact interfaces and source references. Embedded local and
stdlib source texts change exactly as recorded by their before/after hashes;
full artifact byte identity is intentionally not claimed. The current
phase-mismatch example still fails its independent contract check. Commands,
original full proposals, stdout and stderr are retained in [validation](validation/commands.json).
The independent `predicate-domain-independent` fixture separately compares
small full complex actions, reference correlations, axis order and Unit phase
against independent expectations and the immediate pre-migration baseline.

[Historical preservation](historical-preservation.json) compares 716 retained
files with the recorded Git base, including authoring sessions, corpus authoring
history and the fixed 799 artifact/request archive. All are byte-identical. The
archive SHA-256 remains
`296c36efa109762fefe9386c9a5b53ac010f8aa94e7464f595c0bf3173f3fae1`.
This is a byte-preservation check, not a fresh replay of all 799 native outcomes.

## Executed validation and limits

[Initial existing-test summary](validation/initial-focused-test-summary.json)
accurately retains the first run's failure: generated zero/dual-Unit predicates
in `source_ir_correspondence` still used the removed convention. The test was
migrated to explicit Unit trees, retaining its phase assertions, and the failed
test then passed. Other five tests in that target passed in the first run.
Together with the [six additional targets](validation/remaining-focused-tests.stdout.txt),
147 distinct existing tests passed across 14 targets. The later six-target
command has directly captured streams; the earlier terminal run is explicitly
labelled as a post-execution summary rather than a saved raw stream.

The first derivative comparison also made an overly broad full-artifact equality
assertion. [Its recorded correction](validation/initial-artifact-comparison.json)
retains the original driver and proposal bytes, then compares non-source fields
and precisely identified source-text changes. No production repair resulted.

[Final source identities](final-source-identity.json) cover the three production
files, nine existing test files and eleven migrated active sources. The shared
helper replaces both implicit domain folds; table generation, low-axis-first
leaf packing, cleanup checking, ownership and native evidence stay in their
existing paths. `cargo check --offline --lib` and `git diff --check` passed.
Independent tests, latest/MSRV Clippy and their exact commands are recorded by
the parallel `predicate-domain-independent` fixture.

`record.py` and `record-first.py` are the saved local recording drivers, not
portable CI tools: they name the original scratch roots and historical CLI.
`commands.json` records the processes actually executed, including expected
nonzero rejections. Reproducing a historical comparison requires the recorded
baseline executable or rebuilding its historical source. This bounded record
is not a universal source-preservation theorem, a new guarantee admission or
full release validation.
