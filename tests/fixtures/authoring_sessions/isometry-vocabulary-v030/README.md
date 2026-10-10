# Adopted isometry spelling: first implementation stage

This informed maintenance record implements the spelling selected in
[Issue #57](https://github.com/MGYamada/Qleisli/issues/57). It is neither a
blind authoring benchmark nor completion of that Issue. The original context,
two sources and baseline parse refusals remain unchanged.

The four `after/` observations run those same sources with the changed CLI.
Preparation passes both automatic and explicit Raw native checking and runs
as the zero state. The observing counterexample now reaches the body-effect
check and fails with `effect`, rather than being refused by the grammar.
Command arguments, exit codes, complete JSON and observed executable hashes
are recorded separately from the source hashes. These observations do not
establish compiler, runtime or source-preservation proofs.

`tests/isometry_source.rs` also checks the actual inferred/asserted effect,
fresh Raw acceptance, original-body replay, both versioned exports and a
closed finite observation adapter. The adapter is explicit: the original
quantum-result source is not a finite classical-result entry. A literal
phase-sensitive numerical regression checks the canonical spelling through
the CLI. It is not an exact mathematical discharge.

The existing `iso` spelling is temporarily accepted through the very same
effect assertion while active sources migrate. The control comparison checks
identical Raw bodies; it supplies no distinct effect, inverse or control
authority. Versioned QIRF 1/2 still serializes `"iso"` and checks it freshly.
Public effect names/diagnostics, remaining active sources and legacy-prefix
retirement remain unfinished under #57. Historical records must retain their
original bytes. No transport migration or permanent source alias is adopted
by this stage.

The adopted QS/PR/RS and EXACT interpretations and two scoped QLV1 guarantees
are unchanged. This lexer connection adds no semantic primitive or trusted
acceptance path and discharges no new constitutional obligation.

## Subsequent source-prefix retirement

The temporary acceptance described above records the first implementation
stage. Current source rejects the reserved `iso` token with a located migration
error directing authors to `isometry fn`; comments and longer ordinary
identifiers are unaffected. The original sources and observations here remain
unchanged. The active test comparison now checks `isometry fn` against an
unannotated `fn`, preserving the assertion-versus-inference distinction.
Versioned transport tags retain `"iso"`. Public Rust variants now use `Isometry`;
Lean-side vocabulary compatibility remains pending under #57.
