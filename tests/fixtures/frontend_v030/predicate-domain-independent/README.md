# Independent explicit predicate-domain checks

This informed study independently checks the #25 explicit unary predicate-domain
implementation. It does not admit a new guarantee or prove source preservation.
The production migration, active consumer inventory and original 26-case study
are recorded in the adjacent [predicate-domain fixture](../predicate-domain/README.md).

## First sources and actual failures

`session.json` fixes 41 first sources before observation. `additional-session.json`
fixes five later cases for zero-width exact trees and ordinary nullary/Unit call
arity. The original files under `sources/` remain byte-identical. `before.json`
and `additional-before.json` contain their real baseline stdout, stderr and argv.
`baseline-observer.json` binds the unchanged observer used for these observations;
its source/build provenance is the multi-declaration fixture's `after/validation.json`.

Ten separately saved `repaired/` copies are explained and hashed in `repairs.json`:

- The two Meaning examples initially named an ordinary function `use`, a reserved
  token, and failed parsing. The copies rename that helper to `apply`.
- Eight certified negative examples give the logical reference its own correctly
  typed predicate. This makes the candidate's three-argument predicate use fail
  directly, instead of stopping first at the logical reference's restricted use.

The corrected copies were also saved before their first observations, retained in
`repaired-before.json`. There are 56 final observations: 46 originals and ten
corrected copies. Current checking accepts sixteen and rejects forty. Nineteen
finite diagnostics change: six previously accepted observations now reject with
`arity`; thirteen existing shape rejections add the word `exact` to the message.
`comparison.json` retains each old/new diagnostic. Observer exit zero means the
observer completed; the `finite.check` line separately records acceptance.

The first current six-test run had five successes and one test assertion failure:
it expected `TypeMismatch` for multiple predicate parameters. The implementation's
`Arity` category correctly distinguishes the argument-count failure; Meaning keeps
its existing `TypeMismatch` category. The initial test file, actual output and
assertion correction remain in `first-current/`. Production source was not changed
for this failure. The final seven-test suite also covers zero-width tree rejection
and ordinary zero/Unit argument-count differences.

## Independent semantic checks

`tests/predicate_domain.rs` checks these separate boundaries:

- Both computed forms accept one matching flat, left-nested or right-nested
  three-bit domain. Their retained truth table must be exactly
  `[0,1,0,0,1,0,1,1]` for `(a AND NOT b) XOR c`, with leaf weights 1, 2 and 4.
- Each generated computed operation is extracted into a small **untrusted** open
  RawProgram and checked afresh by the native function checker against an
  independently specified diagonal `zeta_8^f`. Every exact matrix coefficient is
  checked, followed by its action on unequal complex coefficients with reference
  dimension two. The extraction is a test adapter, not source-preservation evidence.
- Noninjective AND and constant predicates stay legal in both forms. Predicate
  totality, coherent-lift injectivity and permutation bijectivity are distinct
  obligations; a unary domain must not conflate them.
- All eighteen cross-tree substitutions reject at the actual predicate/Meaning
  use. `Unit` also remains distinct from `(Unit,Unit)` in all three paths despite
  their common zero width. Meaning's result interface remains exactly
  `(Bit,(Bit,Bit))`, retaining phase-exponent weights 1, 2 and 4.
- Both computed forms reject nullary and multiple-parameter predicates. Explicit
  unary predicates may call unchanged ordinary three-argument or nullary helpers;
  ordinary argument packing and omission still reject.
- A Unit predicate, certified computation and Meaning-bound provider each retain
  scalar phase `exp(i*pi/4)` under coherent control. The measured one probability
  is independently `(1 - 1/sqrt(2))/2`, including linear Unit ownership.

The exact action checks cover at most three data bits and one computed auxiliary.
No maximum-size case, ignored lane or 4,000-case differential suite was newly run.
Existing ownership, effect, cleanup and source-snapshot checks are exercised by
the production owner's separately recorded regression suites.

## Baseline and migrated artifacts

`baseline-action/` records four selected tests compiled against an isolated source
snapshot of commit `a6c8bb7e83a5885c39af1d528afd9a480dfdf62c`: the old three-parameter
left-fold action, all three explicit trees, noninjective predicates and controlled
Unit phase. All four passed. Its source hashes were checked against that commit.
The first harness compile failed because its copied common helper lacked the
adjacent Qargo manifest; that setup failure and the successful second compile are
both retained. No baseline production source was edited.

`after/proposals.json` records eight byte-identical baseline/current finite QIRF
pairs: six unchanged explicit-domain sources and two old left-fold sources compared
with their unary left-domain counterparts. These specific closed observe artifacts
contain no function-evidence/source snapshots. Their explicit input/output tree
reassociation lowers to the same ordered wire map, so byte equality across trees
does **not** make the source types equal. Snapshot-bearing artifacts from other
clients require the separately recorded source-identity migration comparison;
this fixture makes no blanket whole-artifact equality claim.

## Performed validation and reproduction

Final recorded results: seven tests passed, zero failed/ignored on Rust 1.98.1 and
the actual Rust 1.85.0 toolchain; both all-target Clippy runs and formatting passed.
The MSRV bin directory was explicitly prepended to PATH. `rustc`, `cargo` and
`cargo-clippy` paths/versions, source/test/kernel hashes and raw outputs are in
`after/`. All source/test inputs remained unchanged across the final replay.

Prepare an isolated baseline from the commit above with Cargo.toml, Cargo.lock,
README.crates.md, src and stdlib, then build its library and qleisli binary offline.
The recorded final replay command is in `replay-command.json`; a new replay uses:

```sh
python3 tests/fixtures/frontend_v030/predicate-domain-independent/replay.py \
  --tree /path/to/Qleisli --baseline-tree /path/to/isolated-baseline \
  --kernel /path/to/Qleisli/lean-kernel/.lake/build/bin/qleisli-kernel \
  --output-dir /private/tmp/new-predicate-domain-replay \
  --msrv-bin /path/to/1.85.0-toolchain/bin
```

`files.json` hashes every stored file except itself. Compiled executables are
represented by their hashes; they are not copied into this fixture. Historical
authoring sources and fixed diagnostic records elsewhere in the repository are
unchanged; this study does not silently replay their old arity as current syntax.

Independent review covered the shared `Compiler::check_predicate_domain` and both
call sites, ordinary basis evaluation, Meaning signature/evidence paths, and the
separate native table/cleanup conditions. There is no outstanding concrete finding.
