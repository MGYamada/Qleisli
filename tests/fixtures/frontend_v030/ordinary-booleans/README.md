# Common ordinary Boolean preparation and finite execution

This is an implementation checkpoint within
[Issue #32](https://github.com/MGYamada/Qleisli/issues/32), not completion of its
common-language contract or the 108-Issue plan. Edition remains 2026 and the
development version remains 0.3.0-alpha. No Lean definition, native schema,
dependency version, admitted guarantee or human adoption record changed.

## Implemented scope

Finite evaluation and sized symbolic/concrete checking now use one exact
ordinary Bit judgment and eager left-to-right operand traversal. Their actual
Raw constant/not/and/xor instructions use the same emitter. Sized concrete
steps retain literal values, operand/result identities, original source spans
and normal call/effect accounting. A dropped result does not erase evaluation.

`ElaboratedProgram::lower_raw` produces an immutable source-bound finite
proposal for Unit/Bit/products and specialized ordinary calls. Whole argument
and result trees remain in its source instance; flattened Raw classical IDs
are not source type identity. Every executed proposal is independently accepted
by the existing native kernel. Open classical inputs can be represented and
checked but are not executable through `sim::run_closed`.

The independent source-step replay inspects actual Raw instructions without
calling the common emitter. It checks literal/opcode/operand/output identities,
whole call trees, a fresh source-ID map for each call activation, globally fresh
Raw IDs, declared effects, final output order and complete instruction
consumption. The public check additionally requires the exact accepted proposal
bytes. It neither grants native acceptance nor proves AST-to-step preservation.

The first adapter explicitly rejects quantum/Bits values, primitives and
operation providers before emission. Existing hierarchy contracts stay intact;
Boolean steps that cannot be represented reject at their source locations.
Mixed quantum execution, measured Boolean postprocessing, fine phases, explicit
runtime invocation and CLI integration remain required implementation work.
No failed native decision is retried as a weaker request.

## Preserved first evidence and repairs

The [authoring study](../../authoring_sessions/ordinary-boolean-v030/session.json)
preserves twelve original complete projects before thirty-three observations
with the existing executable. Its first source manifest is
`21063a9fac152575394e42f68a338b72fb43a9db9351c0a71684ee5e7d232863`;
all original source/manifest and observation bytes remain unchanged.

`first-library/` records the first successful direct Raw mutation regression.
`latest/` preserves the first integration run: four new tests passed and four
failed. Three shared wrappers omitted public host-entry visibility. Another
test expected a type error where forbidden quantum capture correctly failed
first. `first-test.rs.txt` preserves that original test source; `test-repair.json`
and `test-repair.patch` bind its explicit corrections. No production visibility
or ownership rule was relaxed. A separate zero-fold wrong-type example covers
the intended Boolean judgment.

The first metadata driver completed its seven checks, then failed because
`mdbook` was absent from PATH. Its outputs remain in `metadata/`; the separate
`book-validation.json` records the existing pinned executable by absolute path,
version and hash. Neither failure is rewritten as a successful initial run.

## Validation

`validate.py --record latest-fixed` and `--msrv --record msrv` each pass:

- 78 tests across nine focused integration targets;
- one direct native-valid mutation/replay regression;
- all-target Clippy with warnings denied, and formatting.

These use actual Rust/Cargo/Clippy 1.98.1 and 1.85.0. Their 254-file selected
source manifests are identical:
`184a6135e7dde057a3bf65eee63c7d7724d28f90cf3cd57ea179670feeb046fb`.
Fixtures outside that selected manifest remain bound by the recorded Git base;
this is not a claim of a complete dependency/input closure or all-target
runtime validation. The existing native checker was reused without a new local
Lean build/audit/replay.

Independent oracles cover all four two-bit truth rows, exact nested products
and Unit, repeated output aliases, dropped evaluated expressions, repeated
helper activations and static folds at zero/one/two. The effect case checks both
retained source steps and an actual finite MeasureZ preceding ClassicalAnd;
its deterministic zero result alone would be insufficient evidence. Unused
declarations, static branches and zero-fold bodies still reject invalid types,
effects and stage leakage.

Four mutated Raw programs first pass native validity, then fail the independent
step matcher: AND changed to XOR, a changed literal, an extra unused instruction
and reversed output IDs. The last mutation is structural even when the selected
010 result is numerically palindromic. This exercises the matcher beyond the
outer artifact-identity check and demonstrates the distinction from validity.

`cli-build.json` identifies the current CLI and its actual source hashes.
`observe_cli.py` reconstructs fixed commands without executing historical
record contents. All 21 finite check/closed-run observations are byte-identical
to the first study. Twelve sized CLI calls remain rejected by their actual
stages; seven diagnostics change as Boolean syntax reaches later checking or
lowering. Raw API execution is established by the Rust tests, not inferred from
those CLI failures.

Inventory, production coverage, fourteen coverage regressions, fifteen native
scheduler regressions, authoring/constitutional identity and documentation
checks pass. Native comparison scheduling now has 67 groups and 85 commands,
including both new tests. mdBook 0.5.4 builds twenty HTML files; rendered/print
validation checks 741 links and 266 anchors.

Validation reuses `/private/tmp/qleisli-bounded-validation-target`, with
incremental compilation and debug information disabled and two build jobs.
No new whole-source snapshot, maximum-size quantum case or large Lean build was
made. Old authoring and migration records are not executable current clients.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
