# Independent sized declaration integration study

This is an informed, bounded implementation study for the adopted #32 unit that
removes the sized profile's one-function-per-module restriction. It is not a
blind authoring benchmark, a new primitive admission, or a source-preservation
proof. The implementation and original ten-case study are recorded separately in
[multi-declaration](../multi-declaration/README.md).

## Saved sources and observations

`session.json` records sixteen sources before observation; the two later focused
diagnostic cases were saved in `additional-session.json` before their observation.
Every original `.qli` byte remains unchanged. `before.json` and
`additional-before.json` retain actual stdout/stderr and argv from the unchanged
lexical-complete observer. `before-provenance.json` binds that executable and all
96 production inputs to commit `0d93a186fbe2e1345542595b75f680f867e1e4e5`.
The observer source and executable provenance remain in the adjacent
[lexical-resolution](../lexical-resolution/README.md) fixture.

`after/` records all eighteen observations, exact compiler commands, source/test
hashes, kernel hash, observer identity and raw command streams. `comparison.json`
records five accepted sized sources and thirteen rejected sources. Fifteen sized
diagnostics deliberately changed when the former second-declaration rejection
was removed. The remaining three sized observations and all 36 finite-profile
observations are unchanged. The finite profile continues to reject the sized
`std::quantum::phase` import; this study does not unify primitive catalogs.

## Independent semantic expectations

The integration tests live in `tests/sized_declarations.rs` and check:

- A public `z_entry` before private `a_phase` and `m_swap`, the reversed declaration
  order, and the equivalent split-module source. All implement the separately
  written amplitude equation `|a>q|b>r -> i^a |b>first|a>second`.
- Same-named `a::gate` and `b::gate` with distinct X and S meanings, selected in
  the order A, B, A. Both their analytic output coefficients and repeat-A proposal
  bytes are checked. A same-module private identity provider remains usable.
- Private sibling calls and providers, public host entries, rejection of private
  host entries and external private providers/imports, local/import collisions,
  ambiguous imported leaf names, duplicate definitions and unsupported renaming.
- Checking every unused sibling, including an invalid type, repeated quantum
  owner, invalid unselected static branch and illegal capture in a zero-iteration
  fold. The first invalid declaration follows source order even when DefId order
  differs. Retained module text and relocated diagnostic spans are checked.
- Mutual sibling and unused-provider cycles remain rejected. Actual self-calls
  with decreasing `n` elaborate distinct instances for 2, 1 and 0; nondecreasing
  recursion remains rejected.

Each final seven-test run includes eight native original-payload/request checks
and eight executions with one or two quantum bits and reference dimension two.
Unequal complex amplitudes make phase and labelled-axis errors observable;
coefficients are compared directly without normalization or phase removal.
Only the selected Lean checker issues the accepted hierarchy handles. Its
producer-derived request is a consistency check; the independently written
amplitude expectations supply bounded semantic regression evidence. No general
source, lowering, decoder or simulator theorem follows from these tests.

The initial six-test harness had two assertion errors: it expected `name` instead
of the existing `ownership` code for a captured quantum owner, and omitted the
backticks in the parser's semicolon diagnostic. The original harness and exact
failure details are retained in `initial-test/`. No production fix or source
change was needed. The corrected six-test run is in `validation/`; the final
seven-test runs additionally check first-error source order and import ambiguity.

## Validation and replay

Final results in `after/`: seven tests passed, zero ignored, on each of the actual
Rust 1.98.1 and Rust 1.85.0 toolchains; both all-target Clippy runs and formatting
passed. The 1.85 toolchain directory was explicitly prepended to PATH, and
`rustc`, `cargo` and `cargo-clippy` identities were recorded before execution.
No maximum-size case or ignored test was newly run.

`single-declaration-replay/` records the existing lexical fixture replay against
this source. Its comparison to the retained lexical-complete baseline preserves
22 observations and six exact proposal byte strings, plus six successful native
checks and six one-qubit executions. Only `multiple-acyclic` and
`multiple-unused-invalid` changed as intended; both old/new raw diagnostics are
included in `single-declaration-comparison.json`. This supplements the new tests
without rerunning the 4,000-case ownership differential suite.

To reproduce the observations, independent tests, both toolchain checks and source
stability verification, choose a new output directory and the installed 1.85 bin
directory:

```sh
python3 tests/fixtures/frontend_v030/sized-declarations-independent/replay.py \
  --tree /path/to/Qleisli \
  --kernel /path/to/Qleisli/lean-kernel/.lake/build/bin/qleisli-kernel \
  --output-dir /private/tmp/new-sized-declaration-replay \
  --msrv-bin /path/to/1.85.0-toolchain/bin
```

The exact performed invocation is saved in `replay-command.json`. To replay the
prior one-function behavior, build the observer against commit `0d93a18` and use
the saved source directories. Rebuilding native binaries may change executable
hashes; the recorded source hashes and actual outputs are the historical record.
`files.json` binds every stored file except itself; executables are represented by
hashes rather than copied binaries.

Independent review covered the four production changes in `sized.rs` and
`sized/{ast,parser,check}.rs`, their shared DefId/ast_index mapping and existing
elaboration cache/host visibility paths. There is no outstanding concrete finding.
Private `Module` Debug now contains the source-order `functions` collection; that
derived display can also appear through public ParsedProgram-containing Debug
output. No stable Debug serialization is claimed.
