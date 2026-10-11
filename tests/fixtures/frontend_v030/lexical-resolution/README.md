# Common lexical binding study and bounded replay

This is an informed implementation study for the shared lexical-resolution
unit recorded in Issue #32. It is not a blind model benchmark, a new syntax
adoption, a completed common checker, or a source-preservation proof.

`initial-study/` retains all ten original sources, manifests, the observer and
actual first diagnostics from the read-only study at `af21dd5`. Those files
were copied unchanged before this implementation. `baseline.json` identifies
an isolated `git archive` of `fae0e6a`; its production source, Cargo files and
stdlib are identical to `af21dd5`. The archived source is rebuilt offline.
The retained `before/` output is a fresh replay on that fixed source, not a
replacement for the original study's observations.

The implementation assigns each lexical binder and name occurrence a stable
ordinal within its `DefId`. Scope and source-span metadata belong to the same
table. Equal spans do not merge identities. Borrowed AST addresses are used only
to locate occurrences while projecting one immutably borrowed declaration;
projections retain numeric IDs and owned tables, never addresses. Cloned or
relocated syntax gets a newly constructed reverse index. The index traverses
an explicit work stack and restores scopes with an undo log; it does not
recursively walk the AST or copy the complete visible-name map per scope.

Source identity does not replace execution identity. Repeated calls, recursive
sized activations and static-fold iterations retain their existing fresh owner
identities and moved-state checks. The table classifies names; existing type,
effect, capture, access and ownership checks decide whether a use is allowed.
In particular a global or static-parameter candidate does not make a local or
spent runtime value callable. Source-to-IR checks and independent native
acceptance remain separate obligations.

## Preserved profile distinctions

The first ten programs cover initializer-before-rebinding order, duplicate
patterns, moved names hiding imports, live-owner hiding, static parameter
shadowing, branch rebinding, repeated fold activation, zero-fold capture,
and the current sized one-function restriction. Finite source can rebind a
static operation's spelling as a runtime value; sized preparation rejects that
shadow. Finite source still rejects sized static branches/folds, and sized
preparation still rejects additional function declarations. The unit does not
add general local functions, mutual recursion, new syntax or new type profiles.

`additional-study/` retains two small finite static-call ordering cases. The
first setup attempt used a malformed manifest and the second omitted the
explicit checker; their actual output is retained and is not counted as a
semantic baseline. `before.json` uses the corrected edition-2026 manifest and
explicit compatible checker, with unchanged `.qli` sources. A runtime shadow
of `U` with argument `missing` first reports the missing argument; with a valid
argument it reports that a runtime value cannot be a static operation.

## Reproduction

Run the driver on a buildable checkout and an absolute, matching native checker:

```sh
python3 tests/fixtures/frontend_v030/lexical-resolution/replay.py \
  --tree /absolute/checkout \
  --kernel /absolute/qleisli-kernel \
  --output-dir /private/tmp/new-lexical-replay
```

The output directory must not already exist. The driver records exact argv,
cwd, checker selection, statuses and raw streams. It builds a small observer,
checks the ten original and two additional source programs, emits six actual
proposal files, and runs six independent native checks and six one-qubit
executions. The scenarios are finite rebinding and branching, a two-iteration
sized fold, a small decreasing recursive specialization, and one generic client
with two different module-qualified providers. No maximum-size case is run.

```sh
python3 tests/fixtures/frontend_v030/lexical-resolution/compare.py \
  --before tests/fixtures/frontend_v030/lexical-resolution/before \
  --after /private/tmp/new-lexical-replay \
  --output /private/tmp/lexical-comparison.json
```

The comparison requires identical exit status, stdout and stderr for twelve
source observations and twelve check/execution observations. It also compares
the six actual proposal byte strings and their baseline hashes. Build output
and the proposal-writing status lines are excluded because they embed checkout
or output paths; their command statuses must still succeed. No diagnostic,
proposal or execution-output normalization is performed.

`before/retention.json` binds the unmodified retained baseline outputs. Binary
executables are not copied into this fixture; their hashes and actual paths
remain in `executables.json`. The original before run predates the addition of
the two static-shadow cases, which are retained in `additional-study/before.json`.

## Regression scope

Private table tests cover equal-span binders and uses, clone/reallocation
boundaries, later static-natural parameters in annotations, late import binding,
static candidates beneath runtime shadows, and a modest constructed AST beyond
the parser's nesting boundary. The scope test compares both the historical
name-keyed algorithm and the current identity-keyed algorithm against the same
7,225-case independent owner/scope model. These checks do not establish general
source preservation or admit a new formal guarantee.

## Recorded result and compatibility

The final source-stable replay passes: all 24 observed exit/stdout/stderr
triples and all six actual proposal byte strings match the fixed baseline.
Each version separately completed six native checks and six one-qubit runs.
`comparison.json` contains the exact matching proposal hashes;
`after/source-identity.json` binds the production Rust/Cargo/stdlib inputs,
fixture source inputs and native executable, checked unchanged across the run.
The baseline source identity was recomputed from its unchanged git archive;
the original baseline executable identity is retained separately.

Finite public AST, project and error representations are unchanged. The private
projected representation changes the derived `Debug` text of sized
`ParsedProgram`, and therefore of `Instantiation` and `ElaboratedProgram` that
contain it. That text now contains lexical identity metadata. Public method
signatures, source accessors, concrete IR accessors, `Clone`, `Send` and `Sync`
are retained. Symbolic diagnostic formatting deliberately retains the previous
name-based `Linear` representation. Debug text is not used as artifact identity.

The latest all-target Clippy check used Homebrew Rust/Cargo 1.98.1 and Clippy
0.1.98. The MSRV check prepended the explicit 1.85.0 toolchain `bin` directory
to `PATH`; its recorded `rustc`, `cargo` and `cargo-clippy` executables and
version output are all 1.85. `rustup run 1.85.0 cargo clippy` without that PATH
correction would select this machine's Homebrew Clippy, and is not the recorded
MSRV check. Both checks pass with `-D warnings`. Detailed performed-test scope
and counts are in `validation.json`; the sized migration's separate regression
record is in `../sized-lexical/`.
