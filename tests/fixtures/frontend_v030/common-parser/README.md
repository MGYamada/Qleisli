# One parser and source AST: bounded migration evidence

This informed regression packet records the implementation unit in
[Issue 32](https://github.com/MGYamada/Qleisli/issues/32). The initial ten sources
and actual observations in `before.json` were saved before parser/AST edits at
`061636d76a5f502a80ab33deacca9ca548298d82`. The same source bytes and observer
are used for `after.json`. The label `finite` in the observer means the public
`parse_module` entry point; it does not run the finite type checker. The sized
observation includes parsing, profile projection and its existing generic
checker. Neither observation grants accepted IR.

## Implemented boundary

There is one physical scanner, token stream, recursive parser and source
`Module`/`Span` representation. The shared AST now represents the already
supported sized Nat expressions/predicates, register types, static parameters,
static branches/folds and counted-power operation arguments. It preserves
original UTF-8 spans, immediate tuple trees and all declarations.

`Project::load` and `sized::ParsedProgram::parse/load` use the common parser.
`ParsedProgram::syntax` exposes the retained immutable common Module. The file
`src/frontend/sized/parser.rs` is now a source-free AST projection: it does not
scan tokens, read source text or run a second parser. Its output feeds the
existing sized generic checker and lowerer. Finite lowering has an explicit
all-declaration profile preflight before dependency ordering, so unsupported
newly representable syntax cannot hide in unused declarations.

This does not unify name resolution, generic/static checking, ownership/effect
checking or lowering. The sized profile still rejects a second declaration,
located at that declaration, until declaration identities and same-module cycle
checks are implemented. The common parser retains both declarations. No mutual
recursion is newly admitted. Candidate `Op<A,B>` and labelled meanings, Basis
generics and final canonical syntax are not implemented here.

## Compatibility classification

| Input boundary | Current behavior |
| --- | --- |
| Existing finite reserved words used as sized names, such as `fn` | Both entry points reject the identifier at the same span. Rename the binding. |
| `Bits`, `CBits`, `Nat` in ordinary identifier positions | Remain contextual names; size/type/kind positions recognize their existing roles. |
| Misplaced sized doc comments | Rejected by the shared declaration attachment rules, matching the finite path. Move docs to their declaration/module boundary. |
| `for static` and fold `yield` | Parsed in those existing sized contexts. Ordinary identifiers such as `for` and `yield` remain identifiers in other contexts. |
| `controlled(op)(args)` versus `controlled(q)` | The former is the existing controlled application construct; the latter remains an ordinary call. No name-resolution category is guessed. |
| Empty sized block/type/pattern, empty `yield`, empty specialization brackets | Existing spellings are represented by the common syntax path. Sized projection retains their prior meaning; a bare `q[]` is the same owner expression as `q`, and its expression span includes the brackets. |
| Trailing comma in runtime parameters | Retained from the existing sized parser in the common grammar. This is not completion of the general punctuation decision. |
| Symbolic Nat and power repetition counts | Retained as syntax. The finite lowering profile still requires a literal count in 0 through 4096. Parsing a count does not establish its evaluability or execution cost. |
| Static Nat parameters, size predicates, register types, static branch/fold in the finite backend | Located profile rejection until that backend supports them. The common AST is not a promise of backend coverage. |
| `basis fn ... requires ...` | Explicit parse rejection at `requires`; neither former profile supported this combination. |

The token enum now includes the sized arithmetic/comparison punctuation. For
example, `==>` tokenizes as `==` followed by `>`; it remains invalid in the old
finite contexts. Invalid wildcard imports now fail at the parser's identifier
check rather than the scanner's `*` rejection. The common unclosed-comment
message is `unterminated block comment`. Ordinary source spans and all original
bytes remain unchanged; individual malformed-input diagnostics can move to the
shared parser boundary.

Sized source retains its 64 KiB/module, 1 MiB aggregate, 64-module, 10,000-token
and 64-comment-depth limits. Tokens are counted before owning their spellings;
EOF and trivia consume no token allowance. Both syntax paths use the common
64-level recursion/tree bound and 64-field tuple bound; Nat expression trees
retain the 128-depth bound. The common type parser counts the quantum wrapper
and basis parse together: a particular old sized type with 62 nested natural
parentheses now reaches the shared limit one level earlier. The independent
comparison records this narrower edge; no bound is raised and no alternate
grammar is selected by backend. Finite iterative deep comments are unchanged.

The migration remains in edition 2026. These are implementation/release
compatibility changes, not a new constitutional regime or Guardian ruling.

## Sources, proposals and review counterexamples

`before.json` binds source hashes, the initial observer compilation and ten
actual calls. `after.json` records the corresponding common-parser calls.
`proposals.json` retains before/after binaries, argv, exits, streams and actual
untrusted JSON artifacts for four small cases. All four proposal byte strings
and SHA-256 values match. The Nat fold case binds `n = 1`; the cases use at most
one quantum bit. `baseline-build.json` records an offline baseline build from
the exact commit's `Cargo.toml`, `Cargo.lock`, `src` and `stdlib` tree. No native
checker is invoked by proposal emission.

`independent-review/` retains a second reviewer's counterexamples, actual
stdout/stderr and five-module Rust snapshots. Its `before-fix` is an
intermediate uncommitted implementation, not the baseline or a released parser.
The review exposed a debug assertion for invalid basis requires clauses, and
two missed old sized spellings: empty `yield` and `q[]`. All were repaired with
regressions. The final review also checks the full `q[]` expression span while
retaining the narrower identifier span. `retained-paths.json` maps historical
absolute paths in the original observations to local preserved files.

The snapshot parser observer can be rebuilt with:

```sh
rustc --edition=2024 tests/fixtures/frontend_v030/common-parser/independent-review/fixed/main.rs -o /private/tmp/qleisli-common-parser-fixed
/private/tmp/qleisli-common-parser-fixed 'basis fn f(x:Bit)->Bit requires 0 == 0 {x}'
```

For the complete public-API observations against an explicitly chosen checkout:

```sh
python3 tests/fixtures/frontend_v030/common-parser/replay.py --tree /Users/masa/git/Qleisli --output-dir /private/tmp/qleisli-common-parser-replay
```

The driver writes fresh results to the supplied output directory, preserving
the recorded before/after files. To reproduce the baseline, select a checkout
or isolated archive of the pinned commit with its locked dependencies.

## Performed validation and limits

`validation.json` retains exact argv, selected kernel environment, exits,
stdout/stderr and per-suite results. The final recorded selection has
**150 passed, 0 failed, 10 ignored**: 148 integration tests across parser,
documentation, finite compilation, module loading, static operations,
operation parameters, sized source/CLI/profile diagnostics and ordinary
diagnostics, plus two small injected-bound lexer unit tests. All **68 Rust test
targets compiled** with `cargo test --offline --no-run`; this is not a claim
that all targets were executed.

The ten ignored tests retain their existing attributes: three sized-source
native tests, two sized-CLI native tests, and five sized-review dialect tests
(four Python oracle tests and one native test). Their actual reasons appear in
the recorded integration stdout. `--ignored` was not selected. The matching
existing native kernel was supplied for the active tests that require it.

The active tests include same-AST checks through explicit module maps and
project loading, new Nat/count/spans and profile rejection checks, old missing
access/unused branch/zero-fold/owner/cycle checks, original UTF-8/doc rules and
the existing finite deep-comment regression. Early local runs exposed old
expectations for intentionally moved syntax/diagnostics; those were updated
only alongside the explicit migration cases above. An initial command named
nonexistent `frontend`/`cli_sized` test targets and did not run tests; the
recorded final selection uses `compile` and `sized_cli`.

No new maximum-size quantum case, full Rust execution, full corpus replay or
Lean rebuild/audit was performed for this parser unit. This work changes no Lean
acceptance/proof definition and admits no new primitive or formal guarantee.
Frontend AST/projection/proposals remain untrusted, with the existing native
gates unchanged. Proposal identity and passing tests do not prove general source
preservation, QS, PR or RS.
