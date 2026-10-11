# Shared physical scanner: bounded migration evidence

This informed regression packet accompanies the shared lexical boundary recorded
in [Issue 32](https://github.com/MGYamada/Qleisli/issues/32). The initial sources
and actual old-CLI observations were saved before editing either scanner, at
commit `0605d716c2a79e2b6776476981c3e25cdfa1709b`.

`context.json` records source hashes, baseline revision and executable hash.
`before.json` and `after.json` retain exact argument lists, exits, stream paths
and emitted proposal hashes. The proposal files themselves were temporary files;
their observed hashes are retained, not claimed to be replayable artifacts.
Raw `.qli` files deliberately contain the named noncanonical characters. Do not
normalize their bytes when viewing or editing other fixtures.

These are curated lexical experiments, not blind model authoring, native
acceptance, constitutional guarantee discharge or source-preservation proofs.
Successful `sized emit-proposal` only produces untrusted JSON. No kernel was
selected or invoked by those nine commands.

| Source | Before | After |
| --- | --- | --- |
| Japanese line comment with CRLF | Proposal emitted | Same proposal hash |
| Bare CR in block comment | Proposal emitted | Located parse rejection |
| Vertical tab before declaration | Parse rejection | Located parse rejection with shared message |
| Form feed before declaration | Proposal emitted | Located parse rejection |
| Bidi control in block comment | Proposal emitted | Located parse rejection |
| Nonbreaking space in line comment | Proposal emitted | Located parse rejection |
| 64 nested block comments | Proposal emitted | Same proposal hash |
| 65 nested block comments | Parse rejection | Same capacity rejection |
| Unclosed Unicode block comment | Parse rejection | Same unclosed-comment rejection |

The common scanner owns UTF-8 byte positions, ASCII word/numeral boundaries,
atomic punctuation, LF/CRLF and forbidden-character rules, nested comments and
doc-comment recognition. The finite lexer and sized parser use temporary token
projections. They preserve contextual versus reserved words, canonical numeral
diagnostics and adjacent punctuation grouping. In particular `==>` remains
`=` plus `=>` in the finite view, while `<->` remains `<` plus `->` in the sized
view. Comments and whitespace never join separated punctuation.

No new syntax is enabled. The finite public token enum/API is unchanged. The
sized adapter retains its 10,000 projected-token and 64-comment-depth limits;
EOF/comments consume no token allowance. Finite comment nesting remains
iterative with no new depth limit, including its existing 20,000-depth test.
Existing source-byte/module limits and lowering capacities are unchanged.

Doc classification and character validation are shared; doc attachment is still
a finite-AST rule. The sized parser still ignores doc metadata, including
misplaced docs. A regression explicitly records this remaining difference,
which must disappear with the common AST/grammar. This step does not claim that
the two parsers, ASTs, resolvers or type checkers have already been unified.

## Performed validation

- `cargo test --offline --lib frontend::sized::parser::token_tests -- --nocapture`:
  3 passed. Small injected bounds test projected token counting, EOF/trivia,
  comment nesting and punctuation adjacency; no new maximum-size case.
- `QLEISLI_KERNEL=/Users/masa/git/Qleisli/lean-kernel/.lake/build/bin/qleisli-kernel cargo test --offline --test parser --test documentation`:
  29 passed (18 parser, 11 documentation), including existing token-prefix,
  UTF-8, doc attachment, deep-comment and native-backed ownership checks.
- `cargo test --offline --test sized_source scanner`: 2 passed.
- `cargo test --offline --test sized_source preparation_limits_and_utf8_diagnostics_are_explicit`:
  1 passed.
- `cargo test --offline --test sized_source original_bytes_and_contextual_identifiers_are_retained`:
  1 passed.
- `cargo test --offline --test sized_source grouping_semicolons_and_count_precedence_match_the_source_contract`:
  1 passed.
- `QLEISLI_KERNEL=/Users/masa/git/Qleisli/lean-kernel/.lake/build/bin/qleisli-kernel cargo test --offline --test sized_review_diagnostics`:
  2 passed, including rejection-only process fault injection.
- `cargo fmt --all -- --check` and `git diff --check`: passed.
- Nine old/new CLI observations above: all recorded outcomes matched the stated
  lexical migration. The two successful pairs had identical proposal hashes.

The initial combined parser/documentation invocation omitted `QLEISLI_KERNEL`:
10 documentation tests passed and the native-backed test failed because no
checker was selected; Cargo stopped before running the parser suite. The rerun
above supplied the existing built checker and passed all 29 tests. The earlier
`cargo test --offline --test parser --test documentation --test sized_source --no-run`
also compiled successfully.

No Lean source/proof changed. No full Lean rebuild/audit, full Rust suite,
full corpus replay or newly generated maximum-size quantum case was run for
this scanner step. The existing built kernel was used only where the retained
documentation test required native acceptance.
