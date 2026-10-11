# Independent bounded scanner review

This packet preserves an independent comparison of the finite lexer and sized
token adapter before and after the shared physical scanner extraction. The
baseline is `0605d716c2a79e2b6776476981c3e25cdfa1709b`. The after snapshots are the
reviewed, then-uncommitted working sources; their exact bytes, rather than a
later working tree or release name, identify the comparison.

The review found no unintended discrepancy in the tested lexical domain. This
is bounded regression evidence, not a proof of parser equivalence, source
preservation, semantic correctness or native acceptance. Doc attachment and the
two ASTs/resolvers remain separate. Existing integration tests cover selected
attachment and parsing behavior; the differential harness compares lexing only.

## Frozen inputs and extraction

`manifest.json` records the baseline commit and SHA-256 of both real comparison
files (`src/frontend/lexer.rs` and `src/frontend/sized/parser.rs`) before and
after, plus the new `src/frontend/scanner.rs`. Full input snapshots live under
`inputs/`; they are historical test evidence, not alternate production sources.

`replay.py` contains the extraction procedure. It embeds the finite lexers and
shared scanner, extracts the sized `tokens` functions before the parser, and
adds small data-only `Span`, `DocComment`, token and error representations.
It removes Rust inner module documentation and exposes the private sized token
functions to the harness. It does not rewrite their scanning logic. The
data-only wrappers do not test the production definitions of those structures.

`cases.rs.txt` contains the fixed comparison driver. `harness.rs` is the original
self-contained review harness, preserved byte for byte. Replay verifies every
snapshot hash and the regenerated harness hash before compiling it. An optional
source-tree check also verifies the snapshots against the baseline Git objects
and the current production files. The default frozen replay remains usable when
production code changes later.

## Compared domain and intended exclusion

- All 65,536 four-atom strings over a fixed 16-element ASCII alphabet, including
  adjacent punctuation, comment delimiters, whitespace and numeral prefixes.
- 100,000 deterministic strings of 12 fragments, with seed
  `0x0123456789abcdef`. Fragments include contextual/reserved words, punctuation,
  numeral spellings, UTF-8 comments, CRLF, nested/doc comments and malformed
  delimiters. The original `usize` indexing requires a 64-bit host; replay
  rejects a different Python host pointer width.
- 40 additional forbidden-character cases compare the finite old/new lexers
  only: eight characters in five source/comment positions.

The finite comparison therefore covers **165,576 inputs**; the sized comparison
covers **165,536 inputs**. Results compare complete Debug representations,
including token contents, byte spans, rejection messages and retained finite
doc comments. A mismatch aborts the comparison with the input and both results.

The sized comparison deliberately excludes the 40 extra forbidden-character
cases and does not generate those characters in its random fragment set.
Adopting the finite policy intentionally rejects bare CR, control characters,
unsupported whitespace and line separators in sized source, including comments.
Those are recorded migration changes, not claimed old/new equality. The real
sized regression tests separately verify their new rejection and exact spans.

## Replay and recorded results

From the repository root, using Python 3.11+ and an available Rust compiler:

```sh
python3 tests/fixtures/frontend_v030/shared-scanner/independent-review/replay.py --output-dir /private/tmp/qleisli-shared-scanner-recorded-review --check-source-tree /Users/masa/git/Qleisli
```

That exact command was run for this record. For another checkout, replace the
source-tree path. Omit `--check-source-tree` to replay only the frozen evidence.
The output directory receives generated source, a temporary executable, exact
compiler/comparison argv, exit codes and separate stdout/stderr streams.
The retained `results/run.json` and adjacent streams record the successful run;
`results/rustc-version.stdout.txt` identifies the actual compiler.

The comparison reported:

```text
PASS: 165576 finite old/new comparisons; 165536 sized old/new comparisons on inputs without the intentionally tightened character policy
```

The following existing tests were rerun to retain actual separate stdout/stderr
and argument/environment records in `results/tests.json`:

```sh
QLEISLI_KERNEL=/Users/masa/git/Qleisli/lean-kernel/.lake/build/bin/qleisli-kernel cargo test --offline --test parser --test documentation --test sized_source
cargo test --offline --lib frontend::sized::parser::token_tests -- --nocapture
```

Results: documentation **11 passed**, parser **18 passed**, sized source
**29 passed / 3 ignored**, adapter unit tests **3 passed / 80 filtered out**.
The total is **61 passed, 0 failed, 3 ignored**. This includes the existing
20,000-depth finite comment regression and sized 64/65-depth checks.

The three sized-source tests retain their existing explicit ignore reason,
`requires the separately built and audited Lean kernel`:

- `direct_finite_source_gates_preserve_entangled_h_x_references`
- `reordered_fourier_roots_and_inverses_preserve_native_phase_and_reference`
- `rust_source_proposals_check_natively_and_preserve_small_system_coefficients`

The default test selection was retained; `--ignored` was not requested.
`QLEISLI_KERNEL` was supplied for the existing native-backed documentation test,
but setting it does not override Rust's explicit ignore attributes. These
results do not claim the ignored tests passed. No full Rust suite, full corpus
replay, Lean rebuild/audit or newly generated maximum-size quantum case was run.
The parent packet's original before/after sources and observations were not
changed by this review.
