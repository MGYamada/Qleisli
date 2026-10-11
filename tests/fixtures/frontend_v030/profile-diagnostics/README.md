# Shared-parser profile diagnostic regression

This bounded informed regression records the stale expectation discovered in
hosted run 37204302133. It changes a conformance test, not source acceptance,
the frontend implementation, native verification or a language specification.
The shared-parser migration in Issue 32 already made static Nat parameters
representable in the common AST while retaining a located finite-profile
rejection. The authoring corpus still expected the former parser's category.

The original twelve rejected sources remain unchanged in
`tests/fixtures/qli_authoring/rejected/`. The copies in `sources/` retain their
exact bytes and the test tree's schema-2 edition-2026 manifest. All twelve
source files also match commit
`0605d716c2a79e2b6776476981c3e25cdfa1709b`.

## What the comparison establishes

`before.json` is a fresh replay with the pre-migration binary from that commit;
it is not relabelled as an original authoring session. Its existing isolated
source tree's 92 production files under `src`, `stdlib`, `Cargo.toml` and
`Cargo.lock` were compared byte for byte to the commit. `after.json` uses a
fresh `cargo build --offline --lib --bin qleisli` from
`af21dd5d3e4373083edcf207ef9890967d4c7dab`, with no production-source changes.
Both records retain actual argv, exits, streams, source hashes and executable
hashes. `source-identity.json` records the checked identities.

All twelve sources return exit 1 before and after. Eleven have identical JSON
stdout and stderr. Only `static_nat.qli` changes its diagnostic:

| Boundary | Code | Message | Primary UTF-8 byte span |
| --- | --- | --- | --- |
| Former finite parser | `parse` | ``parse error: expected `Op`, found identifier`` | `27..30`, the `Nat` spelling |
| Shared parser and finite profile | `unsupported` | `finite profile does not support static Nat parameters` | `24..25`, the parameter `n` |

The unchanged cases cover the still-unimplemented Basis parameter grammar,
exact product types and meanings, sealed operation providers, name resolution,
owner reuse/aliasing/drop, missing adjoint/application access and the structural
computed-block certificate restriction. Rejection is retained in every case;
these observations establish no new accepted language feature or proof.

The updated [Rust corpus test](../../../qli_corpus.rs) checks both sides of the
boundary for the exact static-Nat source: the parser produces a Natural static
parameter, and finite checking returns the named unsupported diagnostic at
that parameter's original span and line/column. This guards against moving the
failure to an unrelated later error, or accidentally accepting the source.

## Failure and validation records

`stale-expectation.json` preserves the locally reproduced failing test before
the test expectation was corrected. `hosted/14.stdout` and `hosted/14.stderr`
are unmodified raw logs from command 14 of distribution artifact 11304737633;
`hosted/provenance.json` binds them to the downloaded archive, the tested merge
commit and the selected original command metadata. The hosted raw logs include
other pre-existing suites; they are historical observations, not a claim that
this repair reran the full distribution or maximum-size cases.

`validation.json` records both completed local commands with the matching
absolute `QLEISLI_KERNEL` path:

```sh
cargo test --offline --test qli_corpus
rustup run 1.85.0 cargo test --offline --test qli_corpus
```

Rust 1.98.1 and Rust 1.85.0 each pass all 12 tests, with 0 ignored. Formatting
and whitespace checks also pass. No ignored or new maximum-size case was run.
The tests retain the existing small finite simulation and native-check oracles;
they do not prove general source preservation or semantic soundness.

To repeat the twelve diagnostic observations with an explicitly built binary:

```sh
python3 tests/fixtures/frontend_v030/profile-diagnostics/replay.py \
  --binary /absolute/path/to/qleisli \
  --kernel /absolute/path/to/qleisli-kernel \
  --output /private/tmp/profile-diagnostics-new.json
```

The recorder refuses to overwrite an existing output. `files.json` hashes
every retained file other than itself. Historical records are retained as
recorded, including temporary absolute paths in executed commands.
