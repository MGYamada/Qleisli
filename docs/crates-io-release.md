# Preparing and publishing the Rust package

Status: **0.2.1 crates.io publication authorized on 2026-09-30 after rechecking**.
The user's later request to run `cargo publish` outside the sandbox lifts the
earlier preparation-only hold. Upload success must still be confirmed in the
release record. PyPI publication remains a separate action.
The [versioning policy](versioning.md) remains authoritative for compatibility
and the complete release gates. Executed results belong in the
[0.2.1 release record](releases/v0.2.1.md).

## Package identity and user documentation

| Surface | Name or entry point |
| --- | --- |
| crates.io package | `qleisli` |
| Installed command | `qleisli` |
| Rust import | `qleisli` |
| Registry landing page | [README.crates.md](../README.crates.md), selected by `package.readme` |
| Project introduction and theorem goals | [README.md](../README.md) |
| Rust API documentation | [src/lib.rs](../src/lib.rs); docs.rs after publication/build |
| Optional Python host | [python/README.md](../python/README.md); separately installed |

The user adopted the package **and Rust import** name `qleisli` on 2026-09-30,
before the first crates.io publication. The executable already has this name.
Future separate tools may use names such as `qargo` or `qlidoc`; those names
are not new packages, implemented commands or registry reservations here.
See the [name migration](#name-migration-from-github-releases-through-020).
Confirm registry name
availability or publisher ownership at release time; local metadata cannot
establish either. `Cargo.toml` supplies the version, MSRV, Apache-2.0 license,
repository, documentation URL, description, keywords and categories.
There is no separate project homepage, so no duplicate homepage URL is needed.

## Name migration from GitHub releases through 0.2.0

Earlier GitHub releases used package `qleisli-core` and Rust library
`qleisli_core`. This is an **incompatible package/import identity change for
existing Git/path Rust consumers**, explicitly selected by the user for the
first registry release at 0.2.1. It is a narrow exception to the normal
compatible-PATCH policy, not permission for unrelated API, language or
capacity changes. The subsequent breaking type-system work still targets 0.3.0.

After publication, new clients use:

```toml
[dependencies]
qleisli = "0.2.1"
```

Update `use qleisli_core::...` to `use qleisli::...`. Git/path dependencies must
also select the new package name. Existing Rust import spelling can be kept
temporarily with Cargo dependency renaming:

```toml
[dependencies]
qleisli_core = { package = "qleisli", version = "0.2.1" }
```

Before publication, use the same alias with `path = "/path/to/Qleisli"`
in place of `version`. This is a downstream Cargo alias, not a second published
crate. The `qleisli` CLI, `.qli` syntax, IR/evidence semantics and Python package
name remain unchanged. Historical archive names and validation logs retain the
name actually used at the time.

## README presentation

The repository and registry README examples must be executable and agree.
Both document registry installation and installation from a checkout. The
registry README uses absolute HTTPS links
and ordinary Markdown, without GitHub math blocks. GitHub document links are
pinned to the current release tag, matching the packaged source. Local target
checking does not establish that links are live before the verified source tag
is pushed; publish that tag before uploading the registry artifact.

Document ordinary Rust CLI/library use without Lean, Python or LLVM. Python
hosting and optional QIR input have their own requirements. `Bits<n>` / `CBits<m>`
source experiments, staged Lean authority and the three future theorem pillars
must not appear as production APIs or completed guarantees.

## Distribution contents

Retain Cargo's default file selection for this release, with the repository's
ignore rules. Do not trim the archive solely to reduce its size. Review
`cargo package --list` and the actual compressed `.crate` for each candidate.

- Include Rust sources, all four `stdlib/src/*.qli` modules used by
  `include_str!`, the selected README, project documentation, examples, tests
  and applicable scripts. The executable embeds its ordinary standard library.
- Retain `LICENSE`, `NOTICE`, corpus provenance and all source-specific license
  and attribution files, including notices referenced by fixtures. Bundling
  third-party corpus material does not make it Qleisli-owned or dual-licensed.
- Lean sources and registries are development/proof artifacts in the archive;
  Cargo does not build or install a Lean checker. Python sources are included
  as source material; `cargo install` does not install a Python wheel.
- Cargo omits ignored build outputs and nested Rust packages. In particular,
  `research/semantic-kernel` is retained and tested in the complete Git source
  archive, and remains a non-published package. The `.crate` and complete source
  archive are different deliverables with separate inventories.

The [distribution checker](../scripts/check_distribution.py) binds both archives
to a **clean commit**, checks bytes/modes/provenance and package metadata, builds
API documentation without warnings, runs doctests, installs the extracted
package and exercises its quickstart outside the checkout. It also runs the
existing source archive Rust/research and provenance checks. A successful local
dirty-tree rehearsal is useful but does not satisfy that clean-commit gate.

## Prepare and validate without publishing

1. Review changes against shipped 0.2.0 public contracts. Keep compatible changes
   in 0.2.1 and the deferred heavy integration/proofs in 0.2.2. Retain the current
   `Unreleased` changelog and pending-publication wording until release selection
   is finalized. Check all project version metadata, including the Python host.
2. Build and execute the public documentation:

   ```sh
   RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --offline
   cargo test --doc --offline
   cargo fmt --check
   python3 scripts/test_check_docs.py
   python3 scripts/check_docs.py
   python3 scripts/test_check_distribution.py
   ```

3. Rehearse packaging and installation from the extracted artifact. The following
   POSIX-shell commands permit local uncommitted preparation and publish nothing:

   ```sh
   cargo package --list --allow-dirty --offline
   cargo package --allow-dirty --offline
   qleisli_release_dir="$(mktemp -d)"
   cargo install --path target/package/qleisli-0.2.1 --offline --locked \
     --bin qleisli --root "$qleisli_release_dir" \
     --target-dir "$qleisli_release_dir/build"
   python3 scripts/check_installation.py "$qleisli_release_dir/bin/qleisli" \
     --root target/package/qleisli-0.2.1
   ```

   `check_installation.py` runs in a temporary directory with no helper tools
   on the child's PATH. It checks the actual README Bell program, structured
   output and sampling, an ordinary embedded QFT module, and rejection of
   measured-owner reuse. It also checks README version agreement and registry
   link portability. On Windows, use the installed `qleisli.exe` path.

4. For the eventual release candidate, finish the full
   [release validation](versioning.md#release-records-and-validation): Rust
   primary/MSRV, Lean builds/audits, corpus/docs, interop and appropriate small
   examples. Preserve the user's small-system scope for remaining corpus work.
   After the intended changes are committed, run the clean distribution gate:

   ```sh
   python3 scripts/check_distribution.py --report /tmp/qleisli-0.2.1-distribution.json
   ```

   Choose a fresh report filename if one already exists. Inspect all CI jobs for
   that same commit, retaining artifact hashes and performed/skipped checks.
   This preparation turn does not run the clean gate against an older HEAD.

## Publication after explicit authorization

The user supplied release authorization on 2026-09-30. Finalize the 0.2.1
changelog/release date and remove temporary hold wording from both READMEs. Keep
the distinction between an authorized candidate and a confirmed registry
upload. Commit those final changes and validate that exact candidate; do not
publish the earlier dirty-tree rehearsal.

Confirm the crates.io account and package rights through the maintainer's normal
authenticated setup. Inspect the final `cargo publish --dry-run --locked` result,
then create the annotated `v0.2.1` tag on the verified commit. Push, hosted
release creation and `cargo publish --locked` are separate actions whose scope
must be authorized. Record actual outcomes; a failed upload is not publication.
Never overwrite a published version or move a published tag.

After successful upload, install the exact registry version in a fresh environment
and rerun the quickstart. Verify the crates.io README rendering/links and the
docs.rs build, recording their URLs and results. A local rustdoc build is not
evidence that the hosted docs.rs build succeeded. Preserve failures for follow-up;
any needed package correction takes a new version. PyPI distribution remains
separate from this Rust release.

Primary references: [Cargo publishing](https://doc.rust-lang.org/cargo/reference/publishing.html),
[package metadata and file selection](https://doc.rust-lang.org/cargo/reference/manifest.html),
and [docs.rs builds](https://docs.rs/about/builds).
