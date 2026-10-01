# Qleisli release procedure

Status: **0.2.4 published and verified on 2026-10-01**.
The latest completed publication is [0.2.4](releases/v0.2.4.md#successful-publication-2026-10-01).
This reusable procedure illustrates the sequence with 0.2.4; actual outcomes
belong in its [release record](releases/v0.2.4.md). Versioning and proof/feature
gates remain authoritative.

The release retains Qleisli edition 2026 and the explicit source-tree manifests
introduced in 0.2.3. Package the full std qrate manifest and check the shipped
quickstarts. A version or this procedure alone does not perform publication.

## Release sequence

| Step | Completion evidence |
| --- | --- |
| Select development version | Synchronized manifests/runtime version, `Unreleased` changelog, current status and a release record; no publication claim. |
| Finalize candidate | Compatibility and feature-gate dispositions, release notes/date, a clean commit containing all intended release changes. |
| Validate exact commit | Required local checks, every applicable CI job and clean distribution report with commit and artifact hashes. |
| Tag and push source | Annotated `v0.2.4` tag on that verified commit and remote readback; version-pinned README links become available. |
| Publish Rust package | Successful `cargo publish`, registry availability and matching downloaded `.crate` identity. |
| Verify installed package/docs | Fresh exact-version registry installation, shipped quickstart, rendered registry README and actual docs.rs build. |
| Publish GitHub Release | Release on the existing verified tag, prepared notes and verified complete source downloads. |
| Record results | Dates, URLs, commit/tag identities, artifact hashes, performed/skipped checks and any failures, without moving the published tag. |

The current [CI workflow](../.github/workflows/ci.yml) validates Rust, MSRV,
interop, Lean proofs, the Lean kernel, distribution and documentation in seven
jobs. It does not automatically upload to crates.io or create a GitHub Release.
Read all job outcomes for the exact final source commit; a passing earlier
commit or pull-request merge preview does not validate a changed release tree.
PyPI and any future platform binaries have separate preparation and publication
steps. Cargo distributes the Rust CLI/library, GitHub provides complete tagged
source, and docs.rs builds the Rust API documentation.

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
pinned to the selected candidate tag, matching the packaged source. During
development, explicitly label registry installation and tag links as pending.
The repository README can additionally offer the latest published version.
Local target
checking does not establish that links are live before the verified source tag
is pushed; publish that tag before uploading the registry artifact.

Document ordinary Rust CLI/library use without Lean, Python or LLVM. Python
hosting and optional QIR input have their own requirements. `Bits<n>` / `CBits<m>`
source experiments, staged Lean authority and the three future theorem pillars
must not appear as production APIs or completed guarantees.

## Distribution contents

Retain Cargo's default file selection, with the repository's
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

1. Review changes against the latest shipped public contracts. For 0.2.4,
   compare with 0.2.3 and preserve its published contracts; a necessary public
   break selects 0.3.0. The earlier edition exception does not authorize another break. Resolve the
   [0.2.2 feature gates](v0.2.2-plan.md) for the selected release scope explicitly;
   a metadata bump cannot mark shared QPE or H1–H5 complete. Retain `Unreleased`
   and development wording until the final candidate is selected. Synchronize
   `Cargo.toml`, `Cargo.lock`, both Lean package manifests, `python/pyproject.toml`
   and Python `__version__`; do not change dependency versions. Refresh the
   local lockfile after changing version metadata. The root `Cargo.lock` is tracked from 0.2.4 at the user's request.
   Keep the reviewed dependency resolution fixed with `--locked`; the
   distribution checker also validates the generated package lockfile. After changing Lean manifests, refresh the source-bound
   registry through its normal build
   and audit path:

   ```sh
   python3 scripts/check_schema_registry.py --write
   python3 scripts/check_docs.py --write-status
   ```

   Keep all external schema entries disabled until their own binding gates pass.
   Review the registry diff; a manifest-only change must preserve theorem types,
   parameters and enablement. Update current summaries and the matching release
   record without rewriting past validation or publication records.
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
   cargo install --path target/package/qleisli-0.2.4 --offline --locked \
     --bin qleisli --root "$qleisli_release_dir" \
     --target-dir "$qleisli_release_dir/build"
   python3 scripts/check_installation.py "$qleisli_release_dir/bin/qleisli" \
     --root target/package/qleisli-0.2.4
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
   python3 scripts/check_distribution.py --report /tmp/qleisli-0.2.4-distribution.json
   ```

   Choose a fresh report filename if one already exists. Inspect all CI jobs for
   that same commit, retaining artifact hashes and performed/skipped checks.
   Do not run the clean gate against an older HEAD while intended release
   changes remain uncommitted. The small-system corpus scope does not waive
   ownership, exact phase/reference, compatibility, proof/audit or distribution
   checks; newly generating maximum-size corpus cases is not a release prerequisite.

## Final candidate and publication

First finalize release scope, move completed `Unreleased` changes into a dated
0.2.4 changelog entry, and prepare standalone release notes. State supported
contracts, migrations, proof coverage and remaining limitations. Finalize
candidate installation examples and version-pinned links while still recording
publication as pending. Commit the final tree and run the full checks and clean
distribution gate above on it. Any subsequent source change requires validation
of the changed candidate before tagging.

Confirm the crates.io account and package rights through the maintainer's normal
authenticated setup, including verified email. Inspect the final dry run from
the clean candidate:

```sh
git status --short
git rev-parse HEAD
cargo publish --dry-run --locked --registry crates-io
```

The worktree must be clean and HEAD must equal the validated source commit.
Once the publication operations are within the user's authorized scope, tag
that commit and push the tag:

```sh
git tag -a v0.2.4 -m "Qleisli v0.2.4"
git show --no-patch v0.2.4
git push origin refs/tags/v0.2.4
git ls-remote origin refs/tags/v0.2.4 'refs/tags/v0.2.4^{}'
```

Verify the annotation and peeled commit locally and remotely. Open the
version-pinned documentation links before uploading. Publish from the same
clean source checkout, outside the sandbox when required by the authorized
release request:

```sh
cargo publish --locked --registry crates-io
```

Tag creation, tag push, Rust upload and GitHub publication are separate actions.
Earlier release authorizations/results are historical; record the current
request's preparation or publication scope explicitly.
Record each outcome; a failed upload is not publication. For account/network
failures, preserve diagnostics and retry the same immutable source after
resolving the cause. A source correction after tag publication requires a new
version and validated candidate; never move a published tag or overwrite a
registry artifact.

After successful upload, install the exact registry version in a fresh environment
and rerun the quickstart. With a new empty installation root, Cargo home and
target directory, run:

```sh
qleisli_registry_dir="$(mktemp -d)"
CARGO_HOME="$qleisli_registry_dir/cargo" \
  cargo install qleisli --version '=0.2.4' --locked --registry crates-io \
  --root "$qleisli_registry_dir/install" \
  --target-dir "$qleisli_registry_dir/build"
```

Run the `scripts/check_installation.py` shipped in the downloaded crate against
the installed executable and extracted crate root. Compare the downloaded
`.crate` SHA-256 and retained VCS commit/dirty flag with the validated candidate.
Verify the crates.io README rendering/links and the
docs.rs build, recording their URLs and results. A local rustdoc build is not
evidence that the hosted docs.rs build succeeded. Preserve failures for follow-up;
any needed package correction takes a new version.

Then create the GitHub Release on the already pushed tag. Save the reviewed
Markdown notes in `/tmp/qleisli-0.2.4-release-notes.md` before running:

```sh
gh release create v0.2.4 --repo MGYamada/Qleisli --verify-tag \
  --title "Qleisli v0.2.4" --notes-file /tmp/qleisli-0.2.4-release-notes.md
```

Read back the actual release title, body, tag, published/prerelease status and
Latest selection. Download GitHub's tag tar.gz and ZIP and compare their
complete file inventories and bytes with the tag; check executable modes where
the archive format preserves them. Record observed download hashes separately
from tagged content identity, since GitHub may regenerate archive containers.
Custom binary assets are not part of the current distribution method.

Save publication evidence in a later result-record commit if necessary. That
commit does not replace the immutable tagged source or registry package. PyPI
distribution remains separate from this Rust release.

Primary references: [Cargo publishing](https://doc.rust-lang.org/cargo/reference/publishing.html),
[package metadata and file selection](https://doc.rust-lang.org/cargo/reference/manifest.html),
[GitHub Release management](https://docs.github.com/en/repositories/releasing-projects-on-github/managing-releases-in-a-repository)
and [docs.rs builds](https://docs.rs/about/builds).
