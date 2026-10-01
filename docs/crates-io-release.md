# Qleisli release procedure

Reusable procedure illustrated with published 0.2.4; substitute the selected candidate consistently. [Latest publication](https://github.com/MGYamada/Qleisli/blob/7bfcd36916199b05d5ab11851d38d53375ccf71e/docs/releases/v0.2.4.md#successful-publication-2026-10-01) has immutable evidence; development 0.2.5 is unpublished. Cargo selects the version; [versioning](versioning.md) and feature/proof gates govern release. Ship edition 2026 manifests, full std qrate and checked quickstarts.

## Release sequence

Complete each step separately with the evidence below. Read all applicable [CI jobs](../.github/workflows/ci.yml) for the exact final source, not an earlier commit. CI does not publish. Rust package, full GitHub source and docs.rs are separate outcomes; PyPI/platform binaries require separate preparation/publication.

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

## Package identity and user documentation

Names below were adopted before first upload. Cargo supplies version/MSRV/license/repository/docs/description/categories. Confirm actual registry publisher rights at release time. qargo/qlidoc remain possible future tools, not implemented or reserved packages.

| Surface | Name or entry point |
| --- | --- |
| crates.io package | `qleisli` |
| Installed command | `qleisli` |
| Rust import | `qleisli` |
| Registry landing page | [README.crates.md](../README.crates.md), selected by `package.readme` |
| Project introduction and theorem goals | [README.md](../README.md) |
| Rust API documentation | [src/lib.rs](../src/lib.rs); docs.rs after publication/build |
| Optional Python host | [python/README.md](../python/README.md); separately installed |

## Name migration from GitHub releases through 0.2.0

Explicit 0.2.1 identity exception replaces qleisli-core/qleisli_core for Git/path consumers; no other PATCH break is authorized. New import is qleisli; keep old spelling temporarily with the alias below (path instead of version before upload). CLI/source/evidence/Python identity remains. Historical names remain in old artifacts; type-system breaks target 0.3.

```toml
[dependencies]
qleisli = "0.2.1"
```

```toml
[dependencies]
qleisli_core = { package = "qleisli", version = "0.2.1" }
```

## README presentation

Repository/registry examples must agree and execute. Registry README uses HTTPS/ordinary Markdown, links pinned to candidate tag; label development install/tag links pending. Push verified source tag and check live links before upload. Ordinary Rust use needs no Lean/Python/LLVM; host/QIR requirements, sized experiments, staged authority and future theorem goals have explicit separate status.

## Distribution contents

Use default Cargo selection/ignores; review actual list/compressed crate, never trim solely for size. Include Rust, four embedded ordinary std modules, README/docs/examples/tests/scripts and LICENSE/NOTICE/all third-party provenance. Lean/Python are source artifacts, not installed by Cargo; nested nonpublished research package belongs in full Git source, not crate. [Distribution checker](../scripts/check_distribution.py) binds clean-commit bytes/modes/metadata/provenance, warning-free docs/doctest, extracted install/quickstart and source archive Rust/research checks. Dirty rehearsal is not that clean gate.

## Prepare and validate without publishing

Review shipped contracts and feature dispositions; synchronize project manifests/runtime/lockfile, never dependency versions. Keep Unreleased/development until final candidate, use --locked. Manifest changes refresh registry via actual build/audit/type review, preserving IDs/domains/types/disabled schemas. Full checks include Rust primary/MSRV/fmt/Clippy/docs/doctest, pinned Lean audits/native comparisons, corpus/editions/contracts/interop and small examples. No newly generated maximum-size corpus is required; other gates remain.

Rehearsal commands below publish nothing. Installation checker uses empty helper PATH for Bell/JSON/sample/QFT/reuse rejection and README/link agreement; Windows uses qleisli.exe. Commit all intended changes before clean distribution, choose fresh report names and record same-commit CI/artifact identities and performed/skipped checks.

   ```sh
   python3 scripts/check_schema_registry.py --write
   python3 scripts/check_docs.py --write-status
   ```

   ```sh
   RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --offline
   cargo test --doc --offline
   cargo fmt --check
   python3 scripts/test_check_docs.py
   python3 scripts/check_docs.py
   python3 scripts/test_check_distribution.py
   ```

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

   ```sh
   python3 scripts/check_distribution.py --report /tmp/qleisli-0.2.4-distribution.json
   ```

## Final candidate and publication

Finalize scope, dated changelog, reviewed notes and install links; commit complete candidate and validate exact tree. Later source changes need revalidation. Verify authenticated account/package rights/dry run; clean HEAD must equal checked commit. Tag/push/upload/GitHub creation follow the current authorized request, earlier publication requests are historical.

Read back local/remote annotation and peeled commit and live pinned links before upload. Account/network failure is no publication: save diagnostics, resolve and retry same source. Published tags/artifacts immutable; source correction needs new version. Fresh exact registry install in separate Cargo/install/target roots runs shipped installation checker. Compare downloaded crate hash/VCS/dirty flag, actual README/links and hosted docs.rs build; local rustdoc proves no hosted success.

Save reviewed notes to the shown file before creating GitHub Release. Read back title/body/tag/status/Latest and compare complete tar.gz/ZIP bytes/inventory/modes to tag. Archive container hashes are observations because GitHub may regenerate them. No custom binaries currently. Later result commit preserves tagged identity; PyPI separate.

Primary references: [Cargo publishing](https://doc.rust-lang.org/cargo/reference/publishing.html), [manifest/files](https://doc.rust-lang.org/cargo/reference/manifest.html), [GitHub Releases](https://docs.github.com/en/repositories/releasing-projects-on-github/managing-releases-in-a-repository), [docs.rs](https://docs.rs/about/builds).

```sh
git status --short
git rev-parse HEAD
cargo publish --dry-run --locked --registry crates-io
```

```sh
git tag -a v0.2.4 -m "Qleisli v0.2.4"
git show --no-patch v0.2.4
git push origin refs/tags/v0.2.4
git ls-remote origin refs/tags/v0.2.4 'refs/tags/v0.2.4^{}'
```

```sh
cargo publish --locked --registry crates-io
```

```sh
qleisli_registry_dir="$(mktemp -d)"
CARGO_HOME="$qleisli_registry_dir/cargo" \
  cargo install qleisli --version '=0.2.4' --locked --registry crates-io \
  --root "$qleisli_registry_dir/install" \
  --target-dir "$qleisli_registry_dir/build"
```

```sh
gh release create v0.2.4 --repo MGYamada/Qleisli --verify-tag \
  --title "Qleisli v0.2.4" --notes-file /tmp/qleisli-0.2.4-release-notes.md
```
