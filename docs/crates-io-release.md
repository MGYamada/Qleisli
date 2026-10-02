<a id="name-migration-from-github-releases-through-020"></a>

# Qleisli release procedure

Cargo/version synchronization under [versioning](versioning.md); [theorem gates](release-milestones.md) separate. Selected0.2.7 unpublished/latest [0.2.6 evidence](../tests/fixtures/releases/v0.2.6/publication.json). Publication requires current authorization.

## Release sequence
1. Select manifests/Unreleased/status/candidate,not publication.
2. Review compatibility/dispositions/notes/date;clean candidate commit.
3. Check exact commit/applicable local+CI+clean distribution identity.
4. Annotated tag exact checked commit,push/read back annotation+peeled commit/live pinned links.
5. Publish Rust/read back downloaded crate/hash/VCS/registry version.
6. Fresh isolated exact-version registry install/shipped quickstart/README links/docs.rs actual build.
7. GitHub Release existing verified tag/notes/title/body/Latest/readback; complete source tar+ZIP bytes/modes/inventories. No custom binaries/PyPI without separate preparation.
8. Retain commands/exits/logs/hashes/dates/skips/failures/URLs. Published artifacts immutable; changed source revalidate/new version.

The [CI selection record](../.github/ci/README.md) must show `proof_lane=full`
for the exact release candidate. `profile=full` only means all suites were
selected; a routine `proof_lane=tests` result is not full release proof validation.

## Package identity and user documentation
qleisli executable/package/import,Apache-2.0/Cargo metadata/MSRV/publisher rights. README.crates/project README/src API quickstarts agree/execute; pending tag/install links explicit. Rust no Lean/Python/LLVM,optional requirements explicit;qargo/qlidoc future. 0.2.1 sole identity exception qleisli-core/qleisli_core->qleisli; alias qleisli_core={package="qleisli",version="0.2.1"},historical identities frozen.

## Distribution contents
Review Cargo default selection/list/compressed crate,not size-only pruning. Preserve Rust/std/docs/examples/tests/scripts/LICENSE/NOTICE/corpus provenance/edition2026/notices. Lean/Python source not Cargo installation; nested research excluded crate/included Git archives.

## Prepare and validate without publishing
Applicable fmt/tests/Clippy/doctests/warning-free docs/MSRV/corpus/editions/contracts/interop/research/pinned Lean builds+source/compiled audits/native comparisons. No new maximum cases. Metadata changes preserve registry IDs/domains/disabled schemas; check_docs --write-status/schema registry --write when applicable,accurate skips.

cargo package --list --allow-dirty --offline and publish --dry-run --locked are rehearsals,not clean gates. [Distribution checker](../scripts/check_distribution.py) fresh external report rejects dirty/staged/untracked candidates,binds clean HEAD bytes/modes/regular-file inventory to safe complete source+crate archives before extraction; exact manifest/generated Cargo exceptions/metadata/install/quickstart/archived Rust+research tests/clean recheck. [Installation](../scripts/check_installation.py) extracted offline locked install. Mutation tests/dirty rehearsal not exact CI/hosted publication/cross-host reproducibility; gate does not publish/rerun all MSRV+Lean.

## Final candidate and publication
Commit intended files before exact checks; only clean checked HEAD/tag publish. Network/account failure retain diagnostics/retry same source; fresh registry/Cargo/target roots and artifact comparisons. Save multiline notes/gh --notes-file. Evidence may later commit,tag/artifacts immutable. [Cargo](https://doc.rust-lang.org/cargo/reference/publishing.html)/[GitHub](https://docs.github.com/en/repositories/releasing-projects-on-github/managing-releases-in-a-repository)/[docs.rs](https://docs.rs/about/builds).
