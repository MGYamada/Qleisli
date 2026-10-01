# Versioning and compatibility

Authoritative Cargo-compatible version policy, adopted 2026-09-28. [Cargo.toml](../Cargo.toml) selects the version; [release procedure](crates-io-release.md) governs publication. Historical releases use Git history and immutable tags.

## Version identity

Development 0.2.5 covers compatible refactoring, documentation reduction and finite corpus additions; latest published is 0.2.4. Synchronize Cargo/lockfile, both Lean lakefiles, Python metadata/__version__ and std Qargo version, never dependencies. Use MAJOR.MINOR.PATCH and annotated vMAJOR.MINOR.PATCH; synchronize prerelease suffixes. Accumulate Unreleased changes and do not bump per task. Product, edition, specification and ledger identifiers are separate. Narrow user exceptions retain their migration: 0.2.1 package/import identity to qleisli, and 0.2.3 explicit schema-2 edition manifests. They authorize no other incompatible PATCH.

## Choosing the next version

For 0.y.z, y>0, compatible fixes/features/deprecations use PATCH; breaks use MINOR and reset PATCH. In 0.0.z successive PATCH versions are incompatible. From 1.0 use SemVer. Combined changes take the largest required increment. New enum variants/required public fields/reserved valid identifiers may break even when other APIs are additive. V1 requires stabilized public contracts and its evidence gates.

| Change | 0.y.z, with y > 0 | From 1.0 onward |
| --- | --- | --- |
| Compatible bug fix, internal refactoring, documentation/proof clarification, or maintenance with unchanged public behavior and requirements | Increment PATCH, for example `0.1.0 -> 0.1.1`, when shipping another release. Documentation alone need not trigger a release. | Increment PATCH when released. |
| Backward-compatible public functionality, syntax addition, or deprecation without removal | Increment PATCH, for example `0.1.8 -> 0.1.9`; no feature exception is needed. | Increment MINOR and reset PATCH. |
| Breaking change to a supported public contract | Increment MINOR and reset PATCH; document migration. | Increment MAJOR and reset MINOR/PATCH; document migration. |

## What compatibility covers

Compatibility includes source syntax/resolution, Rust/IR/evidence, stdlib, CLI commands/exits/results and public Lean declarations; phase, axis/bit order, owners, effects, entry premises and cleanup are public semantics. Reduced capacities or raised toolchains require at least MINOR in 0.y.z. Rejecting already-invalid inputs can be PATCH only with the published violated rule, before/after behavior, diagnostic and regression. A new restriction/operator/API change cannot use that exception. Future breaking changes need an Issue naming 0.x.0, contracts/reason/migration and validation; no duplicate backlog.

## Release records and validation

Validate exact candidate norms/conformance, fmt/all-target tests/Clippy/doctest/API docs, docs and examples, research checks where shipped, pinned Lean builds/axiom/runtime/compiled audits and independent native comparisons, and package notices/distribution. Record skipped checks honestly; documentation-only work need not rerun Rust/Lean. Tag the exact clean checked release commit, never an older HEAD with uncommitted implementation. Published tags/artifacts are immutable; corrections require another version. Selection, checks, tag, push, registry/hosted publication and PyPI/platform binaries are distinct actions within user authorization.
