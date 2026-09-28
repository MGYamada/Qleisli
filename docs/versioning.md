# Versioning and compatibility

Status: **adopted project policy, revised at the user's request on 2026-09-28**.
This is the authoritative English policy. The repository working rules in
[AGENTS.md](../AGENTS.md) summarize it. The project uses the version format
and release immutability rules of [Semantic Versioning 2.0.0](https://semver.org/spec/v2.0.0.html),
with Cargo-compatible initial-development version selection below. This
supersedes the 2026-09-27 rule requiring MINOR for every new feature.

## Version identity

Compatible feature additions no longer need a version-policy exception.
The previous 0.1.6/0.1.7 decisions and then-untagged 0.1.8 checkpoint retain their
historical numbers and migration records; dated exception statements describe the former
policy, not a continuing requirement. This revision does not reclassify their
documented source/API breaks as compatible or authorize future incompatible
PATCH releases. See the [0.1.6](releases/v0.1.6.md),
[0.1.7](releases/v0.1.7.md) and [0.1.8](releases/v0.1.8.md) records.

The selected baseline and release state are in [current status](current-status.md)
and the [0.1.8 implementation record](releases/v0.1.8.md). The user explicitly
retained development version 0.1.8 for the authoring continuation after its
temporary 0.2.0 selection. The public Rust `Param.name` → `Param.pattern`
migration remains incompatible and documented; the general compatibility
policy below is unchanged. Version selection alone
does not establish publication. [M0–M5](v0x-roadmap.md) schedule development
independently of version numbers; no theme reserves a MINOR number. Continuous
audits need no PATCH unless a useful compatible change is being released.
The legacy B019 finite maintenance checkpoint is not a requirement to ship
patches 6–9 first, and later maintenance may use 0.1.10.
[Cargo.toml](../Cargo.toml)'s
`package.version` is the source of truth. Keep the project's own package
version in [lean/lakefile.toml](../lean/lakefile.toml) synchronized. Compiler,
bundled standard library, examples, and proof development currently share
one release version; this does not imply that their verification is complete.

Manifests use `MAJOR.MINOR.PATCH`, without a leading `v`; release tags use
`vMAJOR.MINOR.PATCH`. A prerelease, when needed, uses an explicit suffix such
as `0.2.0-rc.1`, synchronized in both manifests and its tag. The current
release number is not changed merely because a task, commit, or test run
finishes. Accumulate pending changes under `Unreleased` in the changelog;
update the number when selecting the next release or prerelease.

The finite-core specification's `v0`, standard-library ledger's format `v1`,
development stages, and product release numbers are separate identifiers.
Do not rename historical specification files or rewrite old validation
records when bumping a package version. [Release milestones](release-milestones.md)
provide evidence gates: a manifest number alone does not satisfy them.

## Choosing the next version

For `0.y.z` with `y > 0`, Qleisli follows
[Cargo's compatibility convention](https://doc.rust-lang.org/cargo/reference/semver.html#change-categories):
`y` identifies the incompatible release line and `z` may include compatible
features as well as fixes. In the table, MINOR and PATCH name the numeric
positions, not the size or importance of the work.

| Change | 0.y.z, with y > 0 | From 1.0 onward |
| --- | --- | --- |
| Compatible bug fix, internal refactoring, documentation/proof clarification, or maintenance with unchanged public behavior and requirements | Increment PATCH, for example `0.1.0 -> 0.1.1`, when shipping another release. Documentation alone need not trigger a release. | Increment PATCH when released. |
| Backward-compatible public functionality, syntax addition, or deprecation without removal | Increment PATCH, for example `0.1.8 -> 0.1.9`; no feature exception is needed. | Increment MINOR and reset PATCH. |
| Breaking change to a supported public contract | Increment MINOR and reset PATCH; document migration. | Increment MAJOR and reset MINOR/PATCH; document migration. |

For `0.0.z`, Cargo treats successive PATCH versions as incompatible; that is
not the project's current release line. If a release contains several kinds
of change, use the largest required bump. An additive feature can still break
compatibility: reserving a previously valid identifier, adding a variant to an
exhaustive public enum, or adding a required field to a publicly constructible
struct requires MINOR in 0.y.z with y > 0. Classify the whole public change, not only
its new CLI or source entry point. Specification, evidence and validation
requirements apply equally to compatible features shipped in PATCH releases.

Before starting `0.2.0` feature implementation or releasing `0.2.0` (including
its prereleases), complete the
[imaginary Qleisli 1.0 code prerequisite](release-milestones.md#pre-v020-imaginary-v1-code).
The initial algorithm drafts may be noncompiling; their existence and recorded
semantic requirements must precede the implementation they guide. Adopting
this policy does not itself complete the prerequisite or bump the version.

`1.0.0` requires the [V1-C1–C5 acceptance evidence](release-milestones.md#v1-acceptance-target-textbook-algorithm-structure)
and a documented stable public contract. The current fixed-size examples,
elapsed development time, or completion of a 0.x feature do not establish
that threshold.

## What compatibility covers

The public surface includes the documented `.qli` grammar and name resolution,
sealed and standard-library APIs, public Rust items including raw IR and
evidence APIs, CLI commands and exit-status/result conventions, and exported
Lean declarations. A mathematical contract's phase, bit/axis order, output
layout, ownership, effect, and entry/cleanup premises are behavior, not
implementation details. A change to them requires the same compatibility
review as a signature change.

Record changes to implementation limits and supported Rust/Lean toolchains.
Reducing supported capacity or raising a toolchain requirement uses at least
a MINOR bump in 0.y.z with y > 0; after 1.0, apply the declared stable support contract.
Exact human-readable diagnostic wording and internal file layout are not
stable interfaces, but public error-code variants remain public Rust API.
No stable serialized IR or certificate format is promised by the 0.1.x line.
M1 interchange, JSON diagnostics and sampling may use PATCH when the complete
change is compatible; they do not require MINOR merely because they add
functionality. A new source-file byte limit reduces
accepted capacity and also requires a MINOR decision; it is not a patch fix
without an already published violated limit. Hierarchical IR changes require
explicit Rust API and format migration, including exhaustive enum matches.

Rejecting a program or certificate that violated the already published
specification is a correctness fix and may ship in a patch. Document the
previously erroneous acceptance, the violated rule, the new diagnostic, and
regression evidence. Restoring an implementation's promised operator likewise
requires explicit before/after evidence. This exception does not allow a
new restriction on previously valid programs, a different promised operator,
or an incompatible public Rust API change to be hidden in a patch.

## Release records and validation

For `0.2.0` and its prereleases, first verify that the conformance ledger links
the completed initial imaginary-code corpus and its requirement records.

For each release or prerelease:

1. Select the version from the compatibility review. Synchronize both project
   manifests and the changelog; update current-version summaries and links.
2. Record added/changed/fixed behavior, breaking changes and migration,
   supported bounds/toolchains, license or dependency changes, and relevant
   specification/conformance references. Keep past release entries intact.
3. Validate the release tree with `cargo fmt --check`,
   `cargo test --all-targets`, `cargo clippy --all-targets -- -D warnings`,
   `python3 scripts/test_check_docs.py`, `python3 scripts/check_docs.py`,
   `python3 scripts/test_check_imaginary_v1_examples.py`,
   `python3 scripts/check_imaginary_v1_examples.py`,
   `python3 scripts/test_check_semantic_contract_examples.py`,
   `python3 scripts/check_semantic_contract_examples.py`, and
   `git diff --check`. Check package metadata and that distributable archives
   include the required license/attribution files. Run documented release
   examples. Record platform exclusions and any skipped check explicitly.
   While the independent semantic research package is in the release tree,
   also run its documented [fmt, all-target tests and Clippy](../research/semantic-kernel/README.md#reproduction)
   on the primary and minimum Rust toolchains (format with the primary
   formatter). Distinguish the production `.crate` from the complete repository
   source archive: Cargo excludes nested packages, including this non-published
   prototype, from the production package.
4. Build and audit the Lean development using the pinned toolchain:
   `lake build Qleisli` and
   `lake env lean -DwarningAsError=true Audit.lean` from `lean/`.
   Physlib is currently a [future dependency](physlib-environment.md), not a
   release prerequisite. If reintroduced for a concrete bridge, add its scoped
   external build/axiom audit separately and document the declarations covered.
   This is a full release check; a documentation-only working change
   need not rerun Lean or claim that it did.
5. Tag the exact checked commit with an annotated `vMAJOR.MINOR.PATCH` tag
   (including a prerelease suffix if present). Never tag an older HEAD while
   the release's implementation remains only in a dirty worktree. Include
   the version, commit identity, verification scope, and known limitations in
   the release record. Published tags and release artifacts are immutable;
   corrections require a new version.

Changing a manifest or designating a baseline is distinct from creating a
Git tag, pushing it, creating a hosted release, or publishing a package.
Report which steps actually happened; do not infer publication from a file
version or a completed development goal. Publication operations follow the
scope of the user's release request.
