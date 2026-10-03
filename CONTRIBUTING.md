# Contributing to Qleisli

Read [AGENTS.md](AGENTS.md) before changing the repository. It records the
design-first workflow, quantum safety requirements, specification languages,
and required validation. The public compatibility and release policy is in
[Versioning](https://github.com/MGYamada/Qleisli/blob/v0.2.7/docs/versioning.md).

## License of contributions

Unless a file explicitly states otherwise, Qleisli's own source code,
standard library, examples, tests, scripts, Lean proofs, and documentation are
licensed under the [Apache License, Version 2.0](LICENSE). See [NOTICE](NOTICE)
for the project attribution.

By intentionally submitting a contribution for inclusion, you provide it
under Apache-2.0, as described in section 5 of that license, unless the file
explicitly has different terms. Contributions to MIT-licensed QuantumKatas
translations remain MIT. Follow the closed three-source [corpus policy](corpus/POLICY.md);
do not add or replace an input source without an explicit user-approved amendment.
Contribute only
material that you have the right to submit under those terms. Contributors
retain their copyright; this policy does not require an assignment of ownership.

Preserve existing copyright, license, and attribution notices. Identify the
origin and license of any third-party material added to the repository, keep
its required notices, and review compatibility before incorporating it.
Dependencies and corpus inputs retain their own licenses. Do not relabel third-party material
as Qleisli-owned code.

Human-written and AI-assisted contributions follow the same review and
verification requirements. An explanation, author identity, or generation
method is not a certificate of quantum correctness or permission to reuse
third-party material.

## Tracking issues

When creating a GitHub Issue, a local backlog entry is unnecessary. An existing
GitHub Issue also suffices: no duplicate entry, backlog update or A020 ID is
required. Use the Issue to track the problem, relevant evidence, acceptance
criteria and resolution. The legacy backlog is retired; use Issues for new work.

## Documentation cleanup

Follow **docs/ cleanup boundary at v0.3.0** in
[AGENTS.md](AGENTS.md#docs-cleanup-boundary-at-v030). Delete obsolete documents
actively, while retaining the active v0.2.x goals and migration plan. Retire the
remaining legacy files by v0.3.0 and write the new documentation from scratch;
do not migrate or archive the old tree.

## Recording changes

Record user-visible changes under `Unreleased` in [CHANGELOG.md](CHANGELOG.md).
Explain compatibility effects, including source syntax, public Rust APIs,
quantum meaning, and supported limits. Changes to normative behavior must
update the English specification and relevant acceptance/rejection evidence
in the same change.

Run the checks appropriate to the affected files and record actual results.
CI validates PRs once, cancels superseded ordinary PR runs and keeps the existing
required check names. [Input profiles](.github/ci/profiles.json) permit only listed
descriptive documents/result records to use the docs path; specifications,
protected/unknown inputs, missing diffs, tags and manual runs require full checks.
Every required context rejects missing/failed selected suites. Cargo caches contain
dependency archives only; project binaries/Lean definitions are rebuilt, audited
and freshly replayed. This selection policy does not adopt the future constitutional
registry in Issue #141. Use `python3 scripts/test_ci_profiles.py` locally.
For release preparation, use the complete checklist in
[Versioning](https://github.com/MGYamada/Qleisli/blob/v0.2.7/docs/versioning.md#release-records-and-validation). Distinguish
paper arguments, finite tests, Lean results, and remaining proof obligations.
The [crates.io procedure](https://github.com/MGYamada/Qleisli/blob/v0.2.7/docs/crates-io-release.md) covers the registry README,
API doctests, installed quickstart and archive inventories. Local release
preparation alone does not authorize an upload; the 0.2.1 upload was separately
authorized by the user on 2026-09-30, subject to rechecking.

## Executable verification kernel

The [Lean migration](docs/lean-kernel-migration.md) keeps the Rust frontend and
moves acceptance logic in bounded, proved steps to [lean-kernel](lean-kernel/README.md).
That executable package depends on Lean 4.30.0 Init/Std only; Mathlib remains in
the separate proof/model package. Follow the package's build, compiled audit,
proof replay and native differential checks when changing its code. Development
Python checks require Python 3.11 or later; Rust's minimum remains 1.85.0.
Record the actual theorem scope and residual native/transport assumptions.

## Community development from v0.5

Qleisli currently develops through an individual-led effort with public source
and checks. The [adopted roadmap](docs/v0x-roadmap.md#community-development-from-v05)
plans broader community development from v0.5 onward, anchored in the
[Qleisli Soundness Theorem](docs/release-milestones.md#qleisli-soundness-theorem-v050).
Contributions and review can begin before that milestone.

During 0.4.x, prepare reproducible contributor setup, bounded issues, proof/code
review requirements, maintainer responsibilities and release/security reporting
procedures. At v0.5.0, publish the theorem, its coverage and assumptions, review
results and reproduction commands. Thereafter expand participation in the
kernel, source tooling, algorithms, examples and documentation through those
processes. These are planned deliverables; no additional maintainer roles or
completed external reviews are claimed. Existing licensing and corpus policy
continue to apply.

## Standard-library contributions

Until v0.5.0, do not expand `stdlib` as a general rule; add algorithms to
`corpus` under its existing source/license policy. From v0.5.0, grow the library
as a mathlib-style open-source effort with shared mathematical conventions and
reviewed contributions. Read [STDLIB.md](STDLIB.md), start from its
[contract template](docs/stdlib-contract-template.md), and compare the
[three filled contracts](STDLIB.md#template-and-reference-implementations)
with their actual source and existing evidence.

Specify the meaning/phase, encoding, owner transitions, entry/access premises,
scratch return, approximation and resource model before selecting an optimized
implementation. Show source checks, semantic tests, actual-IR proofs, source
preservation and specification review as distinct scoped results. Keep general
borrow syntax and final parameterized APIs in the language specification process.
The initial `check_stdlib_contract_docs.py` CI step checks documentation form
and links only; planned `qlippy` tooling issues no semantic acceptance evidence.
Follow the existing reuse/adoption and compatibility rules rather than treating
corpus frequency or a successful linter as standard adoption.
