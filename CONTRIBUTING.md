# Contributing to Qleisli

Read [AGENTS.md](AGENTS.md) before changing the repository. It records the
design-first workflow, quantum safety requirements, specification languages,
and required validation. The public compatibility and release policy is in
[Versioning](docs/versioning.md).

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

## Recording changes

Record user-visible changes under `Unreleased` in [CHANGELOG.md](CHANGELOG.md).
Explain compatibility effects, including source syntax, public Rust APIs,
quantum meaning, and supported limits. Changes to normative behavior must
update the English specification and relevant acceptance/rejection evidence
in the same change.

Run the checks appropriate to the affected files and record actual results.
For release preparation, use the complete checklist in
[Versioning](docs/versioning.md#release-records-and-validation). Distinguish
paper arguments, finite tests, Lean results, and remaining proof obligations.

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
