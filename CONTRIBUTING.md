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
under Apache-2.0, as described in section 5 of that license. Contribute only
material that you have the right to submit under those terms. Contributors
retain their copyright; this policy does not require an assignment of ownership.

Preserve existing copyright, license, and attribution notices. Identify the
origin and license of any third-party material added to the repository, keep
its required notices, and review compatibility before incorporating it.
Dependencies retain their own licenses. Do not relabel third-party material
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
