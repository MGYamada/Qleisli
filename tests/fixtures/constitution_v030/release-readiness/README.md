# Scoped release gate implementation experiment (#142)

This fixture records release-tooling checks, not a release candidate, human
approval, complete Issue acceptance index, new guarantee or publication.
The [recorded implementation contract](contract.md) was fetched from Issue #142
before implementation. `before.json` and its untouched stdout/stderr files
capture the actual original CLI: ordinary constitutional identity validation
passed, while `--require-release-ready` rejected unconditionally and referred
to the three broader pending obligations.

The new gate instead requires a caller-trusted requirements snapshot and
same-run hosted producer context. No actual `release/requirements.json` or
`release/acceptance.json` was added: the real 108-Issue work remains incomplete
and GitHub remains its only decisions/progress ledger. Both CLI entry points
reject missing required context with a concrete diagnostic.

## Synthetic positive and actual verification boundaries

`python3 scripts/test_check_release_ready.py` generates disposable Git
repositories with the exact 13-group/108-ID shape, one explicitly synthetic
criterion per Issue, small synthetic archives, two scoped-guarantee IDs and
three broader pending IDs. Nothing in that synthetic criterion list asserts
that the real Issues have only one criterion or are complete. The full
positive path exercises actual Git identity, exact coverage, snapshot/hash
validation, same-run receipt matching and archive readers. Its constitutional
and version-validation service results, build receipts, native executable
contents, hosted environment and human review are **simulated**. It neither
runs Lean nor authenticates GitHub or a human transcript.

Separate subprocess tests invoke the real new CLI producer and rejection
paths, and the existing constitutional CLI's release delegation. Fixed live
verifier invocation and input-change rejection are tested through its actual
wrapper API. The existing constitutional test suite continues to validate the
real archived ratification/admission records and mutable current-evidence
checks. Those tests are not new human judgments or a hosted release rehearsal.

Real proof maintenance predating the new receipt wrapper is retained in
[the routed-control checkpoint](../routed-control-commutation/README.md),
including its official registry/build/audit/fresh-replay record. That earlier
Lean validation must not be relabelled as validation of this new wrapper or of
a complete synthetic release. A real wrapper run on a clean staged candidate
and future hosted readiness run are separate integration evidence.

## Validation records

`validation.json` records exact local commands, exit codes, elapsed times and
untouched raw outputs in `validation/`. Its ordinary constitutional invocation
checks source/evidence identity only. The successful unit suites do not imply
that full release CI or publication has run. No maximum-size quantum cases or
Rust/Lean runtime acceptance rules were changed.

The final gate suite has **22 passing tests**, including the added rejection of
ignored candidate evidence absent from the exact Git commit. Its complete
before/after code hashes and raw output are in
`tracked-reference-validation.json`. The existing constitutional and CI-routing
suites passed **54 and six tests** respectively. Both real CLI missing-context
cases exited 1 as intended; ordinary constitutional validation, documentation
and whitespace checks passed. `source-identity.json` identifies the final owned
files and actual Python runtime, distinguishes Python 3.11 grammar checking from
running that interpreter, and records Ruby/Psych parsing of the workflow.

The initial development run exposed three test-harness errors: macOS temporary
path canonicalization, a singular/plural diagnostic assertion, and extraction
of YAML job blocks. They were fixed before the recorded successful run; no
production acceptance rule was relaxed for those test errors.

The checker and workflow contracts, trusted-base selection, separate identity
fields, exact evidence-index schemas, pending/admitted distinction and later
publication boundary are documented in `.github/ci/README.md`.
