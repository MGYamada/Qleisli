# Shared checked formal operations: actual results

The ordinary [before-code contract](phased-contract-01.md) was recorded in
[#32](https://github.com/MGYamada/Qleisli/issues/32) before production edits;
[the exact readback](github-before-code-32.json) preserves that checkpoint.
One private `Formals` now supplies the real finite and sized declaration
consumers with checked ordinary bases, finite Meaning payloads and the three
explicit access slots. Sized kind checks borrow the existing environment.
Original binder association, type shape, error and capacity order, complete
unused-body checking and native acceptance remain at their stated boundaries.

## Actual consumer validation

Actual Rust **1.98.1 and 1.85.0 each passed 147 tests with zero failures**:
four existing shared-type unit tests and 143 tests across thirteen integration
targets. Both runs passed formatting, all-target compilation, warnings-denied
all-target Clippy and CLI rebuild. The separate raw stage records are in
[latest attempt 02 (archived)](validation/README.md) (`validation/latest-attempt-02/results.json`) and
[MSRV attempt 01 (archived)](validation/README.md) (`validation/msrv-attempt-01/results.json`). Their 715 declared
source inputs remained unchanged throughout each run. This is an incomplete
build/runtime/fixture closure, not validation of a complete committed release.

Four new real-consumer controls exercise direct formal Adjoint/Controlled,
missing access in private unused bodies and dead arms/zero folds, and duplicate
requirements with the original per-profile locations. Positive controls execute
small operations against an independently written complex T/controlled-T
formula, including external-reference slices, at tolerance `1e-11`. Numerical
observations do not establish exact correspondence or a general theorem.

The genuine first formatting failure remains in
[latest attempt 01 (archived)](validation/README.md) (`validation/latest-attempt-01/results.json`); only two test
assertions were reformatted before the successful second run.
[The repair record (archived)](validation/README.md) (`validation/format-repair-01.json`) identifies those bytes.
Three existing sized tests remain ignored. Two unrelated 3000-file import
stress tests, the 4000-source differential suite, full CI and Lean
build/audit/replay were not run in this bounded validation. No new maximum
quantum case was generated.

## Exact comparison and independent review

All **40** unchanged first-source text/JSON checks matched raw stdout, stderr,
exit status, literal command and native journal bytes/counts without
normalization. Both observations contain **6 successes, 34 refusals and 46
pre-execv forwarded attempt rows**. The comparison used the rebuilt latest CLI
before the MSRV build. Those rows do not independently attest native starts or
exits. Original source/manifest bytes, FIRST map and all before files remain
unchanged. The actual [comparison summary](../../../authoring_sessions/common-formal-access-v030/after-attempt-01/summary.json)
and separate [terminal observation](../../../authoring_sessions/common-formal-access-v030/terminal-after-attempt-01.json)
retain the result; semantic/profile failures are not hidden as successes.

The [independent actual-code review](independent-implementation-review-by-docs-01/review.md)
found no blocking defect in the seven production files and their real callers.
Its read-only audit also checked the complete original forty observations;
that audit was not an execution of the after collector or tests.
[Current metadata maintenance](metadata-review/README.md) binds all 254 source
rows, adds only private `formals.rs`, updates the six reviewed old source
hashes and coverage's derived surface identity, and retains every other parsed
route, criterion and proof-status field. The original inventory refusal and
preparation assertions remain recorded. [Policy checks](policy-validation/README.md)
are a separate fixed command packet with their own actual results.

## Remaining scope

This factor does not complete the common whole-source checker, semantic
checking before lowering eligibility, canonical generic std/QFT, namespace
migration, source/runtime preservation, exact Fourier family or quantitative
resource proofs, or release readiness. Both ordinary QLV1 scoped guarantees
and pending QS/PR/RS/EXACT obligations retain their exact adopted scopes and
premises. No constitutional text, adoption/admission record, native rule,
dependency version, accepted schema, ledger status or Issue criterion changed.
All 24 #317 criteria remain required; confirmed completion remains
**14/111 (12.61%)**.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
