# Independent audit of the formal unit's actual results

Reviewer: `/root/isometry_cli_tests`. This is an additive read-only results
audit, not another execution. No recorded driver, harness, CLI, native checker,
test or build was run or imported. Only local file reads, hashes and JSON/raw
log parsing were used. I authored the four additional test controls; I did not
author the production implementation or root's validation/capture records.
This audit independently checks those recorded results, rather than claiming
independent review of my own test design.

No actionable result, identity or count mismatch was found.

## Original and replay observations

All 46 FIRST members match their recorded bytes, SHA-256 and modes; the FIRST
map retains SHA-256 `140bc0e555d23460d6f8c523627c8cba643ca3ddc2aaa3d95533e06234a2e454`.
All 203 before files match the frozen complete inventory and corresponding
hash/byte/mode rows. The replay file map's 205 members also match; its own map
is self-excluded. The original and replay identity records match their
respective frozen preparation identities.

For each of the 40 cases, I compared the literal argv and cwd to the original
command plan and both pre-command records; verified completed outer-client
status with no recorded operational error, truncation or limiting; recomputed
raw stdout/stderr/native-journal hashes and compared the actual bytes; parsed
every journal and checked row count; and matched all summary fields. All six
comparison predicates hold for every case, without output normalization.
The 20 JSON presentations have the corresponding success/error outcomes and
truthful diagnostic/result envelopes. Both runs have six successes, 34 source
refusals and 46 journal rows. The journals record forwarded attempts immediately
before `execv`; they do not independently attest native child starts or exits.
The replay summary retains SHA-256
`41ccc86663b8d11065fb011a03e6cba843979f275a9f392209c2a414acc5ff99`.

## Rust records and current inputs

For both `latest-attempt-02` and `msrv-attempt-01`, all eight stage records match
their separate JSON files and planned argv. Every stage records exit zero,
no launch/timeout/postcondition error and unchanged declared source/native
identities; every raw stdout/stderr hash and length matches. Cargo/rustc raw
version outputs identify 1.98.1 and 1.85.0 respectively. Independently parsing
the raw test result lines gives four shared unit tests and 143 integration
tests: **147 passed, zero failed, three existing ignored** per toolchain.
The library filter count is 112; two separate project stress tests are filtered
by explicit skips. The 13 integration pass subtotals are
`10,13,3,15,14,9,8,9,3,11,38,2,8`.

Each run's before/after maps are equal, contain 715 declared inputs and have
independently recomputed digest
`9292057ddc1cd09f4eb0ff0689b8d52b0be14edf245fd8683011d2078a84ed42`.
These are incomplete declared maps. All seven changed production files still
match the replay's recorded after identities and both Rust input maps. The
current test file matches the genuine formatting repair's after hash. The first
attempt's actual formatting refusal and unexecuted tests remain preserved;
the subsequent repair changes no test assertion semantics. The separate
manual subtotal correction is accurate: its former +10 reporting error was
not a test, compiler or native failure.

The replay used historical latest CLI
`2209c0528e4f25dc46498bbbe8cc3ca3df31201e0fa7bed41130bff593e233c9`.
The current shared CLI file instead matches the terminal MSRV rebuild
`d219e3cb0e546c8173ab1215ffd94cacc7c032ce9abd145b98949bbb2c4d089e`.
The current native file matches both validations and replay:
`39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85`.
File hashes alone do not attest running-image provenance or compiled HEAD.

## Four added consumer controls and limits

Both raw integration logs contain one passing line for each of:

- `direct_formal_adjoint_and_controlled_slots_are_usable`
- `private_unused_formals_cannot_borrow_adjoint_or_controlled_access`
- `selected_unused_dead_arms_and_zero_folds_check_both_missing_access_slots`
- `duplicate_adjoint_and_controlled_slots_keep_each_profile_diagnostic`

Reading the actual tests confirms real finite/selected declaration consumers,
exact per-profile diagnostics/spans, private unused bodies and selected dead
arms/zero folds. Direct controlled syntax's finite refusal remains explicit;
finite `qif` is its separate real consumer. The positive selected programs
retain an ordinary source provider and source identity, use a native-checked
operation and compare small complex coefficients including two external
reference slices to independently written T/inverse-T/controlled-T equations.
The oracle does not copy producer meaning or probabilities. Numerical tolerance
`1e-11` is a bounded regression observation, not an EXACT discharge or proof.
Selected-only dead-arm/fold controls do not claim downstream finite access
coverage after that profile's earlier unsupported-form refusal.

The audit establishes consistency of these bounded records. It does not
complete whole original-AST generic checking, common frontend, canonical std/QFT,
source/runtime preservation, a general family theorem, full CI or release
readiness. Existing ignored/skipped cases, declared-map limits and mathematical
premises remain explicit. No guarantee/adoption/Issue criterion or completion
status is changed; pending QS/PR/RS/EXACT obligations remain pending.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
