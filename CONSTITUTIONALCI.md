# Constitutional CI specification

**Specification revision: 1. Constitutional edition: 2026. Release line: 0.3.0.**

This is the canonical operational specification for Qleisli's constitutional
checks. It fixes their required behavior, evidence boundaries and change rules.
It is subordinate to the ratified [Constitution](CONSTITUTION.md), the human
acts recorded under [governance](governance/README.md), and the
[authority hierarchy](docs/src/reference/authority.md). It neither amends the
Constitution nor adopts an interpretation, admits a guarantee or approves a
release. Revision history belongs in Git; current proof status belongs in the
ledger, not in a second editable inventory here.

This file is ordinary maintained documentation, not a protected constitutional
artifact. It has no pinned content hash, ledger entry or dedicated approval
gate. Changes to this file alone use docs-only validation. Correcting or updating
the document does not authorize a change to the Constitution, a protected record
or the behavior of an enforcement check.

The implementation is the existing checker and workflow described below.
An implementation/specification mismatch is a review or maintenance defect;
passing the implementation alone cannot resolve that conflict. The coverage
limits in this document are part of the specification: a successful check must
not be advertised as verifying an unimplemented obligation.

## 1. Authority and responsibility

The natural-human Constitution Guardian Office (CGO) determines the applicable
QS, PR and RS obligations and whether a formalization adequately expresses
them. Lean or the designated independent checker verifies derivability under
the recorded proof boundary and assumptions. CI checks recorded acts,
continuity, current evidence and the selected validation results.

CI, AI agents, Issue state, theorem names and source annotations cannot supply
a human adoption or adequacy judgment. A hash binds bytes; it does not
independently authenticate the human who spoke. Historical candidate notices
remain unchanged after adoption; a separate affirmative human record supplies
the resulting authority. Ordinary maintenance within adopted requirements
does not require a new interpretation for each change.

The ledger records only human-admitted guarantees concerning the constitutional
QS, PR or RS obligations. Helper lemmas, implementation milestones and routine
tests do not acquire ledger entries automatically. Transport proofs supporting
an existing guarantee update its current evidence without creating a new
admission. The external schema registry has a separate role and cannot confer
constitutional authority.

## 2. Protected inputs and identities

| Input | Required treatment |
| --- | --- |
| [Constitution](CONSTITUTION.md) | Preserve the complete ratified bytes. The current SHA-256 is `40777370ec860891991bc89ef283f01a5db9a6be5480143f2e09e6014407452b`. No editable metadata is excluded from this text. |
| [Ratification and appointment](governance/ratification-2026.json) | Bind the exact text, approved governance candidate, edition, adopting human, appointment and effective date. Preserve the approved candidate separately from current `GOVERNANCE.md`. |
| [Initial interpretation adoption](governance/interpretations/initial-2026-adoption.json) and [reviewed text](governance/interpretations/initial-2026-reviewed.txt) | Preserve the adopted QS-2026-01, PR-2026-01 and RS-2026-01 identities, scopes, premises and separate pending status. |
| [Exactness adoption](governance/interpretations/exactness-2026-adoption.json) and [reviewed supplement](governance/proposals/exactness-2026.md) | Preserve EXACT-2026-01 across the same three jurisdictions. It adds no fourth Fundamental Theorem or discharged guarantee. |
| [Scoped admission](governance/guarantees/initial-2026-admission.json) and [reviewed proposal](governance/proposals/initial-guarantees.json) | Preserve the explicit human adequacy/admission act and the exact protected meanings, premises, exclusions and historical proof evidence. |
| [Ledger](governance/guarantees.json) | Preserve all admitted identities and pending duties; validate its schema, references, coverage and current evidence bindings. |
| [Current evidence](governance/guarantees/current-evidence.json), [semantic baseline](governance/guarantees/initial-2026-semantic-sources.json) and [continuity baseline](tests/fixtures/constitution_v030/initial-guarantees-continuity/baseline.json) | Bind the admitted properties to current actual checker definitions, decoded artifacts and independent meanings. Historical evidence stays separate. |

Constitutional edition, product release version, native protocol/profile,
schema version, source revision, accepted artifact and native executable
identity are distinct coordinates. An edition identifies the constitutional
regime; it is not inferred from syntax or a compiler version. One matching
coordinate cannot substitute for the others.

The current active ledger uses schema v5. Schemas v1–v4 are recognized for
checked historical transitions, not as alternative active ledgers. Unknown
schemas, malformed or duplicate fields, missing records, invalid paths and
incorrect file digests must reject. Changing an expected digest does not
authorize changing the protected artifact it identifies.

## 3. Validation modes and result boundaries

| Mode | Entry point | What success establishes |
| --- | --- | --- |
| Record and source integrity | `python3 scripts/check_constitution.py` | Consistency of the fixed recorded acts, ledger, historical evidence and current source/evidence identities. It is not fresh Lean replay. |
| Trusted-base continuity | Add `--base-ref COMMIT` | The preceding checks plus preservation of already recorded protected artifacts and admitted identities against the caller's reviewed Git base. |
| Current proof verification | Add `--verify-lean` | The preceding checks plus live execution of every selected fixed registered guarantee verifier in the built Lean environment. This does not run every release check. |
| Scoped release readiness | `python3 scripts/check_constitution.py --require-release-ready` | Delegates to `scripts/check_release_ready.py`; requires the additional trusted context, requirements, receipts and artifacts in section 7. It cannot establish full constitutional conformance. |

The first three rows are complementary checks that may be combined; readiness
is a separate result. The ordinary CLI exits zero on success and nonzero on
failure. Its output distinguishes source identity from current Lean replay.
The internal result also identifies the SHA-256 of the exact ledger checked,
admitted/pending counts and verification mode. Counts alone cannot establish
ledger identity. Failure must not produce a successful readiness receipt.

## 4. Record continuity and fixed verifier dispatch

The caller selects the continuity base from previously reviewed history or
the bound workflow event. An unchecked candidate HEAD, candidate-supplied
expected hash or convenient last commit is not an independent trusted base.
The ordinary CLI can run without a base, but that result must explicitly be
reported without a trusted-base continuity claim. A selected unavailable or
malformed base must reject rather than silently disable comparison.

The checker must preserve each stage already present at that base: ratification,
interpretation adoption, scoped admission, historical continuity evidence,
ledger history and the exactness supplement. A recorded stage with missing
artifacts cannot be treated as a new introduction. Supported migrations retain
the preceding ledger bytes and every previously admitted identity.

The active ledger separates immutable admitted identities from replaceable
current evidence bindings. Each admitted identity binds its ID, jurisdiction,
interpretation, human admission, reviewed proposal and proposal entry, with a
canonical edition-bound identity digest. Refreshing current proof evidence
does not replace those fields or narrow the admitted scope.

Production registrations and executable verifier profiles are fixed reviewed
checker code in [check_constitution.py](scripts/check_constitution.py) and
[check_guarantee_ledger.py](scripts/check_guarantee_ledger.py). Candidate JSON
cannot register a human approval, add an executable verifier, choose commands,
omit a guarantee or redirect its evidence to an arbitrary path. Every admitted
identity needs exactly the coverage required by its registered profile;
unknown profiles, duplicate coverage, fabricated discharge and missing
evidence reject. Current dispatch uses `qlv1-structural-identity-v1` for both
initial admissions; the record's checked continuity format selects only its
implemented identity or transport cases.

Verification captures ledger and protected evidence bytes, checks the digest
actually consumed by each verifier, and rejects replacement during checking.
After live replay, source-only validators run again for all selected profiles
so a later verifier cannot leave an earlier one bound to changed sources.
Start/end equality and matching entry counts are insufficient substitutes.

## 5. Current proof and production binding

The two admitted guarantees are `QS-QLV1-OWNERSHIP-2026-01` and
`QS-QLV1-SCOPE-2026-01`. They cover independent linear ownership and classical
lexical scope of the original decoded ordinary QLV1 root accepted by the
actual `QleisliKernel.Protocol.Validity.check` definition. Their quantifiers
retain original bytes and budgets, optional-request behavior, decoded artifact
and root selection. They do not certify every dependency, source program,
hierarchical path or native-contract path by implication.

[check_initial_guarantees.py](scripts/check_initial_guarantees.py) and
[check_guarantee_continuity.py](scripts/check_guarantee_continuity.py) must
preserve independent protected predicates, theorem types, Acceptance/Artifact
fields and the relevant elaborated definition, constructor and recursor
closure. A success predicate cannot be substituted for the intended property.
The current source closure and recorded build/audit evidence must agree with
the registry and the actual files being checked.

Live verification compares fresh type/axiom output and current extraction with
the protected review and historical baseline. The supported cases are full
expression identity, the fixed atomic-Bits basis/artifact transport and the
fixed Raw/Basis transport. Representation changes require checked semantic
transport where identity no longer applies. The Raw profile permits only its
fixed namespace/helper mapping and bound-variable display changes; it preserves
binder kinds, indices, types, bodies and constructor fields. Arbitrary renaming,
a review marker, a source hash or a proof about an obsolete predicate is not
semantic preservation.

Use pinned Lean/Mathlib 4.30.0. Build and audit the applicable actual definitions
before live verification. Source and compiled policy checks must retain their
rejection of project axioms, `unsafe`, `partial`, `implemented_by` and `extern`
overrides, including private/generated helpers. The recorded axiom basis for
the scoped proofs is `propext`, `Classical.choice` and `Quot.sound`. Full proof
validation additionally retains fresh kernel/Main replay and the independent
native, source and small-system oracle checks required by the shared manifests.
A compiled binary digest is provenance, not proof of native compiler/runtime
correctness.

Production acceptance remains the independently selected native Lean checker
under [TRUSTBOUNDARY.md](TRUSTBOUNDARY.md). A fresh decision binds private
accepted handles to immutable original artifact/request bytes. Missing,
incompatible, malformed, timed-out or failed checking must not fall back to
Rust acceptance, cached success or a producer receipt. CI receipts described
below are validation evidence; they are not executable acceptance handles.

## 6. Scheduling, lanes and required contexts

Develop and validate locally. Hosted runs start on every branch push, on pull
requests when opened, updated or reopened, and on `v*` tag pushes. Explicit
manual Issue-completion checkpoints and release checks remain available.
Several related Issues may share a checkpoint. Completion fields record intent
and do not automatically close Issues. A later source change invalidates the
applicability of earlier results. Each run retains its own concurrency group;
later events do not automatically cancel existing runs.

[ci_profiles.py](scripts/ci_profiles.py), the
[source-check manifest](.github/ci/source-checks.json), the
[native-comparison manifest](.github/ci/native-comparisons.json) and the
[workflow](.github/workflows/ci.yml) retain one shared local/hosted procedure.
Unknown or policy-sensitive inputs select conservative validation.
Constitutional records, enforcement/workflow and Reference changes select the
full policy-risk proof lane. This document alone is an explicit docs-only input;
its ordinary documentation treatment does not extend to those other paths.
The cumulative PR diff and its exact head remain bound to selection and size
checks.

The documentation producer checks record identities and rejection regressions
and runs the separate event-base continuity invocation. `tests` retains native
build/audit and native comparisons but is not live Mathlib guarantee replay.
`model` and `full` additionally build/audit the mathematical environment and
run the fixed live constitutional verifiers; `full` also rebuilds schema types
and runs the retained fresh proof replays. Required contexts `rust`, `rust-msrv`,
`macos-source`, `interop`, `lean`, `lean-kernel`, `distribution` and `docs`
aggregate all selected producers against the exact checkout. A failed selector
or missing/failed/skipped selected producer fails the gate. An intentionally
unselected producer is not evidence that its work ran.

Corpus validation uses `--quick` / `quick-representative-v1` in every profile,
including releases and manual full validation. Automatic exhaustive corpus
execution is retired. Selected probes, omissions and failures stay visible;
representative testing does not establish a universal proof. Full proof replay
and exhaustive corpus enumeration are different operations. Fixture and PR
[size budgets](.github/ci/README.md#size-budgets) remain unchanged; no maximum-size
experiments or new fixture inventories are required by this specification.

## 7. Scoped release readiness and evidence consumption

Readiness requires a clean exact candidate, full selected suites and the full
proof lane. The trusted caller supplies an exact reviewed base through
`release_base` / `RELEASE_TRUSTED_BASE`; a tag workflow may use the repository's
`QLEISLI_RELEASE_BASE`. There is no candidate-HEAD fallback.

The gate reads `release/requirements.json` and its review/Issue snapshots from
immutable Git blobs at that base. Candidate `release/acceptance.json` must bind
the exact requirements digest, all criterion IDs and required evidence roles,
the schema registry and separate edition/schema/protocol identities. Only
reviewed requirements can mark a criterion `explicit-later-version`; a
candidate cannot reduce scope. The complete-feature inventory is the 127 Issues
in the 2026-10-12 beta plan under #142; the original 111 remain recorded as
history. #83 requires completion after its explicit resumption, so an older
reviewed deferral cannot authorize beta readiness. Closed Issues still require
current evidence. The maintainer excludes #39 and #63 from all v0.3.0, including
beta and the current goal, superseding #39's earlier resumption. Retain all 127
audit entries as 125 applicable Issues and two approved exclusions, without
implementation credit for either exclusion. The approved generic-QFT exclusion
remains separate.
GitHub remains the decisions/progress ledger.
These files are evidence indices, not another backlog or authority for adoption.
The criterion review references the
[primitive admission and replacement policy](docs/src/reference/primitive-boundary.md#admission-and-replacement-process)
for any new sealed semantic authority, including its independent contract,
QS/PR/RS impact, human specification review, inventory and migration obligations.
Source/constructor and production-route checks detect drift; no candidate hash
or successful release receipt supplies that human review or admits a primitive.
Referencing this policy is distinct from satisfying the full release gate.

For `0.3.0-alpha` alone, the maintainer separately approved the
[development-snapshot scope](release/alpha-scope-proposal.md), with the
[affirmative human record](release/alpha-scope-approval.json) tracked in
[Issue #351](https://github.com/MGYamada/Qleisli/issues/351). The gate binds both
exact records to the trusted base and candidate, and uses
`release/alpha-acceptance.json` to bind approval, identities and proof status.
This snapshot need not complete the feature goal. It still requires every
producer, full proof/replay lane, same-attempt receipt and artifact check below.
Other versions retain the complete-feature gate. This ordinary release-scope
decision adopts no constitutional interpretation or discharged guarantee.

The proof-scope disclosure must say `scoped-pre-v1` and bind the exact checked
ledger digest, sorted admitted IDs and all sorted pending IDs, including
EXACT-2026-01. Pre-v1 pending broader obligations are disclosed, not silently
discharged and not by themselves an unconditional ban on scoped releases.
Every already admitted guarantee still needs its current evidence verification.

Every successful validation producer emits a receipt outside the candidate
tree. The final gate consumes same-run artifacts and their digests supplied
through trusted workflow `needs` outputs. It verifies repository, commit/tree,
run ID, attempt, event, producer identity and actual payload hashes. Candidate
JSON cannot choose the workflow run or trusted digest. Rerunning only failed
jobs cannot combine earlier-attempt successful receipts into readiness.
The Lean producer must supply the live constitutional replay result for the
same exact ledger, not a source-only result.

Distribution evidence binds the checked crate, complete source archive and
fresh installation to that commit and synchronized product version. Both
macOS arm64 and Linux x86_64 native bundles need full fresh replay, exact source
and payload inventories, matching protocol/version/target, checksums and
licenses. Readiness rechecks its captured mutable inputs before success.

The supported hosted boundary obtains context from GitHub and digests from
producer outputs. Offline environment variables and synthetic tests can model
that boundary; they cannot authenticate real GitHub provenance. The checker
does not establish human review merely from a review file/hash.

Success reports `ready-scoped-candidate`, not publication authorization or full
constitutional conformance. Ordinary required contexts are test gates and do
not substitute for readiness. Merging, tagging, pushing and publication are
separate acts; publication needs separate authorization and artifact readback.

## 8. Failure rules, regressions and present limits

Required rejection regressions cover unauthorized text/record changes, removed
or rebound admitted identities, schema rollback, invented admission/discharge,
unknown verifier selection, missing current bindings, changed predicates or
decoded-root witnesses, stale evidence and replacement during verification.
Release regressions additionally cover wrong commit/run/attempt/job, missing or
forged producer digests, source-only proof receipts, hidden pending duties,
unauthorized scope reduction and mismatched package/native payloads.

These checks are maintained in
[test_check_constitution.py](scripts/test_check_constitution.py),
[test_check_initial_guarantees.py](scripts/test_check_initial_guarantees.py),
[test_check_release_ready.py](scripts/test_check_release_ready.py),
[test_ci_profiles.py](scripts/test_ci_profiles.py) and the shared policy/action
tests. Failures must identify the violated boundary. Repair the technical
defect or obtain the necessary concrete human judgment; do not rewrite a
protected record, raise a limit or disable a required check to obtain success.

At revision 1, QS-2026-01, PR-2026-01 and RS-2026-01 remain broader pending
obligations, with pending EXACT-2026-01 proof/enforcement duties. The two scoped
admissions do not establish ordinary-root EffectSound/CPTP, source/native/runtime
preservation, general hierarchy semantics, PR or quantitative RS. Ownership
`ResourceSafe` and checker work limits are not quantitative RS. Epsilon bounds
and floating-point oracle agreement cannot replace an applicable exact duty.

The readiness checker exists, but no completed real requirements/acceptance
index is present. Its active inventory contains 13 groups/127 Issue IDs and
retains the historical 111 separately. Historical alpha exclusions do not
authorize the beta gate.
Release use requires a reviewed complete index reflecting the authorized
criteria, not automatic generation of completion evidence. No release readiness
is claimed by writing this specification.

Current checks do not mechanically decide all semantic non-weakening, prove
coverage of every production path, authenticate human transcripts, attest
native compilation/runtime or implement an Article IX rectification process.
Those limits remain explicit work under
[constitutional enforcement #141](https://github.com/MGYamada/Qleisli/issues/141)
and [release readiness #142](https://github.com/MGYamada/Qleisli/issues/142).
An arbitrary future guarantee or representation is not supported merely
because the ledger schema can describe it.

## 9. Change control and agent handoff

Maintain this file as the single operational specification. Link to it from
the Book and working procedures when needed; do not create another editable
copy. This document can be revised through ordinary documentation maintenance,
without constitutional protection or a separate approval procedure. Changes to
actual enforcement contracts still follow the applicable review process: record
the affected contract, constitutional impact, migration where necessary and
performed or unexecuted checks in the relevant Issue/PR; update the documentation,
enforcement and rejection coverage together. A changed contract warrants a new
specification revision. Review must not approve a weakening forbidden by the
Constitution.

Routine evidence refresh or a preserving technical refactor stays within the
existing admission. A new binding interpretation, adequacy judgment or guarantee
admission still requires the responsible human CGO's explicit adoption of the
concrete proposal. A constitutional-text change follows Articles III/IV, or a
valid strictly pre-v1 Article IX process with separately reviewed enforcement.
This specification grants no authority to modify entrenched bytes.

At startup, model change or context reset, follow the
[constitutional handoff](governance/README.md#agent-startup-and-handoff).
Read repository originals, preserve their recorded scopes and run integrity
and trusted-base checks before dependent work. Report whether Lean replay was
actually performed. Missing/conflicting/failed records stop dependent changes;
paused development remains paused. Conversation summaries and prior model
conclusions do not replace the records or authorize resumption.

For local record/continuity validation, with `REVIEWED_BASE` supplied by the
human task or review process:

```sh
python3 scripts/check_constitution.py --base-ref "$REVIEWED_BASE"
```

After the applicable pinned Lean environments have been built and audited:

```sh
python3 scripts/check_constitution.py --base-ref "$REVIEWED_BASE" --verify-lean
```

Local plans, command/result formats and hosted invocation details remain in
the [shared CI procedure](.github/ci/README.md). Passing these commands never
substitutes for a human decision or the separate release gate.

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
