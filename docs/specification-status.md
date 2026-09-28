<a id="有限コア仕様v0-決定適合状況証明課題"></a>

# Finite-core v0: decisions, conformance, and proof obligations

Current status (2026-09-28): **the declared finite v0.1 semantic-contract profile
is implemented and checked; general correspondence between all accepted Rust
paths and the mathematical source/IR rules remains unproved.** The stated
mathematical rules have ideal-soundness paper proofs Q1–Q3. Local Lean results
have the scope recorded in the [proof ledger](lean-resource-proof.md).
The [generated current status and rule inventory](current-status.md) derive
from one current-state record and the manifests. The [0.1.8 record](releases/v0.1.8.md) separates fixed-width M1 implementation,
its explicit version exception and local validation from publication.

This ledger retains dated Japanese entries as original historical evidence.
Their counts, “pending” statements, and checks not rerun describe those steps.
The current [release record](releases/v0.1.8.md) and
[documentation map](documentation-map.md) identify subsequent results and
English authority. Historical text does not override current specifications.
The original 2026-09-26 introduction recorded paper Q1–Q3, unfinished general
Rust/IR correspondence, SPEC-0–2 records, and SPEC-3/4 progress in the
[roadmap](../ROADMAP.md); those proof limitations remain.

## Fixed-width M1 implementation in v0.1.8 (2026-09-28)

The user selected v0.1.8 for continued implementation on a suitable branch.
The normative [M1 supplement](next-minor-spec.md) now has static operation
parameters, independent access constraints, basis-derived meanings and checked
composition. The existing monomial/FunctionEvidence boundary expresses these
obligations; no new core checker rule or IR variant is introduced. Generic
source checks do not issue evidence; each concrete computed equation still
requires exact independent checking.

The [release record](releases/v0.1.8.md#validation) records primary/MSRV Rust,
source/evidence regressions, docs/helpers, representative execution and pinned
Lean audit results, along with skipped release gates. Reserved identifiers and
public AST/error additions require migration; the old function-contract example
renames its `meaning` module to `specification` while retaining its operator.
No v0.1.8 publication, general Rust theorem, completed M1/M2 milestone or V1
algorithm acceptance follows from this implementation.

## v0.1.7 release procedure (2026-09-28)

The user prioritized releasing the completed JSON diagnostic and bounded
OpenQASM input/output + QIR output slice. Operation parameters, independent
meaning declarations and QIR input remain unreleased work. The shorter README
and English working guidelines preserve the project contracts and proof limits.
Implementation CI passed all five jobs, including the new external-interop job;
the [release record](releases/v0.1.7.md#release-preparation-and-hosted-validation)
and [GitHub publication evidence](https://github.com/MGYamada/Qleisli/releases/tag/v0.1.7)
identify exact-commit release checks, source distributions and publication.
Earlier candidate records below retain their original scope and pending states.

## M1.1-A connections start in v0.1.7 (2026-09-28)

The user's additional M1.1 request now has a [normative terminal profile](interop-m1.1.md)
and additive Rust adapters for OpenQASM 3 input/output and QIR 2.0 Base text
output. Explicit fresh initialization, exact gate phase, physical/logical IDs,
measurement consumption, hidden terminal disposal and result order are specified.
Unknown gates, missing initialization, reuse, malformed/aliased IDs and capacity
excess reject before returning an artifact. Imported IR passes the same verifier;
no new verifier rule, source form or certificate authority was added.

Independent input fixtures, exact gate matrices, negative cases and external
OpenQASM/LLVM checks are recorded in the [0.1.7 continuation](releases/v0.1.7.md#m11-a-connection-continuation).
QIR import, adaptive instruments and Python packaging remain open. LLVM
validity and local tests do not establish general translation correctness,
backend execution, M1 completion or publication. Earlier dated records below
retain the status and validation scope of their own work.

## M1 X1 implementation starts in v0.1.7 (2026-09-28)

The user explicitly selected v0.1.7 for M1 new-feature work after the normal
MINOR rule was explained. X1 check/run now emits versioned JSON through an
opt-in flag, with stable error categories, nullable source locations, original
UTF-8 offsets and ordered finite distributions. Structured diagnostic APIs
preserve legacy public error types and route through the same source/IR checks.
The [machine-interface contract](machine-interface-spec.md#diagnostics) records
flag/path migration, endpoint roundoff and still-unimplemented commands.

The [implementation record](releases/v0.1.7.md) reports actual validation.
This is new functionality, not compatible-only maintenance. N1–N6, X2–X6,
M2, general compiler correspondence and publication are separate pending work.
No new core rule, dependency or proof declaration is introduced.

## v0.1.6 release procedure (2026-09-28)

The user authorized final review, distribution verification and publication.
The scoped [review and release record](releases/v0.1.6.md#publication-request-review)
covers comments/diagnostics, metadata separation, public IR compatibility and
the existing regressions; no additional implementation defect was identified.
Current-version records and the README heading are finalized, with concrete
comment-migration examples. The
[GitHub release evidence](https://github.com/MGYamada/Qleisli/releases/tag/v0.1.6)
identifies the exact commit, protected-branch PR, Linux CI, source distributions,
annotated tag and publication. Earlier entries retain their original counts,
package contents and then-pending publication states.

## Rust-style source documentation, retained in 0.1.6 (2026-09-28)

The user requested comments/docstrings aligned with Rust conventions and then
explicitly retained v0.1.6 after the normal MINOR requirement was explained.
The [extension specification](documentation-comments.md) records this exception,
lexical forms, attachment, public sidecar API, Markdown output and migration.
This is new functionality with source-acceptance changes, not compatible-only
maintenance. Earlier dated maintenance and validation entries remain intact.

The lexer now handles nested ordinary/doc block comments iteratively. Parsing
validates inner/outer doc attachment while preserving existing public AST fields
and token variants. [`parse_documented_module`](../src/frontend/parser.rs)
retains doc text/style and original UTF-8 spans separately; `qleisli doc` renders
one source file without type/ownership/contract checking or execution. The IR
verifier and evidence kernel gain no new rule or primitive. Comment claims cannot
authorize invalid source, and full source snapshots still bind function evidence.

All four bundled files and all twelve public/three private definitions carry
English documentation, with phase, bit order, ownership/effects and assumptions
matching the existing contract ledger. The [documentation suite](../tests/documentation.rs)
covers attachment, nested/delimiter corner cases, Unicode/CRLF byte spans,
20,000 nested blocks, metadata-neutral IR, ownership rejection and complete
stdlib coverage; [CLI tests](../tests/cli.rs) check rendering and errors.
The [release validation](releases/v0.1.6.md#rust-style-comments-and-stdlib-documentation)
records actual test/toolchain scope and remaining publication gates.

## Desugaring definition and coefficient-domain recommendation (2026-09-28)

The user requested explicit terminology and supplied a comment about the risk
of predicting the wrong future logical gate architecture. The
**[desugaring layer](terminology.md#desugaring-layer)** is now defined as a
meaning-preserving translation of convenient representations into already
specified core operations, with untrusted IR/proposed evidence submitted to
independent checks and no new primitive meanings or acceptance rules. Related
documents repeat this definition locally and distinguish source checking,
post-verification runtime adaptation and approximate synthesis.

The [coefficient-domain note](coefficient-domains.md) records the recommendation
to parameterize future exact algebra and separate exact meaning, approximation
and device/noise contracts. It cites primary STAR work, gives an out-of-R8 phase
example and requires reviewed domain arithmetic/equality, explicit embeddings,
evidence binding and bounded error composition. Generic type notation is not an
implemented API or permission to trust user-supplied equality. The current R8
kernel and M1/M2 profiles remain unchanged.

This follow-up changes documentation/current-state metadata only. Its
[validation record](releases/v0.1.6.md#desugaring-and-coefficient-domain-documentation)
separates document checks from earlier Rust/Lean results; no new kernel,
arbitrary-angle support, approximation checker, proof or backend is implemented.

## Small-core boundary and initial IR reduction (2026-09-28)

The user adopted the [small trusted-core boundary](design-philosophy.md#keep-the-trusted-core-small):
convenience belongs in desugaring, not in the checker. The
[constructor/emitter inventory](interoperability-roadmap.md#ir-reduction-and-the-trusted-boundary)
identifies raw `QuantumIf` and broader raw-only `ProtectedUse` forms as
compatibility debt; existing matching visitors are not production emitters.
The decision record and AGENTS.md make this an ongoing development constraint.

As compatible 0.1.6 maintenance, verified legacy qif arms now adapt to
`CircuitStep` and share numeric execution. Primitive/scalar execution stays
in place, preserving both-arm step charging, phase, axis order and ownership.
Public raw IR, verifier acceptance and independent exact extraction are
unchanged. This is runtime consolidation; trusted-core rule removal remains
pending a specified MINOR migration.

The added regression compares 61 arm configurations against the independent
exact extractor, with both polarities, every legacy primitive, empty arms,
`Unit` scalar phases, composed sequences, reversed physical axes, a coherent
reference, exact step-budget boundaries and state-vector allocation reuse.
The [release follow-up](releases/v0.1.6.md#internal-ir-reduction-and-trusted-core-boundary)
records executed checks and remaining release gates. This bounded comparison
does not prove general translation correctness.

## Interoperability direction (2026-09-28)

The user proposed QIR/OpenQASM 3 entry points and Python bindings to reduce
adoption cost and make the IR useful as shared quantum compiler infrastructure.
The [selected direction](interoperability-roadmap.md) records compiler layers,
initial finite import/export profiles, binding/wheel objectives and translation
obligations. Original M1 specifications remain intact; the additional extension
specifications and implementations are pending. The decision, roadmap and
generated status distinguish that scope from the completed initial M1 design.

Primary QIR Base/Adaptive, OpenQASM 3.1 and binding-tool references were inspected.
The review identified post-measurement ownership, controlled phase, exact versus
floating angles, external QIS meanings and evidence retention as explicit adapter
obligations. Successful parsing or LLVM validation alone does not establish
Qleisli semantic contracts or translation correspondence. QIRF remains a distinct
Qleisli JSON format.

Document/generated-status checks, all 19 document-checker tests and whitespace
checks pass. This follow-up changes documentation only. Rust/Lean tests and
interoperability acceptance tests were not run for this addition; no new binding,
importer, exporter, dependency or proof is implemented. The earlier 0.1.6 test and
package results below retain their original scope.

## v0.1.6 initial IR/evidence maintenance (2026-09-28)

The user selected 0.1.6 for compatible maintenance. The raw-IR verifier
erroneously accepted 65 nested classical branches when the deepest arms were
empty, violating its existing 64-level profile. Checking depth at the branch
itself fixes this without changing the declared limit or any public API.
The rejection path identifies the excessive branch before entering its arms.

The [release record](releases/v0.1.6.md#reproduction-and-regression-evidence)
records the reproduced failure and twelve raw-IR boundary cases. Twelve
additional function-evidence cases preserve the separate 32-level limit and
check both raw functions and their inactive branches with zero-width ownership.
Its preflight already enforced that limit; no evidence-checker defect was
found in this scoped comparison. The existing iterative raw-IR destructor
also needed no change. This is not a complete B019 or evidence-boundary audit.

Rust/Lean project versions and current records are synchronized at 0.1.6;
the [local validation record](releases/v0.1.6.md#local-validation) reports only
executed checks. M1/M2 implementations, general Rust adequacy proofs and
publication remain separate. Prior release and test histories below are intact.

## v0.1.5 release procedure (2026-09-27)

The user authorized publication of the completed maintenance candidate, including
the follow-up specification fixes and Physlib deferral. Release summaries now
refer to the [release record](releases/v0.1.5.md) and
[GitHub publication evidence](https://github.com/MGYamada/Qleisli/releases/tag/v0.1.5)
for the final commit, PR, required CI, immutable annotated tag and source archives.
The procedure follows protected-main requirements without bypass. The earlier
candidate entries below retain their original validation and then-pending
publication states. New public M1/M2 features and general soundness proofs
remain unfinished; this PATCH does not claim those milestones.

## M1 specification review corrections (2026-09-27)

The follow-up review identified two defects in the selected future specifications.
The [portable IR envelope](machine-interface-spec.md#portable-finite-ir-and-evidence)
now retains exact root input/output type trees separately from raw bit-count
shapes. Import validates their port binding; requested contracts reject absent
type information and equal-width but different trees at either port. The
[controlled-operation rule](next-minor-spec.md#access-judgments-and-composition)
now specifies index c+2x and the permutation needed to express a block matrix.
It preserves the current least-significant-control convention, including scalar
phases on Unit. X2/X3 and N2 record the corresponding future acceptance cases.

These are specification corrections within v0.1.5 maintenance, not implementation
of QIRF or M1. The [follow-up validation record](releases/v0.1.5.md#specification-review-corrections)
distinguishes document checks and exact finite label calculations from the
unimplemented import/lowering acceptance tests. Current Rust/Lean code and
public contracts are unchanged.

## Physlib deferred to a future concrete use (2026-09-27)

At the user's later request, remove Physlib from the required Lean environment
and default CI until the finite IR instrument/CPTP bridge uses it. The
[decision and reintroduction gate](physlib-environment.md#current-decision-and-reintroduction-gate)
preserve the historical compatibility results and version baseline. Move the
external probe to research; no Qleisli proof module imports QuantumInfo and no
Qleisli declaration is removed. Lake resolution removes Physlib and five
exclusive transitive packages, retaining all nine Mathlib dependency records
and Lean/Mathlib 4.30.0 unchanged.

Post-removal `lake build Qleisli` succeeds (1,457 jobs, including cache hits),
and the project audit still checks 577 declarations with only the three
standard allowed axioms. The [release validation](releases/v0.1.5.md#dependency-deferral-validation)
separates these results from the earlier Physlib build/audit and records final
documentation/package checks. Rust and mathematical fixture execution are not
rerun for this dependency-only change. v0.1.5 remains the local maintenance
candidate; publication remains separate. This entry supersedes historical
instructions below to keep Physlib installed or run its external audit in CI.

## 0.1.5 local roadmap completion (2026-09-27)

Following the request to advance the roadmap, the
[completion record](releases/v0.1.5.md#roadmap-completion-evidence) marks version/scope,
review/specification handoff, current records, local validation and candidate
distribution complete in the agreed v0.1.5 maintenance scope. Exact-commit CI,
clean-source release checks, tag/push and publication remain pending. The
generated current status now identifies this local-complete state instead of
only version selection. M1 implementation, M2 sized syntax, the full B019 audit
and V1 acceptance remain open.

This advancement changes roadmap/status documentation only. Previous local
Rust/Lean and mathematical execution evidence below is retained with its actual
scope; it is not reported as rerun. Documentation checks and both candidate
archive contents are refreshed for the final roadmap state.

## 0.1.5 review response and scope selection (2026-09-27)

At the user's request, synchronize Rust/Lean project versions at 0.1.5 and
reflect the supplied review of 55510e8. The [response matrix](reviews/v0.1.4.md)
traces every recommendation to a disposition. [M0–M5](v0x-roadmap.md) replace
version-assigned themes; the [decision dossier](decisions/2026-09-27-v1-path.md)
selects fixed-width M1, bounded M2 continuation and a dated scope checkpoint.
B019-5 requires a selected scope and full extension rules rather than accepting
a permanent no-go. M0 scope selection and G020-1 for fixed-width M1 are complete
as specification work: [language rules](next-minor-spec.md),
[machine interfaces](machine-interface-spec.md) and the accompanying
[M2 IR/checker profile](hierarchical-ir-spec.md) state grammar, contracts,
access derivations, accepted/rejected cases, budgets, import trust and migration.
Their future acceptance matrices are not implemented tests. M1 implementation
and M2 sized source syntax remain separate gates.

The dossier addresses independent semantic vocabulary, conjugation-derived
control, ideal dyadic QPE angles, joint hierarchical-IR/evidence design,
reversible synthesis without whole-space tables, portable artifacts, JSON
results, sampling/retries, special-form migration and verifier/kernel-first
proof work. The AE draft's access/cost account and Shor indentation are corrected;
the Physlib investigation is distinguished from its later dependency adoption.

Current-state and fourteen grouped rule-boundary inventory rows are machine
readable, with a generated table checked in CI. They identify existing
implementation/test/proof references and open correspondence obligations;
they do not claim a complete fresh finite-conformance audit. Historical
records and theorem IDs are preserved. Five new document-checker regressions
cover stale output, version divergence, incomplete/invalid records and stale
Rust test references; six mathematical convention cases exercise the conjugation
identity and counterexamples. The [release validation table](releases/v0.1.5.md#local-validation)
records actual checks, with numerical fixtures distinguished from exact proofs.

No production or research Rust source, public Lean declaration, `.qli` rule,
capacity or dependency changes. The proposed byte limit and new public APIs
remain MINOR work. No new generalized algorithm, kernel feature, or soundness
proof is claimed, and publication is separate from this version selection.

## 0.1.4 release procedure and publication record (2026-09-27)

The user authorized v0.1.4 release through publication. The release date is
2026-09-27 (JST); current summaries and release notes are finalized for that
release. The active GitHub main rules require a PR, an up-to-date base,
resolved conversations and the four `rust`, `rust-msrv`, `lean` and `docs`
checks, without a bypass actor. The active `v*` rules prohibit tag updates
and deletion.

The release procedure verifies the exact merged-main commit's CI and packages
its clean source before creating and pushing an annotated tag and publishing
the GitHub source release. The [hosted release record](https://github.com/MGYamada/Qleisli/releases/tag/v0.1.4)
identifies the actual commit, PR, CI, archive validation and completed operations.
No crates.io package or prebuilt binary is included in this source release.
The historical preparation entries below preserve their original then-pending
states and candidate counts; version/date metadata alone is not publication
or completion of later maintenance work.

## 0.1.4 roadmap progress and local candidate validation (2026-09-27)

Following the request to advance v0.1.4, the
[P014 completion record](releases/v0.1.4.md#v014-roadmap-and-completion-evidence)
records P014-1–P014-4 complete locally: planning/review, candidate checks and
distribution verification. P014-5 exact-commit release gates remain pending. On macOS aarch64,
fresh Rust 1.98.1 and minimum 1.85.0 targets each passed all 258 production and
43 research tests and both packages' all-target Clippy checks. Primary fmt,
all 43 Python tests, 52 mathematical checks and 39 exact assertions passed.

Pinned Lean/Mathlib 4.30.0 with the compatible Physlib revision built the
selected modules successfully. Separate warning-as-error audits passed for
577 Qleisli and eight external declarations, using only the three allowed
standard axioms. All ten CLI examples checked and ran; Shor returned factors
3 and 5 on successful outcomes, with success/retry probability 1/2 each.
The [candidate validation table](releases/v0.1.4.md#local-candidate-validation)
records package/source contents, reproduction and platform scope: the 174-file
production package rebuilt successfully, and all 43 research tests passed from
the extracted 179-file complete-source candidate. Final status-only documentation
was refreshed in both archives and byte-checked, with executable inputs unchanged.

No Rust/Lean source, dependency, public API, capacity or toolchain was changed.
The independent review found no blocking issue with the maintenance scope or
historical/semantic boundaries. The Linux-only CLI case, final clean-commit CI,
tagging and publication are separate pending gates. These local checks do not
complete the planned v0.1.5–v0.1.9 audits, B019, generalized source support or
the general implementation-soundness proof. The earlier scoped checks below
retain their original then-unperformed checks as history.

## 0.1.4 version selection and v0.x maintenance boundary (2026-09-27)

At the user's request, synchronize the Rust/Lean project versions at 0.1.4
and adopt the [v0.x roadmap](v0x-roadmap.md). The
[B019-1–B019-6 boundary](release-milestones.md#v019-maintenance-boundary)
limits v0.1.4–v0.1.9 to compatible finite-core maintenance, conformance and
evidence audits, existing proof-obligation records and a next-minor decision
dossier. Later minor themes are conditional targets, not implemented features
or finalized extension specifications. Each proposed abstraction must identify
the programmer obligation removed and its replacement evidence/checker.

The existing finite effects, static operations and SC/FC evidence remain
implemented. New capability/typestate/effect syntax, size generalization,
generalized algorithms and public proof interfaces are outside this patch
series. Additional symbolic-kernel development/integration remains deferred
without a target release, while dense-free checking remains a prerequisite
for generalization. v0.1.9 does not promise a proof of the Rust compiler.

No Rust/Lean source, dependencies, public APIs or implementation limits are
changed. Historical results remain attached to their original releases.
The [0.1.4 validation record](releases/v0.1.4.md#validation-for-this-working-change)
records checks for this version/documentation change and explicitly separates
the unperformed full release checks and publication. B019 completion remains
future work; selecting 0.1.4 does not complete the later audits or design dossier.

## Final 0.1.3 release contents and validation (2026-09-27)

The final release includes the auxiliary shape/nonfinite fixes, retained
independent semantic research, its explicit deferral, and the compatible Physlib
environment. Fresh macOS checks passed on Rust 1.98.1 and 1.85.0: 258 production
and 43 prototype tests each, primary fmt and Clippy on both. Lean built Qleisli
and selected QuantumInfo modules; the 577-project-declaration and eight-external-
declaration audits permit only the standard three axioms. All 43 Python tests,
52 imaginary mathematical checks, 39 exact assertions and representative
executions passed. The [release record](releases/v0.1.3.md#final-release-validation)
states scope; the [GitHub release](https://github.com/MGYamada/Qleisli/releases/tag/v0.1.3)
identifies the exact commit, protected-branch CI and source distribution.
These release checks supersede candidate packaging for publication without
rewriting the historical records below or closing general soundness obligations.

## Physlib dependency in the existing Lean environment (2026-09-27)

At the user's request, add Physlib's `v4.30.0` compatibility tag at fixed commit
`f5242c99d796b59a390d26cd7d1a8057e04c46b5`. Lean/Mathlib remain 4.30.0;
all pre-existing dependency records and Qleisli's 0.1.3 version are unchanged.
The [environment record](physlib-environment.md) gives the remote version
comparison, lock, scoped build/audit evidence and third-party license details.
CI now builds the selected QuantumInfo modules and checks eight external
declarations against the same axiom allowlist as the separate Qleisli audit.
The local combined build passed; audits passed for 577 Qleisli declarations
and eight selected Physlib declarations, with only the three allowed standard
axioms. Document checks and all 14 documentation-checker tests passed.
CI configuration is recorded separately from an actual hosted CI run; Rust
was unchanged and its tests were not rerun in this dependency-only step.

This installs mathematical infrastructure without changing public Qleisli
declarations or establishing language/IR semantic correspondence. The
symbolic-kernel deferral remains in force. Earlier survey results against
Physlib's newer 4.34.1 environment remain historical and are not substituted
for validation of the installed revision.

## 0.1.3 review follow-up and deferred symbolic work (2026-09-27)

The full-codebase review reproduced nonfinite comparison acceptance in the
imaginary mathematical checker and silent shape truncation in the separate
exact-example helpers. The [follow-up record](releases/v0.1.3.md#review-follow-up)
records the corrected input boundaries, diagnostics and regression evidence.
All 43 Python tests (including 15 added regressions), 52 imaginary mathematical
checks and 39 exact assertions pass. The exact suite and fixtures are included
in documentation CI. Rust/Lean source is unchanged and was not revalidated in
this follow-up; earlier candidate archives predate the fixes.

At the user's request, further symbolic-kernel development and production
integration are [future roadmap work](../ROADMAP.md#future-work-symbolic-semantic-kernel)
with no target release selected. The existing architecture, research prototype
and regression tests are retained. The production finite checker still uses
dense matrices; scalable symbolic checking remains a prerequisite for future
size generalization, not a delivered production guarantee.

## 0.1.3 semantic-system design and independent implementation (2026-09-27)

Following review verification, the user requested a first-principles system
design and an independent implementation focused on semantics. The
[architecture](symbolic-contract-architecture.md) fixes separate required
meaning, actual implementation, evidence, ownership/effects and encoded-entry
judgments. Exact pure realization is distinguished from block, instrument,
approximation and algorithm contracts. It records primary-source comparisons,
trust boundaries and gates G013-S0–S3.

The [non-published research package](../research/semantic-kernel/README.md)
implements an initial exact-pure slice: symbolic type/term/proof DAGs,
structural encoding matching, bounded exact leaves, sequence/tensor/qualified
adjoint/control/repetition, and independent binding to a supported actual
raw-IR subset. An immutable client requirement fixes the meaning behind term
IDs before proof production; a producer may only extend that frozen graph.
Its actual 128-bit local-Z regression uses a single 1-bit exact
leaf (maximum matrix dimension 2); the remaining identity frame is symbolic.
This removes global dense materialization in the tested proof path while
preserving the production finite checker unchanged.

The new Lean module adds 20 general semantic lemmas. Full build passed with
1,457 jobs, and the warning-as-error axiom audit passed for 577 declarations.
The [ledger](lean-resource-proof.md) records exact assumptions and the limited
derivation induction. These are mathematical rule proofs, not proofs that the
Rust kernel, importer, frontend or backend implements those rules correctly.
Final Rust, document and package evidence is in the
[release record](releases/v0.1.3.md#local-candidate-validation).
The final prototype passes 43 tests on both supported Rust toolchains,
including one permanent 5,425-case exact differential test. Frozen required
meaning, actual raw-IR binding and the narrow structural proof calculus were
reviewed separately. The complete source archive also reproduces all 43 tests.

Production source correspondence, entry establishment and certified release,
transformation witnesses, portable evidence and generalized algorithms remain
future work. No source feature or new production public API is adopted by this
experimental package. Version selection and this work do not publish a release.

## 0.1.3 initial review verification and maintenance candidate (2026-09-27)

This entry records the earlier maintenance-only step; the subsequent semantic
research and updated validation are recorded above.

The user selected 0.1.3 and requested verification of the supplied v0.1.2
review. Both project manifests and current-version summaries are synchronized.
The [review record](reviews/v0.1.2.md) confirms the tagged baseline, reproduces
silent matrix truncation, checks all six draft-contract claims, and identifies
the exact-checker's bounds and dense logical composition. Tagged-source shape
auditing found no dimension violations in the existing 52 checks.

The auxiliary matrix helpers now reject malformed/incompatible shapes with
`ValueError`, also for comparisons used in negative checks. Fourteen regression
tests pass and run in documentation CI. No Rust implementation, public contract,
Lean declaration, capacity, toolchain requirement or dependency changed.

The user emphasized that dense logical multiplication is fundamentally unable
to scale. The [requirements index](imaginary-v1/requirements.md#scaling-prerequisite-for-r14)
now records symbolic meaning/encoding/evidence composition without whole dense
operators as a prerequisite for generalization, together with explicit first-QPE
angle and checking decisions. The architecture remains unimplemented; existing
finite composition does not establish this generalized requirement.

Fresh local checks passed on macOS aarch64: Rust 1.98.1 and 1.85.0 each passed
258 tests and all-target Clippy with warnings denied; fmt passed. Lean 4.30.0
built 1,212 jobs and passed the 527-declaration warning-as-error audit with only
`propext`, `Classical.choice`, and `Quot.sound`. Both 14-test Python suites, 52
design checks and 39 exact assertions passed. All ten CLI projects checked and
ran; Shor produced factors 3 and 5 with success/retry probability 1/2 each.
Final package/document checks are recorded in the
[0.1.3 release notes](releases/v0.1.3.md#local-candidate-validation).

The exact v0.1.2 release CI was independently inspected and confirms all four
jobs succeeded, including 259 Linux MSRV tests and Lean build/audit. Its extra
Linux-only CLI test was not rerun locally. This historical CI does not validate
0.1.3. No 0.1.3 commit, tag, push, hosted release or registry publication has
been performed. Existing general implementation/proof obligations remain open.

## 0.1.2 release procedure and publication record (2026-09-27)

The user authorized release through publication. The release date is
2026-09-27 (JST); current summaries and the English release notes are finalized
for that release. GitHub main requires a PR, an up-to-date base, resolved
conversations, and `rust`, `rust-msrv`, `lean`, and `docs` checks. No bypass
actor is configured. The v* rules prohibit updates and deletions of release
tags. These active rules were checked before release work.

The release procedure verifies CI on the merged main commit and packages and
rebuilds its clean source before annotated tagging, tag push, and GitHub
publication. The [hosted release](https://github.com/MGYamada/Qleisli/releases/tag/v0.1.2)
records the exact commit, PR, CI, archive verification, and completed operations.
Registry publication is outside this release. Version/date metadata alone does
not prove that publication occurred. The preparation/translation records below
retain their original scope, test counts, and then-pending steps.

<a id="english-documentation-consolidation"></a>

## English documentation consolidation (2026-09-27)

The ten current Japanese documents in the [translation inventory](documentation-map.md#translation-inventory)
now have English editions: README, roadmap, design philosophy, AI-era goal,
algorithm-structure goal, algorithm corpus, quantum-language requirements,
standard-library roadmap, quantum bookkeeping, and the finite-IR paper proof.
Each identifies its authority and distinguishes adopted principles, proposals,
specified behavior, implementation, finite testing, paper proofs, and Lean
results. The current English specifications and six imaginary-v1 drafts are
cross-referenced; concrete future syntax/APIs remain undecided.

Legacy heading anchors, mathematical premises, code/equations, primary-source
links, historical dates/counts, and remaining trust boundaries are preserved.
Stale summaries are clarified against existing specification records: the
original restricted auxiliary form is separate from the later explicit
semantic-contract form, and historical partial implementation is separate from
the achieved bounded v0.1 profile. No language rules, public APIs, Rust/Lean
implementation, dependencies, capacities, or toolchain requirements changed.

Translation and independent review are complete. Reviewers compared the ten
English editions with their Japanese baselines, including every historical
roadmap paragraph, and checked the current-specification/future-design boundary.
The review preserved theorem premises and limitations, C01–C20, S1–S8, A0–A4,
L0–L5, contract fields, and proposed-API status. One ambiguous phrase about
retained partial-discard/reset tests was clarified; new status-record anchors
were added before final link checking.

Checks performed for this documentation step on macOS aarch64:

| Check | Result and scope |
| --- | --- |
| Translation inventory | All ten documents have English prose; all 102 original heading/explicit-anchor targets and all original link destinations are retained. Remaining Japanese prose is operational guidance, historical conformance records, and glossary terms. |
| Documentation checker | `python3 scripts/test_check_docs.py`: all 14 tests passed. `python3 scripts/check_docs.py` passed local links, anchors, Rust declaration/test references, and Lean-root reachability. `git diff --check` passed. |
| Mathematical fixtures | `python3 scripts/check_semantic_contract_examples.py`: 39 exact rational/algebraic assertions passed. `python3 scripts/check_imaginary_v1_examples.py`: 52 finite convention checks passed. Neither compiles imaginary source or proves the implementation. |
| Source candidate | `CARGO_TARGET_DIR=/private/tmp/qleisli-v012-rust cargo package --allow-dirty --offline`: generated and rebuilt the 156-file candidate. All 55 current documentation/license/notice files in the archive were compared byte-for-byte with the working tree, including the new documentation map and translated documents. |

The earlier Rust execution-test/Clippy, Lean build/axiom-audit, and CLI results
below are retained as history; those suites were not rerun or credited as new
translation results. Package verification did rebuild the unchanged Rust code.
This is a local uncommitted candidate, not clean-release-commit validation.
The version remains 0.1.2 in preparation. No commit, tag, push, hosted release,
or registry publication was performed.

### Follow-up review correction (2026-09-27)

Corrected the [corpus review summary](imaginary-v1/review.md) to describe odd
QSVT as mapping right singular vectors to left singular vectors, matching
the unchanged `L p(Sigma) V†` equation and circuit in the draft. Document
references and `git diff --check` passed. This wording correction adds no
implementation or proof claim; Rust/Lean tests were not rerun.

## 0.1.2の設計成果物とローカル候補検証（2026-09-27）

ユーザーの指示に従い、P012-0の英語仕様整備を先に完了してから、v0.1.2の設計・文書候補を完成させるgoalを設定した。[QPE](imaginary-v1/qpe.md)、[Grover](imaginary-v1/grover.md)、[amplitude estimation](imaginary-v1/amplitude-estimation.md)、[Shor](imaginary-v1/shor.md)、[quantum walk](imaginary-v1/quantum-walk.md)、[QSVT](imaginary-v1/qsvt.md)の初稿を作成した。[索引](imaginary-v1/README.md)、[共通要求R01〜R14](imaginary-v1/requirements.md)、[意味論レビュー](imaginary-v1/review.md)から各題の契約・能力・所有権・効果・位相・補助回収・精度・成功／失敗・古典処理・IR方針・未解決事項を追跡できる。

**P012-0〜4を完了し、v0.2.0以前の「初稿の存在と要求記録」という前提を満たした。** コードはすべて仮想・未コンパイルである。QPEの残存標的と参照系、Groverの反射符号とAEの補数反例、Shorの全空間算術・候補検証・実行失敗、Szegedy walkの反射順序、QSVTの偶奇・実多項式selector・成功／失敗instrumentをレビューした。測定結果を`CWord`に統一し、ホストの失敗伝播を本文にも明示した。新構文・標準API・一般サイズの実装を採用したのではなく、V1-C1〜C5と一般的な健全性証明は未完了のままである。

**P012-5はmacOS arm64でローカル完了。** 今回の0.1.2作業ツリーで実施した検査:

| 対象 | 結果 |
| --- | --- |
| Rust 1.98.1 | 新しいtargetディレクトリで`cargo test --all-targets --offline`全258件、全target Clippy（警告をエラー扱い）、fmtが成功 |
| 最低Rust 1.85.0 | 既存の隔離toolchainと別の新しいtargetで全258件・Clippyが成功。既定toolchainは変更しない |
| Lean 4.30.0 | `lake build`成功（1,212 jobs）。`lake env lean -DwarningAsError=true Audit.lean`で527宣言を監査し、公理は`propext`・`Classical.choice`・`Quot.sound`のみ |
| 文書と数学 | 文書検査器14件、参照・差分検査が成功。既存の厳密数学例39件、新しい独立した有限数学チェック52件が成功 |
| 実行例 | CLI全10プロジェクトのcheck/run成功。Shorは成功枝で3と5、理想成功確率1/2・再試行確率1/2を確認 |
| 配布候補 | `cargo package --allow-dirty --offline`で155ファイルの候補を生成・展開後に再ビルド。LICENSE・NOTICE、6初稿と索引／要求／レビューの計9文書、英語枠組み、検査スクリプト等の同梱を確認 |

[新しい数学チェックスクリプト](../scripts/check_imaginary_v1_examples.py)は、Fourier行列との全成分照合、QPEの参照系を含む分岐、増幅、位数候補、walk、QSVTの小行列を確認する。文書CIにも組み込んだ。Pythonの有限モデルの成功は、仮想コードのパース・型検査・IR生成・実行・Lean証明を意味しない。浮動小数点の近似照合を厳密な補助ゼロ復帰の証拠にしない。

**P012-6は未実施・未公開。** Linux専用CLI検査とリモート必須CI、cleanなリリースコミットからの最終梱包、注釈付きタグ、push、GitHub公開は残件。今回コミット・タグ・push・公開・レジストリ配布はしていない。ローカルの未コミット候補検証と公開可能なコミットの確定を区別する。以下の版選択・工程0の記録は、その時点の履歴として保持する。

## 0.1.2工程0: 将来に向けた英語の言語仕様整備（2026-09-27）

ユーザーの追加指示に従い、goal設定と初稿作成に先立ってP012-0を整備した。[英語の言語設計枠組み](language-evolution.md)に現行規範・将来案・仕様選定・実装・検証・証明の境界、共通の仮想記法、所有権・位相・アクセス能力・厳密な補助回収・instrument／誤差の区別、拡張の記録要件を記した。言語仕様と文法の古いv0.1未完記述を現在の有限SC＋FC到達へ合わせ、stdlibの将来候補と用語集を接続した。現行の文法・受理規則・APIは変更していない。文書参照検査と`git diff --check`が成功した。

## 0.1.2の版選択とロードマップ（2026-09-27）

ユーザーの指定により、Rustの`Cargo.toml`とQleisli自身の`lean/lakefile.toml`を**0.1.2**へ更新した。[英語のリリース計画](releases/v0.1.2.md)と[日本語の工程表](../ROADMAP.md#v012-release-roadmap)を作り、README・作業指針・変更履歴・版方針・到達条件の現行版表示をそろえた。0.1.1の変更と検証実績は履歴として保持し、今回の成果に再計上しない。

**P012-1（版と計画）は完了、公開準備中・未公開。** 0.1.2の予定成果物は、仮想Qleisli 1.0のQPE・Grover・amplitude estimation・Shor・quantum walk・QSVTの初稿、各題の意味契約、共通要求の索引、意味論レビューである。P012-2〜4は未実施であり、予定パスを示しただけでは成果物や前提完了の証拠にならない。6題と要求をそろえてからv0.2.0の仕様範囲を選び、一般化の実装と検証へ進む。V1-C1〜C5、有限コアの保証範囲、未完の一般証明は維持する。

今回の版・文書変更で実施した検査:

- `cargo metadata --no-deps --format-version 1 --offline`でRust版0.1.2・Apache-2.0・最低Rust 1.85を確認。Lean版0.1.2とmathlib依存v4.30.0を確認し、`cargo generate-lockfile --offline`で更新したローカルの`Cargo.lock`も0.1.2と照合した。lockfileは従来どおりGit管理対象外。
- `cargo package --list --allow-dirty --offline`が成功し、LICENSE・NOTICE、新しいリリース計画、stdlib、例、Leanソースを含む候補一覧を確認。アーカイブの生成・展開後の再ビルドは未実施。
- `cargo fmt --check`、文書参照検査、文書検査器自身の**14テスト**、`git diff --check`が成功。

Rust実行テスト・Clippy、Lean build／公理監査、厳密数学例・CLI例・Shorは今回は再実行していない。完成した初稿を含む最終候補の検証をP012-5、cleanなリリースコミットの梱包・必須CI・注釈付きタグ・push・GitHub公開をP012-6として残す。今回、コミット・タグ・push・公開リリース・レジストリ配布は行っていない。版選択も文書検査の成功も、仮想コードの実装・検証や健全性証明の完了を意味しない。

## 0.1.1のリリース手順とGitHubルールセット（2026-09-27）

ユーザーのリリース指示を受け、GitHubの有効なルールセットを確認した。[main保護](https://github.com/MGYamada/Qleisli/rules/24055699)はPR、最新baseへの追従、`rust`・`rust-msrv`・`lean`・`docs`の4検査、レビュー会話の解決を要求し、承認数は0、迂回権限はない。[リリースタグ保護](https://github.com/MGYamada/Qleisli/rules/24055722)は`v*`の更新・削除を禁止し、迂回権限はない。従来形式のbranch protectionは未設定だが、rulesetによる保護は有効である。

リリース日は2026-09-27（JST）とし、文書を公開用に確定した。作業ブランチのPRを通し、マージ後のmainコミットに対するCIとcleanな状態での梱包・再ビルドを確認してから注釈付き`v0.1.1`タグを作成する。GitHubソースリリースに実際のコミットID・PR・CI・検証結果を記録する。[公開記録](https://github.com/MGYamada/Qleisli/releases/tag/v0.1.1)がタグと公開状態の確認先であり、この文書の版や日付だけでは公開済みとしない。レジストリ配布は別工程とする。以下の未実施という記述は各工程時点の履歴として保持する。

## 0.1.1追加レビュー: 漏出警報のアンダーフロー修正（2026-09-27）

補助軸の振幅が`[1e-160, 1e-164]`のとき、相対漏出は約`1e-8`なのに、二乗後の漏出質量が0へ丸められ警報しない問題を再現した。新しい回帰検査は修正前に失敗し、修正後に成功した。これは内部状態を直接与えた数値診断の再現であり、正常な検証済みプログラムからの発生や厳密証拠の誤受理を示すものではない。

[シミュレータ](../src/sim.rs)は、診断の比率計算に限り実部・虚部を最大絶対座標で割ってから二乗する。保存する振幅・純粋解放の証拠・閾値`1e-12`は維持し、元の全質量による非有限値とオーバーフローの検出も残した。全ゼロの成分を受理し、最小の正の非正規化数でも漏出を検出する。新しい[回帰検査](../src/sim/tests.rs)は実部／虚部、閾値の両側、subnormalな確率・全確率のゼロ丸め、投影後の振幅ビットの不変性を含む。既存検査も実部／虚部のNaN・正負の無限大・有限振幅からの二乗オーバーフローを確認する。

修正後のmacOS検査: コンパイラとClippyを固定したRust 1.98.1／1.85.0で、それぞれ全target **258件成功**、Clippy成功。fmt、文書参照検査、`git diff --check`も成功。全10個のCLI例とShorホスト例を再実行し、未コミットの0.1.1配布候補を再生成・再ビルドした。公開仕様・変更履歴・リリース記録を更新した。変更のない厳密数学例・文書検査器自身の14テスト・Lean build／公理監査は再実行せず、以下の前回記録を保持する。Linux CI、cleanなリリースコミットの梱包、タグ・push・公開は未実施。

## 0.1.1の実装完了とローカル候補検証（2026-09-27）

ユーザーの指示によりv0.1.1実装のgoalを設定し、[ロードマップ](releases/v0.1.1.md)のP011-1〜3を完了した。既に実装した互換修正を最終独立レビューで再確認した。実際のMSRV検査では`tests/function_evidence.rs`の2式にClippyの優先順位警告が3件出たため、ビット演算へ明示的な括弧を付け、意味を保って修正した。キャッシュは不変のプロジェクト内に限定され、外部証拠の厳密な結合検査、公開API、意味契約・位相・所有権・容量を維持する。診断メタデータと数値漏出検出を受理の証拠として使わない。

**版0.1.1の作業ツリー**で今回実施した結果:

- macOS aarch64／Rust 1.98.1、新規targetで`cargo test --all-targets --offline`: **257件成功**。`cargo fmt --check`と全targetのClippy（`-D warnings`）も成功。
- 最低対応Rust **1.85.0**を一時ディレクトリへ隔離導入し、コンパイラ・rustdoc・Clippyを絶対パスで固定した別の新規targetで全target **257件成功**、Clippyも成功。実行したコンパイラとClippyの版を照合し、ユーザーの既定toolchainや永続PATHは変更しなかった。
- 文書検査器**14件**、文書参照・宣言検査、厳密な数学例**39件**、`git diff --check`が成功。
- Lean **4.30.0**で`lake build`成功（1,212 jobs）。警告をエラーとする公理監査は**527宣言**を検査し、依存公理は`propext`・`Classical.choice`・`Quot.sound`のみ。証明ソースや依存版は変更していない。
- 全**10個**のCLIプロジェクトを検査・実行した。意味契約・関数契約はともに`101: 1.000000000000e0`。Shorホスト例は成功時に因数3と5を返し、成功確率1/2・再試行確率1/2を確認。
- `cargo package --allow-dirty --offline`で**143ファイル**の0.1.1候補を生成し、展開後の再ビルドも成功。LICENSE・NOTICE、stdlib、新しい回帰検査・文書、例、Lean証明を含むことを確認。

**実装とローカル候補検証は完了、リリースは未公開。** 未コミットの候補アーカイブを検証した結果であり、P011-4のcleanなリリースコミットからの最終梱包とは区別する。macOSで実行しないLinux専用CLI 1件とリモートCIは残件。最終ノートを含むコミット、注釈付きタグ、push、GitHub公開、レジストリ配布は行っていない。有限テストと既存Leanモデルの検証は、Rust全受理経路・ソース対応・一般的な量子的健全性の証明完了を意味しない。仮想1.0コード群は引き続きv0.2.0以前の前提であり、未作成。

## 0.1.1の版選択とリリース計画（2026-09-27）

ユーザーの指定により、Rustの`Cargo.toml`とQleisli自身の`lean/lakefile.toml`を**0.1.1**へ更新した。[英語のロードマップとリリースノート草案](releases/v0.1.1.md)を作成し、[日本語の工程表](../ROADMAP.md#v011-release-roadmap)、変更履歴、README、作業指針、バージョン方針を整合した。以下のClaudeレビューで確認した互換修正を収録する。依存版、公開構文・API・容量上限・最低toolchainは変更しない。

状態は**公開準備中・未公開**。版変更前のRust 257件等の成功を履歴として保持し、最終候補のRust・Lean・例・配布物検査、Linux／MSRV CI、検証済みコミットと注釈付きタグ・push・GitHub公開を残件として分けた。仮想1.0コード初稿はv0.2.0以前の前提として維持し、この互換保守版の必須条件にはしない。

本工程の検査: `cargo metadata --no-deps --format-version 1 --offline`でRust版0.1.1・Apache-2.0・最低Rust 1.85を確認し、Lean版0.1.1・mathlib依存v4.30.0との整合も確認した。生成される`Cargo.lock`の自前packageも0.1.1。`cargo package --list --allow-dirty --offline`の143ファイルにLICENSE・NOTICE、新しいロードマップ／レビュー記録・回帰検査、stdlib、代表例とLeanソースを含むことを確認した。これは配布アーカイブの生成・再ビルド成功を意味しない。`cargo fmt --check`、文書参照検査、文書検査器14件、`git diff --check`は成功。今回の版・文書変更ではRust実行テスト・Clippy・Lean build／公理監査は再実行していない。コミット、タグ作成、push、公開リリース、レジストリ配布も未実施。

## Claudeによるv0.1.0レビューの照合と保守修正（2026-09-27）

[英語のレビュー対応記録](reviews/claude-v0.1.0.md)に、ユーザー提供の指摘ごとの再現・仕様照合・適用・保留を記録した。変更されないソース／raw証拠を契約の再利用ごとに比較・課金する問題を修正し、契約不一致のソース位置と厳密な反例成分を診断に追加した。公開エラーvariantは維持し、構文エラーの説明にはparse由来を明示する。補助解放前の数値漏出検出、厳密算術の境界の強化、独立した実行経路の差分検査も追加した。

`run`による全宣言の検査、微小な正の確率の保持、契約の検査済み抽出回路による実行は現行仕様どおりと確認した。公開IR削除・共有呼出しIR・新構文／標準APIは将来の設計課題に記録し、仮想1.0コードを先に書く前提を維持する。このレビュー時点では版を0.1.0に保ち、変更を`Unreleased`へ記録した。その後、上記の0.1.1へ収録した。

検査結果（macOS／Rust 1.98.1、新しいCargo targetディレクトリ）: Rust全target **257件成功**、fmt・Clippy・文書検査・文書検査器14件・`git diff --check`が成功。意味契約・関数契約のCLI例はともに`101: 1.000000000000e0`を返した。追加差分検査は96個の生成回路と16個の物理補助付き実装を含む。Linux専用CLI検査とRust 1.85はローカル未実行。MSRV CIにClippyを追加したが、リモート実行成功とは扱わない。Leanソースは変更せず、build／公理監査は再実行していない。一般的な健全性証明・リリース公開の完了を意味しない。

## v0.2.0以前の前提: 仮想Qleisli 1.0コードの先行作成（2026-09-27）

ユーザーの指示により、[英語正本の前提条件](release-milestones.md#pre-v020-imaginary-v1-code)を採用した。QPE・Grover・amplitude estimation・Shor・quantum walk・QSVTの理想コードと必要な意味契約・能力・未解決事項を先にそろえてから、v0.2.0向けの一般化・新機能実装とリリースへ進む。仮想コードはコンパイルできなくてもよく、設計の進展に応じて改訂する。

**状態: 方針は採用済み、初稿コード群と要求の索引は未作成・前提は未達成。** 完了時には本台帳に各成果物へのリンクを記録する。この変更は開発順序の文書化であり、仮想構文・APIの確定、実装、検証、証明の完了やv1達成を意味しない。この方針採用時点では版を0.1.0に保ち、V1-C1〜C5、有限コアの保証と既存の証明課題を維持した。

文書検査（2026-09-27）: `python3 scripts/check_docs.py`と`git diff --check`が成功。文書のみの変更のため、Rustテスト・Lean build／公理監査は再実行していない。

## 0.1.0のリリース検査（2026-09-27）

初回ソースリリースの内容を[英語のリリースノート](releases/v0.1.0.md)と[変更履歴](../CHANGELOG.md)にまとめた。公開先は`MGYamada/Qleisli`のGitHub Releasesと注釈付き`v0.1.0`タグとする。タグは検証対象の変更をすべて含むコミットへ付け、実際のコミットID・CI・公開状態はGitHubのリリース記録で確認する。レジストリ配布は別の操作である。

直前の最終レビューでは、macOS／Rust 1.98.1でRust全245件、fmt、Clippy、文書検査器14件、文書参照検査、厳密な数学例39件、Lean buildと527宣言の公理監査、Cargo配布パッケージの生成と再ビルドが成功した。意味契約・関数契約の両例は`101: 1.000000000000e0`、Shorホスト例は因数3と5・成功確率1/2・再試行確率1/2を確認した。深く不正なraw IRの拒否も別プロセスの追加照合で確認した。一般の健全性証明とは区別する。

その後の変更は設計メモ、リリース文書、Cargoの公開先メタデータとCIであり、Rust／Leanの実装は変更していない。Linux専用CLIの1件と最低対応Rust 1.85.0はローカルでは未実行である。リリースCIに1.85.0での全targetテストを追加し、Linux上のRust・文書・Leanの全ジョブ成功を公開条件とする。以下の記録は各工程時点の履歴として保持する。

## 0.1.0のライセンス・バージョン方針（2026-09-27）

利用者の指定により基準版を`0.1.0`とし、Qleisli自身のコード・標準ライブラリ・例・証明・文書にApache-2.0を適用した。[LICENSE](../LICENSE)、[NOTICE](../NOTICE)、[貢献方針](../CONTRIBUTING.md)を追加し、Cargoのライセンスメタデータを設定した。RustとLeanのプロジェクト版は既に`0.1.0`で一致している。

[英語のバージョン方針](versioning.md)と[AGENTS.md](../AGENTS.md)に、0.xの互換修正はPATCH、新機能・破壊的変更はMINOR、1.0以降は通常のSemVer増分を使うと記した。位相・軸順・所有権・効果・証拠の前提も互換性に含め、仕様違反の誤受理修正と新しい制限を区別する。[CHANGELOG.md](../CHANGELOG.md)を設け、公開済みタグ・配布物の不変性、リリース検査と正確な状態記録を定めた。

この工程はライセンス・メタデータ・文書の整備であり、言語の受理規則やRust／Leanの実装は変更していない。`cargo metadata --no-deps --format-version 1 --offline`で`0.1.0`／`Apache-2.0`を確認し、`cargo package --list --allow-dirty --offline`でLICENSE・NOTICEの梱包対象を確認した。生成されたPythonキャッシュが配布候補に混じっていたため、Gitの除外設定に追加した。文書検査、文書検査器の14テスト、`git diff --check`は成功。Rustの実行テスト・Lean build／公理監査は本工程では再実行していない。Gitタグ、push、公開リリース、レジストリ配布は未実施。

## v0.1: 宣言した有限プロファイルの到達記録（2026-09-27）

[V01-C1〜C6](release-milestones.md#v01-minimum-semantic-contracts)の仕様、独立した証拠検査、実ソースと最終IRへの結合、関数境界での再利用、実装交換、受理・拒否検査を接続した。v0.1の宣言した有限プロファイルを達成したと記録する。これは公開リリースの配布操作や、Rust処理系全体の形式証明の完了を意味しない。north starは「人間が量子アルゴリズムについて考えるときの言葉と、プログラムを書くときの言葉を一致させる」とし、Shor・QPE・Groverはv1でその方向を評価する具体的な到達条件として維持する。

| 条件 | 到達根拠 |
| --- | --- |
| V01-C1 | [SC仕様](semantic-contracts-v0.1.md)は型木、等長な符号化、固定した論理作用、位相、入口の前提を定義。[FC仕様](function-contracts-v0.1.md)は正確な単一量子入出力と恒等な公開符号化を持つ関数境界を規定。一般の符号化された実行状態を主張するAPIは提供しない。 |
| V01-C2 | [独立した厳密検査核](../src/contract/mod.rs)と[19テスト](../tests/semantic_contracts.rs)が原始等式・逐次／テンソル合成・前提付き逆／制御・全列比較を扱う。SC/FC規則の条件付き紙上導出と、Rust実装の一般的な正しさを区別する。 |
| V01-C3 | [FunctionEvidence](../src/contract/function.rs)は実装と仕様のraw IRを独立検証・抽出して比較し、両raw snapshotと正確なソース依存先を保持。[18テスト](../tests/function_evidence.rs)で位相、非対称な述語、出力順、閉じた古典分岐、補助、共有予算、依存証拠、改変拒否を検査。最終IRのContract actionは逆・制御・反復・軸移送の後も証拠を保持する。 |
| V01-C4 | [14ソーステスト](../tests/certified_source.rs)と[実行例](../examples/semantic_contracts/README.md)が位相オラクル、補助H;H、データ／補助同時Xを同じ厳密等式で検査する。任意の参照系への保証は演算子等式に恒等写像をテンソルする数学的帰結であり、有限の数値実行を一般証明としない。 |
| V01-C5 | [apply_contract](../src/frontend/compile/lower/function_contract.rs)が利用側の固定した仕様を要求。[16ソーステスト](../tests/function_contracts.rs)には同一の利用側で直接Z・従来の補助計算・意味契約付き補助計算を交換し、制御と相関参照を検査するケースがある。通常呼出し・入れ子・逆・反復は同じ不変証拠を再利用する。[実装交換例](../examples/function_contracts/README.md)も実行可能。 |
| V01-C6 | SC/FC/ソースの各検査が誤位相・補助のみX・述語／軸／型／符号化の不一致、入口証拠欠如、不正な逆／制御の前提、古いソース／依存証拠、所有権の紛失／重複と容量超過を拒否する。`Q<Unit>`の所有権と制御で現れるスカラー位相も含む。 |

新しい`apply_contract`は言語形式であり、新予約語となる。対象は通常の宣言済み`unitary Q<A> -> Q<A>`関数で、入力式を先に一度評価し、その後の名前隠蔽規則に従って両対象を解決する。対象を封印ゲート、古典ポートや別の型木の関数へ暗黙に拡張しない。

公開関数は6bit、型木128ノード・深さ32、回路1,024ステップ、関数依存深さ32、関数ごとの展開量100万に限定する。ソース同一性は128記録・合計1 MiB・各名前4,096byte以内。raw操作と分岐にも[FCの個別上限](function-contracts-v0.1.md#3-independent-whole-function-evidence)があり、全上限を同時に満たせるとは限らない。独立検査は共有する厳密作業予算を使い、ソース側は1千万を供給する。証拠の比較は発行時の同一性を用い、共有依存グラフを再帰展開して比較しない。

独立レビューで、証拠を共有する大きな部品の反復による実行量増加を確認し、`SimulationLimits::max_execution_steps`を追加した。既定100万の予算を実行全体・古典分岐・全アンサンブル成分で共有し、関数証拠の展開前にその推移的な費用を計上する。これは実行ステップの上限であり、浮動小数点演算回数や実時間の保証ではない。

検査結果（macOS、2026-09-27）:

- `cargo test --all-targets --quiet`: **245件成功**。直前の211件に関数証拠18件とソース統合16件を追加。既存Linux専用CLI 1件はこの環境では未実行。
- `cargo fmt --check`、`cargo clippy --all-targets -- -D warnings`: 成功。
- `python3 scripts/test_check_docs.py`: **14件成功**。`python3 scripts/check_docs.py`と`git diff --check`も成功。
- `examples/function_contracts`をCLIで検査・実行し、`101: 1.000000000000e0`を確認。
- Leanは本工程で変更せず、ビルド・公理監査を再実行していない。以前からの作業ツリーのLean変更と、その過去の検査記録は保持した。

残る信頼境界は厳密算術、検証器、独立した回路抽出、ソースから実際のIRへのRust実装対応である。ソースsnapshotは由来の照合であり、その翻訳の正しさの証明ではない。証拠付き呼出しの実行は検査済みの回路を用い、補助領域を証明済みの論理作用へ置換できる。元の物理raw本体は証拠内に保持する。一般の符号化された状態ハンドル、サイズ／操作パラメータ、観測・近似契約、証拠のシリアライズ、外部バックエンド、v1の3アルゴリズムの一般化は後続である。

以下の件数と未達記述は、各工程時点の履歴として保持する。

## v0.1: 有限意味契約の最初の実装経路（2026-09-27、関数境界の実装前）

v0.1の最低条件V01-C1〜C6をgoalとして設定し、[有限意味契約の英語仕様](semantic-contracts-v0.1.md)、厳密算術、独立検査、ソース拡張と参照実行を接続した。プロジェクトのnorth starは「人間が量子アルゴリズムについて考えるときの言葉と、プログラムを書くときの言葉を一致させる」とする。Shor・QPE・Groverは、v1でこの方向を評価する具体的な到達条件として維持する。

| 実装 | 検査対象と根拠 |
| --- | --- |
| [厳密算術](../src/contract/exact.rs) | `Z[ζ8,1/2]`の正規化された係数、checked i128算術、最大64次元の行列と作業予算。9単体テスト。浮動小数点の一致を証拠にしない。 |
| [契約検査核](../src/contract/mod.rs) | 型木付き符号化、等長性、正確な位相、全列・全出力行での`U E_in=E_out u`。不変な証拠から恒等・合成・テンソル・前提付き逆／制御を構成する。[19件の回帰](../tests/semantic_contracts.rs)は誤位相・軸・符号化・入口証拠・不正逆／制御・証拠取り違え・容量とraw IRの所有権を含む。 |
| [ソース拡張](../src/frontend/compile/lower/certified.rs) | `with_computed(q,f,u){\|d,a\| body}`を言語形式として追加。独立した所有権スコープでWを生成し、明示したuとともに`CertifiedCompute`へ保持。[14件のソース回帰](../tests/certified_source.rs)で位相オラクル・補助H;H・同時X・相関参照・制御・逆・同じ利用側での実装交換・拒否境界を検査。 |
| [独立IR検証](../src/verify.rs)と[参照実行](../src/sim.rs) | 実際のW/uとpredicateを再検査し、新規補助ID・線形source tokenを確認。実行はcompute/W/uncomputeを行い、厳密な証拠のあるゼロ軸だけを除く。 |

新しい形式は最大5データbitと補助1bit、各回路1,024ステップ、raw検査当たり1千万の保守的な厳密演算予算に限定する。容量超過は拒否する。既存2引数形式のZ/T限定は維持する。公開Rust APIの`check_entry`は証拠の境界同士の照合であり、実行状態が符号空間にある証明ではない。ソース形式の入口はfreshな補助の準備と計算によって成立させる。

独立レビューで、新ASTによるパーサのスタック使用量増加と、深い未検証型の拒否後の再帰的破棄を修正した。前者は追加識別子のBox化と既存深さテスト、後者は反復的破棄と10万段・2 MiBスタックの回帰で確認した。

検査結果（macOS、2026-09-27）:

- `cargo test --all-targets --quiet`: **211件成功**。従来169件に上記9+19+14件を追加。既存Linux専用CLI 1件はこの環境では未実行。
- `cargo fmt --check`、`cargo clippy --all-targets -- -D warnings`: 成功。
- `python3 scripts/test_check_docs.py`: **14件成功**。文書参照検査と`git diff --check`も成功。
- [実行例](../examples/semantic_contracts/README.md)をCLIで検査・実行し、`101: 1.000000000000e0`を確認。
- Leanは変更せず、本工程でビルドや公理監査を再実行していない。SC規則の局所紙上導出とRust実装の一般的な形式検証は区別する。

**v0.1は未達成、goalは継続中。** 次はV01-C3/C5の公開関数契約・依存先・実装を束ねる境界と、静的変換後の最終IRに対応証拠を持たせる経路を完成させる。現在の通常呼出しは展開と再検査であり、同じ利用側での交換テストだけでは部品証拠の再利用を達成したことにならない。

## v0.1の最低条件とv1の到達条件の採用（2026-09-27、実装前の記録）

[英語のリリース条件](release-milestones.md)を正本として、v0.1は意味契約 `U E_in = E_out u` の有限証拠・合成・関数境界での再利用・実装交換・最終IRまでの独立検査を最低条件に採用した。v1は、Shor・QPE・Groverが教科書のアルゴリズム構造のまま読める、実際にコンパイル・実行・検証できる実装をnorth starにする。本節は日本語の補助記録である。

両目標は**未達成**。V01-C1〜C6の統合した仕様・検査経路は未実装であり、[提案レビュー](semantic-contract-proposal-review.md)の39件の厳密な数学的照合、既存の有限回帰例、Cargoの`0.1.0`、契約台帳の形式v1から達成を推論しない。V1-C1〜C5は、共通QPEを使うShorの古典処理・因数検証・再試行まで含む。固定例や疑似コードだけでは達成としない。

ロードマップ、README、作業指針、設計目標と標準ライブラリ計画を同じ順序へ整合した。今回の変更は文書のみで、現行v0の受理規則、Rust実装、Leanの証明範囲を変更しない。以下の処理系・Leanの検査結果は各工程時点の履歴として保持する。

今回の文書検査は `python3 scripts/check_docs.py`、`python3 scripts/test_check_docs.py`（14件）、`git diff --check` が成功。Rust・Leanの検査はこの方針変更では再実行していない。

## SPEC-4: スコープ射影の実装対応と局所証明（2026-09-27）

直近の処理系・Leanの検証結果を本節に記録する。[状態対応の英語文書](lowering-state-refinement.md)で、Rustの値・環境・registerから境界関係BCへの対応を整理した。ブロック終了処理を非公開の[`close_scope`](../src/frontend/compile/lower/scope.rs)へ切り出し、同じ場合分けを[Leanモデル](../lean/Qleisli/Scope.lean)で証明した。言語の受理規則・公開APIは変更していない。

機械検証した範囲は、古典束縛の復元、消費済み束縛の非復活、入口の名前集合の保存、導入・再束縛した量子所有者の未返却の拒否、成功時の各名前と有限名前列の量子所有権リストの保存。`Q<Unit>`も所有権を持つ。一般のlookup関数と集合によるモデルであり、Rustの有限mapとの対応、実行経路が渡すsnapshotと再束縛集合、暗黙frameと発行済みID履歴の健全性までを機械検証したものではない。

| 検査 | 範囲 |
| --- | --- |
| [`scope_projection_matches_a_finite_lexical_identity_model`](../src/frontend/compile/lower/scope.rs) | 明示的な束縛IDと手動の線形分類による独立oracleに対し、2名・8値状態・移動と再束縛を組み合わせた7,225ケースを比較。量子成分が左右それぞれにある混合値とゼロ幅も含む。拒否時の入口非変更性を検査。すべてのソース実行経路の列挙ではない。 |
| [`nested_projection_restores_classical_entries_and_preserves_mixed_pending_ownership`](../tests/source_scope.rs) | 2実行ケース。入れ子scope、古典値の復元、混合値とQ<Unit>、呼出し中のBell参照、完全φ後の所有権を直接の期待相関で照合。 |
| [`equal_value_rebinding_cannot_hide_a_local_leak_or_revive_an_outer_owner`](../tests/source_scope.rs) | 4拒否ケース。値が等しい再束縛の未返却と消費済み外側所有権の再使用を、診断本文と位置まで検査。 |
| [`local_spent_names_expire_but_entry_spent_names_still_hide_functions`](../tests/source_scope.rs) | 6実行・3拒否ケース。通常呼出し・逆・0回反復の関数名について、局所消費済み名は消え、入口の消費済み名は復元されることを照合。 |

検査結果（macOS、2026-09-27）:

- `cargo test --all-targets --quiet`: **169件成功**。従来165件に内部モデル1件とソース回帰3件を追加。既存のLinux専用CLI 1件はこの環境では未実行。
- `cargo fmt --check`、`cargo clippy --all-targets -- -D warnings`: 成功。
- `python3 scripts/test_check_docs.py`: **14件成功**。文書参照検査と`git diff --check`も成功。
- `lake build`: 成功、1,212 jobs。`lake env lean -DwarningAsError=true Audit.lean`: **527宣言**の監査に成功。依存公理は標準の`propext`・`Classical.choice`・`Quot.sound`のみ。
- 独立レビューで抽出前後の同値性、診断、値と束縛の同一性の区別、期待相関の独立性を確認した。

次は入力・移動・束縛・待機中の所有者を含む状態対応を合成し、上の局所定理の前提をRustの成功経路から導く。全処理系・独立検証器の形式検証、量子意味保存、数値誤差の保証は残件である。以下の件数は各工程時点の履歴として保持する。

## SPEC-4: 具体的変換契約と前提付き意味保存（2026-09-27）

この工程の到達点を本節に記録する。[英語の変換契約](source-ir-correspondence.md)で、境界関係BC、基底符号化・表生成C1、原始操作C2、補助証拠と静的ターゲットC3、完全φ構築C4、構造・依存帰納による合成C5を整備した。指定した数学的変換について、位相を含む作用素と参照系付きinstrumentの対応を紙上で示した。Rustの全成功経路がその変換規則を満たす一般証明ではない。

IR検証器の単射表・所有権・freshness・効果の検査と、元のソース式に対する表の値・原始操作の選択・φの結果位置の一致を区別する。[対応表](source-ir-correspondence.md#7-implementation-and-independent-verifier-obligations)に実装項目と残る義務を記録した。言語の受理規則、公開API、Leanの証明範囲は変更していない。

[新しい回帰スイート](../tests/source_ir_correspondence.rs)は、コンパイラの変換や逆変換を期待値に使わず、解析的な疎状態とPauli測定のBorn則から分布を作る。許容誤差は`1e-12`。履歴ごとの振幅を足さず、その元の確率重みを保ったまま和算し、比較前の再正規化は行わない。

| 回帰 | 有限の検査範囲 |
| --- | --- |
| [`unit_factors_and_product_labels_match_every_explicit_basis_image`](../tests/source_ir_correspondence.rs) | Unitを挟む非対称な3ビット積置換を8基底入力と明示した表で照合。 |
| [`growing_lift_matches_joint_pauli_statistics_with_two_reference_wires`](../tests/source_ir_correspondence.rs) | 2→3ビットのliftと2本のBell参照を、5本の出力の全243通りのX/Y/Z設定で照合。 |
| [`observation_instruments_preserve_public_weights_and_reference_statistics`](../tests/source_ir_correspondence.rs) | 位相と偏りを持つ絡み合い入力の測定9設定、reset 9設定、discard 3設定。公開結果の重みと参照系の状態を照合。 |
| [`computed_predicate_packing_and_phase_match_coherent_and_controlled_inputs`](../tests/source_ir_correspondence.rs) | Unitを含む4引数predicate、27設定のコヒーレンス、16設定の制御位相、空引数／2個のUnit引数の1行表と位相4設定。等幅で型木が異なる2例を拒否。 |
| [`complete_branch_phi_transports_measured_results_fresh_wires_and_pending_frames`](../tests/source_ir_correspondence.rs) | 測定と新規割当を含む枝、2古典φ、2参照、待機中のQ<Unit>を81設定で照合。 |
| [`verified_ir_does_not_by_itself_establish_source_correspondence`](../tests/source_ir_correspondence.rs) | ソースのNOT表を別の有効な恒等表へ改変。独立verifyは受理するが、元のソースの期待分布とは異なることを確認。 |

合計は**6テスト、401受理ケース、2拒否ケース、有効IRの改変1件**。この有限範囲の一致は、すべての型・入力・ソースプログラムでの一般的な意味保存を証明するものではない。

検査結果（macOS、2026-09-27）:

- `cargo test --all-targets --quiet`: **165件成功**。従来159件に上記6件を追加。既存のLinux専用CLI 1件はこの環境では未実行。
- `cargo fmt --check`、`cargo clippy --all-targets -- -D warnings`: 成功。
- `python3 scripts/test_check_docs.py`: **14件成功**。文書参照検査と`git diff --check`も成功。
- 紙上導出と独立した期待状態式を再レビューし、座標輸送の向き・中間古典記録・computed入力の効果・静的操作の具体的出力を確認した。

本工程では文書と回帰テストのみを追加・更新し、処理系の変更を要する不整合は見つからなかった。Leanは変更しておらず、本工程でビルド・公理監査を再実行したとは扱わない。直前の境界修正時点の結果は次節に記録する。

## コードレビューで見つかった境界不具合の修正（2026-09-27）

この修正時点の実装検査を本節に記録する。後続節の件数も各改訂時点の履歴である。今回の修正は言語形式・標準API・量子意味論・Leanの証明範囲を変更しない。

| 不具合 | 修正と回帰検査 |
| --- | --- |
| 長いimport連鎖でスタックオーバーフロー | [モジュール探索](../src/frontend/project.rs)を再帰から明示的DFSスタックに変更。[projectテスト](../tests/project.rs)で3,000モジュールの非循環鎖と深い循環を2 MiBスレッド上で検査し、循環の位置・経路と共有依存の受理を照合。 |
| コメント内のLean importを監査対象への到達と誤認 | [文書検査](../scripts/check_docs.py)は先頭のimportヘッダを読み、行コメント・入れ子ブロックコメントを除外。宣言や文字列内のimport風の記述を依存関係と数えない。[回帰検査](../scripts/test_check_docs.py)でコメントにだけ記された未到達モジュールの拒否を確認。 |
| CLIの非UTF-8引数でpanic | [CLI](../src/bin/qleisli.rs)が`args_os`で元のOSパスを保持。[CLIテスト](../tests/cli.rs)で通常パス、非UTF-8のコマンドと存在しないパスの診断を確認。既存の非UTF-8ディレクトリを受理するLinux専用テストも追加。 |

検査結果（macOS、2026-09-27）:

- `cargo test --all-targets --quiet`: **159件成功**。従来153件にproject 3件とCLI 3件を追加。Linux専用のCLI 1件はこの環境では未実行。
- `cargo fmt --check`、`cargo clippy --all-targets -- -D warnings`: 成功。
- `python3 scripts/test_check_docs.py`: **14件成功**。`python3 scripts/check_docs.py`と`git diff --check`も成功。
- 元の12,000モジュールの再現プロジェクトを`qleisli check`で検査し、異常終了せず成功。
- 元のLean監査漏れの再現プロジェクトで、コメントにしかimportを書いていない`Qleisli.Hidden`を未到達として拒否。
- `lake build`と`lake env lean -DwarningAsError=true Audit.lean`: 成功。既存の**456宣言**を監査。

## レビュー後の仕様改訂と適合記録（2026-09-26〜27）

この節はA1〜C3への仕様改訂を記録する。後続の108・115・119・124・130・134件の記録はそれぞれの到達点の履歴であり、最新の件数ではない。本書は日本語の作業・適合台帳で、規範の英語版との関係は[用語集](terminology.md)に従う。

A1・A4は制限の明文化だけで済ませず、仕様と実装を拡張した。`do p <- q; pure e` の `p` に名前・`_`・入れ子の積パターンを認め、通常式には `true`・`false : CBit` と `not`・`and`・`xor` を追加した。どちらも**言語形式**であり、標準ライブラリの公開定義や封印された量子原始操作を追加するものではない。`true`・`false` は新しい予約語なので、旧ソースで識別子として使っている場合は改名が必要になる。

積パターンは基底ラベルだけを分解する。`do (a,_) <- q; pure a` は `Q<(Bit,Unit)> -> Q<Bit>` では全単射として受理し、`Q<(Bit,Bit)> -> Q<Bit>` では全入力の単射性が破れるため拒否する。通常式の論理演算は `CBit` 専用で、両オペランドを一度ずつ左から右に評価し、測定や所有権の消費を省略しない。古典ポートのないユニタリ関数内の閉じた古典計算と分岐は、両枝を検査した後に静的変換でも解決する。

| レビュー項目 | 決定・修正と追跡先 |
| --- | --- |
| A1 | `BP-NAME`・`BP-WILD`・`BP-PAIR`・`LIFT` を[型規則](source-typing-rules.md)へ追加・更新。[`basis_lifts_destructure_exact_product_patterns`](../tests/specification_boundaries.rs)、[`basis_patterns_reject_wrong_shapes_duplicate_names_and_lost_bits`](../tests/specification_boundaries.rs)で型木・重複名・Unit除去・コヒーレンス・単射性を検査。 |
| A2 | 基底関数の呼出しは隔離した `Xi` で名前解決し、外側の通常値は関数名を隠さない。基底パターンの名前は隠す。[`basis_calls_ignore_outer_cbit_names_but_respect_basis_binders`](../tests/specification_boundaries.rs)で `CBit` と積パターンも照合。 |
| A3 | 補助の私有束縛は遮蔽された外側と同名でも可。外側所有権はframeに保存される。[`computed_auxiliary_shadow_preserves_the_outer_owner`](../tests/specification_boundaries.rs)は元の量子値・位相の保持と未返却の拒否を照合。 |
| A4 | `C-CONST`・`C-NOT`・`C-BOOL`、古典レコードの決定的更新、左から右の効果付き合成を規定。IRの `ClassicalConst`・`ClassicalAnd` を追加し、既存 `ClassicalNot`・`ClassicalXor` も到達可能にした。[真理値表](../tests/specification_boundaries.rs)、[SSA検査](../tests/verify.rs)、[静的変換の厳密行列](../tests/static_semantics.rs)を照合。 |
| A5 | [混合値の射影](source-semantics.md#1-mixed-values-and-ordered-quantum-interfaces)と[判断の対応](formal-core.md#1-scope-and-judgments)へ統一。全計算の略記は結果・残存環境・frameをすべて含む。宣言の本体検査と呼出し展開のRust実装対応はSPEC-4の未証明の義務。 |
| A6 | 文法・モジュール／封印API・公開12定義の契約と関連リファレンスを英語化。英語版を正本、日本語の設計・証明メモと本台帳を補助資料と明記。 |
| B1・B2 | `Cnot`・`Toffoli` のIRを正記。[契約台帳](stdlib-contracts.md)に算術3定義を追加し、全12公開定義の型・全空間の意味・費用・検証状態・採用基準を記録。 |
| B3・B4 | `main` の任意の有限な入れ子古典積を明記。`xor2(p)` の個数違反と、分解後 `xor2(a,b)` の非単射性を区別。[`basis_call_arity_is_distinct_from_lift_injectivity`](../tests/specification_boundaries.rs)と[`entry_point_accepts_nested_classical_products`](../tests/specification_boundaries.rs)。 |
| B5・B6 | Bell・位相オラクルの4掲載コードを実ファイルと一致させ、古い検査件数・定義件数を履歴と明記。現行の検証結果は本節に集約。 |
| B7 | 現行の限定補助領域・生IRの保護領域の検査と、未実装の一般借用構文・署名を区別。 |
| B8 | EBNFを予約モジュール名の後の追加パスにも整合。`ClassicalType` は入口検査に使う意味的部分集合と明記。コメント内のCf受理、先頭BOMとソーストークン内Cf拒否を規定。[`reserved_std_module_keywords_allow_further_identifier_components`](../tests/parser.rs)、[`unicode_format_characters_are_comment_text_but_not_source_tokens`](../tests/parser.rs)。非単射リフトの `Ownership` 診断も[記録](frontend-v0.md#診断と上限)。 |
| B9・C1・C2・C3 | 通常関数、アルゴリズム、frame、ケット／ブラを[用語集](terminology.md)に統一。規則ID・実装・テストの対応表を新構文まで更新し、参照先の存在を文書検査で照合。 |

今回の最終検査結果（2026-09-27）:

- `cargo test --all-targets --quiet`: **153件成功**。compile 30、parser 14、project 8、verify 28、sim 13、algorithms 7、static_operations 12、order_finding 10、source_judgments 6、source_semantics 4、source_soundness 4、static_semantics 7、specification_boundaries 10。
- `cargo fmt --check`、`cargo clippy --all-targets -- -D warnings`、`git diff --check`: 成功。
- `python3 scripts/test_check_docs.py`: 9件成功。`python3 scripts/check_docs.py`: ローカル文書・節・実装項目・テスト参照、Leanのroot importを検査。

R1・T1〜T3・S1〜S4・Q1〜Q3の紙上の帰納ケースを新構文へ更新し、F2に閉じた古典評価と完全なφ転送を加えた。Leanは変更せず、ビルド・公理監査は今回再実行していない。有限テストや紙上証明の更新を、全Rust受理経路への適合証明や段階1全体の完了とはしない。

## v0初回確定時の決定

| 項目 | v0として固定した内容 | 後続に置く内容 |
| --- | --- | --- |
| 対象 | `Unit`・`Bit`・有限積、非再帰、静的有限反復 | サイズ付き型、配列、動的反復 |
| 型と所有権 | 基底型と通常型を分離。型木は厳密に比較。`Q<Unit>` と混合タプルも線形 | 型レベルの状態・分離・成功条件の証拠 |
| 効果 | `Unitary ≤ Iso ≤ Observe`。呼び出しに宣言効果を使用。古典入力ごとの量子写像を分類 | 操作値・効果多相・厳密なモナド構造 |
| 基底計算 | 全域な有限表。`not > and > xor`。`do/pure` は捕捉のない単射リフト | 一般の継続、任意の振幅関数 |
| 古典分岐 | 両枝の型木・消費集合、結果位置と生存frameを対応させるφ | 一般の依存型・実行時に変わる資源インターフェース |
| 静的操作 | 同型の単一量子引数を持つ `unitary` の逆・制御・反復。位相を保持 | 操作パラメータ・古典引数付き変換・任意角度 |
| 補助証拠 | 展開後の補助上 `Z/T` 列または空列だけを構成的に認証 | `with0`、一般の借用・作業レジスタ・保存効果署名 |
| 観測 | 測定は所有権を消費して `CBit` のみ。resetは新しい論理ID。破棄は部分跡 | 非破壊測定・実機への割当 |
| stdlib | 封印APIを規範化。通常の同梱定義は同じ検査を通す | 一般のアルゴリズム骨格と標準採用・互換性方針 |

[言語仕様](language-spec.md)が型・効果・所有権・意味・IR対応、[文法](syntax-v0.md)が字句と構文、[標準ライブラリ構成](standard-library.md)がファイル・モジュール・封印名を規定する。将来計画のメタ型や関数名はv0のAPIに読み替えない。

今回のソース規則は、既存の有限実装を監査して規範として採用したもの。処理系の機能追加は行わず、未決表記の解消と6件の適合テストを追加した。既存のA1〜A3/L0〜L3の成果を保持し、言語仕様優先へ順序を戻した。

## 規範と実装プロファイルの差

| 境界 | 現行実装と扱い |
| --- | --- |
| 有限のサイズ | 数学的な型は任意の有限積。処理系はレジスタ・基底表に12ビット、構文・展開に深さ64、内部型／値に4,096ノード・深さ64、合計作業に1,000,000の上限を置く。超過は診断。 |
| 反復回数 | 規範文法は先頭ゼロのない自然数リテラル。現行パーサの容量は0〜4,096。切り詰めて実行しない。 |
| 静的な制御 | 有限 `ApplyUnitary` への展開を使う。制御を含む合成レジスタも12ビットの上限を受ける。 |
| ファイルシステム | 現行ローダはソースルートを正規化し、配下のシンボリックリンクを拒否する。ソースは `.qli`、モジュールの各要素は予約語と単独 `_` を除くASCII識別子。OSごとのファイル配置は量子意味論の規則ではない。 |
| 検査と実行 | `check_project` は全宣言を検査し、入口の存在を要求しない。`compile_project` / `run` が閉じた `main` の条件を要求する。 |
| ソースと生IR | 生IRの保護付き作業レジスタなどはソースv0の全APIではない。古典const/not/and/xorは上の改訂でソースから到達できる。生IRが受理する構造をそのままソースで書けるとは限らない。 |
| 補助本体 | `h(h(a))` の恒等性や `adjoint(t,a)` の対角性を一般判定しない。これは容量差ではなく、v0自体が選んだ証拠形式の制限。 |
| 数値実行 | `f64` の非正規化純粋状態アンサンブルを使う。厳密な等式・ゼロ確率の証明ではない。[実行上限と誤差](ir-prototype.md)を参照。 |
| backend | 外部バックエンドは未実装。能力検査を必要条件として定めたことは、実機での実行保証ではない。 |

上限による拒否と型・効果・所有権による拒否を区別する。既知のv0規則はこのプロファイルと有限テストの範囲で照合した。全入力・全プログラムに対する実装適合を証明したものではない。

## 適合例と検証根拠

以下は実行したテストへの対応であり、網羅的な形式証明ではない。`finite_v0_` で始まる6件が今回の追加。

| 規則・意味 | 自動検査の根拠 |
| --- | --- |
| 字句、文法、基底演算の優先順位、構文上限 | [parser](../tests/parser.rs): `basis_operators_have_documented_precedence_and_left_associativity`、`invisible_separators_and_bad_bit_literals_have_precise_errors` 等 |
| import、pub、std封印、名前衝突と循環 | [project](../tests/project.rs): `import_cycles_and_name_collisions_are_rejected`、`unknown_sealed_name_is_not_reinterpreted_as_user_code` 等 |
| 型木の一致、裸のBit拒否、0ワイヤの線形性 | [compile](../tests/compile.rs): `finite_v0_type_shapes_and_zero_wire_ownership` |
| 古典情報の消去と量子効果、宣言効果の保守的な適用 | [compile](../tests/compile.rs): `finite_v0_effects_classify_quantum_maps_and_respect_declarations` |
| 混合値の移動、分解後の古典部分のコピー | [compile](../tests/compile.rs): `finite_v0_mixed_values_move_as_a_whole` |
| 単射性は入力型に依存、基底式の捕捉禁止 | [compile](../tests/compile.rs): `finite_v0_basis_lifts_are_injective_and_closed` |
| 補助上の展開後Z/T列、意味的には対角でも証拠形式外なら拒否 | [compile](../tests/compile.rs): `finite_v0_computed_blocks_require_the_structural_certificate` |
| 基底・静的操作での局所名の優先、移動後も続くスコープ | [compile](../tests/compile.rs): `finite_v0_local_names_shadow_static_callees` |
| 古典分岐の結果位置、枝内生成、呼び出し元のframe | [compile](../tests/compile.rs): `conditional_swap_pairs_different_input_registers`、`branch_created_wires_and_classical_results_merge`、`function_branch_preserves_the_callers_quantum_frame` |
| 測定後再利用・暗黙破棄・非単射・効果違反の拒否 | [compile](../tests/compile.rs): `invalid_source_is_rejected_before_execution`。生IRも [verify](../tests/verify.rs) で拒否検査 |
| Bell部分測定、破棄後の混合状態、resetの新規系 | [sim](../tests/sim.rs): `bell_half_measurement_and_feedback_corrects_other_half`、`discarding_entangled_half_keeps_mixed_residual`、`reset_breaks_bell_correlation_and_returns_new_zero_wire` |
| 静的逆・出力軸順序・制御下の全体位相、反復0も検査 | [static_operations](../tests/static_operations.rs): `inverse_reverses_noncommuting_gates_and_output_axis_reordering`、`computed_zero_width_phase_survives_inverse_and_control`、`static_forms_reject_bad_names_effects_types_and_ownership` 等 |
| 生成元に依存しない独立IR検査 | [verify](../tests/verify.rs) の27件と [static_operations](../tests/static_operations.rs) の `raw_finite_circuit_validation_rejects_forged_certificates` |
| 同梱定義の合成とアルゴリズムごとの契約 | [algorithms](../tests/algorithms.rs)、[static_operations](../tests/static_operations.rs)、[order_finding](../tests/order_finding.rs)。成功条件・参照系・前提外の反例を個別に検査 |

### 検査結果（2026-09-26）

- `cargo test --test compile finite_v0`: 追加6件成功。
- `cargo test --all-targets`: **108件成功**。compile 23、parser 8、project 8、verify 27、sim 13、algorithms 7、static_operations 12、order_finding 10。
- `cargo fmt --check`、`cargo clippy --all-targets -- -D warnings`、`git diff --check`: 成功。
- README・ROADMAP・AGENTS・docs内のMarkdownローカルリンク先を確認し、欠落なし。

## SPEC-3の資源規則と実装対応

[Source resource rules for finite core v0](source-resource-rules.md)を英語の正本として追加した。混合値、移動済み束縛、一時結果、関数の外側のframe、分岐の結果位置とφ、0ワイヤの所有権を一つの規則系にまとめた。新しい構文や受理規則は導入していない。[形式化の概要](formal-core.md)も英語化した。

| 項目 | 今回の到達点 | 残る境界 |
| --- | --- | --- |
| 資源判断 | 所有権の所在を束縛・一時結果・レジスタ対応の間の分割として定義 | ソース仕様・Rust実装との一般的な対応は未証明 |
| R1 | 明記した規則系の資源不変量と関数境界の帰結を紙上で証明。所有権計数の射影モデルは別途Leanで検証 | 紙上規則全体の機械検証、全Rust実行経路の形式検証ではない |
| φと補助 | 全生存スロットを覆うφの軸改名、限定Z/T証拠のゼロ復帰を局所補題として記述 | 一般のソース意味保存・量子的健全性は未完了 |
| 実装監査 | 規則・Rust関数・既存／追加検査の対応表を記録 | 有限例の照合は完全な対応証明ではない |

追加した `tests/compile.rs` の7件は `resource_rules_` で始まる。評価途中の混合引数・タプル要素とBell参照の保持、混合結果の位置対応、0ワイヤの結果と呼び出し元frameのφ、片側reset後の相関と古典履歴、入れ子の古典φを照合した。最後の検査には、消費集合の不一致・同名再束縛による暗黙喪失・`Q<Unit>`の破棄・混合値の複製・関数引数の未処理という6つの拒否例を含む。

検査結果（2026-09-26）:

- `cargo test --test compile resource_rules_`: 追加7件成功。
- `cargo test --all-targets`: **115件成功**。compile 30、parser 8、project 8、verify 27、sim 13、algorithms 7、static_operations 12、order_finding 10。
- `cargo fmt --check`、`cargo clippy --all-targets -- -D warnings`、`git diff --check`: 成功。
- README・ROADMAP・AGENTS・docsのローカルリンク239件に欠落なし。資源規則の対応表が参照する追加テスト7件の存在も確認。

紙上証明そのものをRustテストに合格したとは扱わない。上の108件は仕様v0確定時の履歴であり、今回の7件を含まない。

## Leanによる補助検証の区切り

[英語の定理台帳](lean-resource-proof.md)にRA-1〜RA-10の機械検証済みの範囲と前提を記録した。混合値・`Q<Unit>`、局所資源遷移、frame、全所有権を覆うφ、合成を対象とし、13件の境界補題を含む。Lean／Mathlibは4.30.0と依存コミットに固定し、ビルドと公理監査をCIへ追加した。CI定義の追加とGitHub上での実行成功は区別する。

名前・効果・古典スコープ・発行済みID履歴・Rust実装との対応・量子意味論は未移植であり、R1全体を機械検証済みとはしない。Leanは本題の言語仕様を支える補助とし、当面は対象を拡大せず、下記の仕様・意味論・IR対応を優先する。

ローカル検査（2026-09-26）: Leanビルドと449宣言の公理監査が成功。Rust全115件・fmt・Clippyも成功。文書リンク263件とLeanの5モジュールのimport網羅を確認した。独自公理・未証明穴・native評価の一時的な混入例は公理監査で拒否された。

## ソース意味論とIR対応の局所証明

[Source values, calls, and branch semantics](source-semantics.md)を追加し、混合値・字句環境・順序付き量子インターフェース・非正規化の古典量子状態を定義した。S1〜S4は、評価済み値の代入、相関するframe、古典分岐と同時φ、構造的IR変換についての前提付きの紙上証明である。部分式と各操作の正確な意味対応、資源・名前・スコープの前提を明示し、全ソース／Rust実行経路への一般化は未完了とした。

本番の規範文書[language-spec.md](language-spec.md)を英語化し、型・効果・所有権・受理／拒否・IR方針と状態を維持した。既存の日本語節アンカーも保持する。Leanは変更していない。

追加した[4件の回帰検査](../tests/source_semantics.rs)は、測定引数の評価回数と同じ古典IDを複数の仮引数へ渡すこと、呼び出し先の名前解決と外側束縛の復元、T/ZTの位相とBell相関、`Q<Unit>`を含む量子・古典φの順序独立性を確認する。独立に求めた確率分布と照合し、単なる処理系同士の一致で合格とはしない。実装の修正を要する不具合は今回の監査では見つからなかった。

検査結果（2026-09-26）:

- `cargo test --test source_semantics`: 追加4件成功。
- `cargo test --all-targets --quiet`: **119件成功**。既存115件に上記4件を追加。
- `cargo fmt --check`、`cargo clippy --all-targets -- -D warnings`、`git diff --check`: 成功。
- `python3 scripts/check_docs.py`: ローカルリンク285件と既存Leanの5モジュールのimport網羅を確認。
- 英語化した仕様の既存12アンカー（表題と11節）、仕様・意味論のMarkdown表を確認。

上の115件とLeanの公理監査は前の到達点の記録である。今回の数式は条件付きの紙上証明であり、RustテストやLeanで機械検証したとは扱わない。

## 有限静的変換の演算子対応

[Exact semantics of finite static transformations](static-semantics.md)のF1〜F5で、順序付き軸の再配置、平坦化と最終出力置換、限定補助計算の位相、逆・反復・量子制御について、位相を含む正確な演算子等式を紙上で示した。単一量子入出力・古典ポートなし・独立検証・対応する構成子への限定を前提とする。検証済み生IRのすべてを平坦化できるとは主張しない。

[静的操作の契約](static-operations.md)を英語の正本として整備し、対象名の解決を入力評価後の環境で行うこと、使い終わったローカル名も関数を隠すこと、正確な型木と宣言効果、ゼロ反復と両制御枝の検査、入力効果と待機中の所有権を推論規則へ明記した。以前の6アンカーと歴史的な検証記録を保持する。受理規則・公開API・Leanの対象範囲は変えていない。

[tests/static_semantics.rs](../tests/static_semantics.rs)は`Z[zeta,1/2]`の整数係数を用い、12個のコンパイル済み回路の38入力列・186行列成分を独立した解析式と厳密に比較する。非可換な位相と置換、非隣接軸への制御の再配置、3-cycleの返却順、ゼロ反復、入れ子の0/1制御、`Q<Unit>`のスカラー位相を含む。4件の演算子検査と1件の算術ヘルパー検査を追加した。処理系の逆変換や確率だけの一致を期待値に使っていない。

検査結果（2026-09-26）:

- `cargo test --test static_semantics`: 追加5件成功。
- `cargo test --all-targets --quiet`: **124件成功**。既存119件に上記5件を追加。
- `cargo fmt --check`、`cargo clippy --all-targets -- -D warnings`、`git diff --check`: 成功。
- `python3 scripts/check_docs.py`: ローカルリンク319件と既存Leanの5モジュールのimport網羅を確認。
- 英語化した静的契約の既存6アンカー、変更した8文書の表27個、演算子の対応表が参照する4テスト名を確認。

対象実装に修正を要する不具合は見つからなかった。これらは数学的アルゴリズムの条件付き紙上証明と有限のRust回帰検査であり、F1〜F5を機械検証した結果や全ソースの健全性証明ではない。119件以前の件数は各到達点の履歴として保持する。

## 型・効果・名前・スコープの推論規則

[Type, effect, name, and scope judgments](source-typing-rules.md)を英語の規範補遺として追加した。型形成、名前と宣言、全基底式、全通常式、引数列、パターン、文、ブロックを資源規則R1へ接続し、全AST構成子を対応表で照合した。型木、引数個数、宣言効果、消費済み名の隠蔽、calleeの定義元モジュール、完全なφ、補助計算の構造的証拠を明示する。新しい構文・API・受理規則は加えていない。

T1は基底式の型付き全域性と型の一意性、T2は結果型・構文的効果・残存束縛状態の一意性と消費済み外側所有権の非復活、T3は宣言効果の保守性と条件付きのIR効果上界を示す。生成IRの一意性は主張しない。レビューで、同じ古典値のφには再利用と新規出力の選択肢があることを確認し、定理の範囲を型・効果・束縛状態に限定した。いずれも紙上証明であり、Rust実装の形式検証や量子的健全性の完成とはしない。

[追加6テスト](../tests/source_judgments.rs)は、宣言効果の伝播、スコープとspent marker、厳密な積型と述語の左結合定義域、基底文脈の分離、補助計算の証拠、複数モジュールの名前解決を確認する。展開後にIRの効果が弱くなる例も照合し、独立IR検証がソースの宣言効果検査を代替するとは扱わない。実装修正が必要な不具合は見つからなかった。

検査結果（2026-09-26）:

- `cargo test --test source_judgments`: 追加6件成功。
- `cargo test --all-targets --quiet`: **130件成功**。既存124件に上記6件を追加。
- `cargo fmt --check`、`cargo clippy --all-targets -- -D warnings`、`git diff --check`: 成功。
- `python3 scripts/check_docs.py`: ローカルリンク351件と既存Leanの5モジュールのimport網羅を確認。
- 7種類のAST列挙型・全34構成子とBlockの対応、追加テスト名6件、変更した8文書の表29個、規範仕様の既存12アンカーを確認。

構文上の全場合を提示したことと、規則系・仕様・Rustの全受理経路の対応を証明したことは異なる。後者、量子意味論の一般定理、全ソースからIRへの意味保存は残件である。Leanは変更していない。以前の検査件数は各到達点の履歴として保持する。

## 数学的なソース導出の理想健全性

[Ideal soundness of the finite source derivation system](source-soundness.md)に、Q1（純粋な古典結果の決定性・等長性／ユニタリ性）、Q2（有限適応Kraus合成・公開結果への集約）、Q3（全ソース導出のインストルメント健全性）を追加した。型・資源規則の成功した数学的導出と正確な原始意味を対象とし、結果だけでなく残る環境とframeを含む完全なインターフェースで帰納する。任意の参照系、履歴ごとに異なる中間空間、確率ゼロの枝、古典情報の非可逆な処理も含む。

紙上定理は、Rustの受理と導出の対応や生成IRの意味保存を前提にして循環的に証明していない。これらの実装対応は別の残件である。静的な対象のユニタリ性は依存順の帰納から得て、単に「別のIRがユニタリと検証された」ことで元のソースと一致するとは扱わない。

[Kraus.lean](../lean/Qleisli/Kraus.lean)を追加し、有限の厳密な複素行列に対する5補題を検証した。`Complete A`は`sum_i A_i† A_i=I`であり、等長な出力対応と、第一結果に応じて後段が変わる適応合成が完全性を保つ。中間・出力の行列型は固定し、紙上定理の正値性・跡・参照系・ソース帰納まではLeanで証明していない。[定理台帳](lean-resource-proof.md)にKA-1〜KA-5と前提を記録した。

[追加4テスト](../tests/source_soundness.rs)は、7個のコンパイル例の解析的な分布と全確率を照合する。隠した履歴の位相を干渉させないこと、適応観測の非一様な結合分布と周辺分布、GHZ位相とreset後の喪失、実行されない確率ゼロの枝を検査した。許容誤差は`1e-12`で、比較前の再正規化は行わない。実装修正を要する不具合は見つからなかった。

検査結果（2026-09-26）:

- `cargo test --test source_soundness`: 追加4件成功。
- `cargo test --all-targets --quiet`: **134件成功**。既存130件に上記4件を追加。
- `cargo fmt --check`、`cargo clippy --all-targets -- -D warnings`、`git diff --check`: 成功。
- `lake build`と`lake env lean -DwarningAsError=true Audit.lean`: 成功。**456宣言**で許可された3公理のみを使用。
- `python3 scripts/check_docs.py`: ローカルリンク377件とLeanの6モジュールのroot import網羅を確認。
- 10文書の表32個、新規テスト名4件、Lean補題5件と台帳、規範仕様の既存12アンカーを確認。

Leanのツールチェーン・依存版、ソースの受理規則、言語形式・標準APIは変更していない。以前の「Leanは変更していない」と検査件数は、それぞれの過去の到達点を記したもの。現在の到達点は規則系の紙上健全性と限定した行列補題であり、Rust処理系全体の形式検証ではない。

## 次に証明すること

この節は元の証明課題の履歴です。v0.1.5で採用した現在の順序は
[有限IR検証器・カーネルを先に扱う計画](formal-core.md#4-theorem-status-and-proof-work)
を参照してください。以下の課題は残していますが、番号順を現在の優先順位とは扱いません。

次の課題は、本節に記録した改訂後の仕様v0について、その契約を成立させる根拠を完成させる作業である。矛盾・反例が見つかった場合は仕様変更として明記する。

1. **推論規則と実装の対応:** 構文全体の型・効果・名前・スコープ規則と資源規則を、v0およびRustの全受理経路へ対応づける。T1〜T3と値・環境の意味論を基に、暗黙frame・束縛スナップショット・スコープの一般的な対応を示す。
2. **資源安全性の接続:** 規則系の紙上定理R1を、ソース検査器とIR検証器のすべての受理経路へ接続する。無断複製・暗黙喪失・測定後利用の不在を、処理系について証明済みとはまだしない。
3. **理想健全性の処理系への移送:** 明示した規則系にはQ1〜Q3の紙上定理を得た。Rustの全受理経路がその型・効果・資源・意味の前提を満たすことを示し、実装での健全性保証へ接続する。
4. **ソース→IRの意味保存:** C1〜C5で数学的な変換規則についてS1〜S4とF1〜F5を合成した。次はその境界関係、型・効果・名前・軸順・証拠の前提をRustの全成功経路が満たすことを示す。紙上の数学的変換と、実装の一般的な適合証明は区別する。
5. **実装への接続:** 検証器の各受理条件を証明の前提と対応づける。[有限IRの紙上証明](finite-core-proof.md)は前提付きの議論であり、Rust実装の正しさやソース全体の定理を自動的に与えない。

これらの完成前は、段階1全体を完了にせず、コンパイル成功を証明済みの物理的妥当性とも呼ばない。個別アルゴリズムの正答・成功確率、ホスト後処理、実機のノイズと較正は、さらに別の検証対象である。
