# Qleisli v0.x roadmap and the v0.1.9 boundary

Status: **development direction and maintenance boundary selected on
2026-09-27**. The current product version is **0.1.4**; its
[release record](releases/v0.1.4.md) distinguishes version selection, validation,
and publication. Later rows below are work targets, not completed releases or
adopted language syntax. This is the detailed release plan linked from the
[roadmap](../ROADMAP.md), subject to the [versioning policy](versioning.md) and
[authoritative acceptance criteria](release-milestones.md).

## Decision: consolidate the finite foundation through v0.1.9

**v0.1.4–v0.1.9 is a compatible maintenance series for the existing finite
language and its semantic contracts.** Its endpoint is an audited, reproducibly
validated finite baseline and an explicit handoff to next-minor design. It
does not deliver a generalized algorithm language. The new public capabilities,
types, effects, evidence interfaces, and library APIs discussed below belong
to v0.2.0 or later, following their own specification decisions.

The supplied ownership/capability/effect/typestate discussion motivates this
plan, but its release sketch cannot be copied literally. Qleisli already has
linear ownership, the effect order `Unitary <= Iso <= Observe`, finite static
adjoint/control/repetition, exact auxiliary certificates, and function evidence
retained through final IR. Future work generalizes these facilities; it does
not defer the first effect checker or first semantic certificate until v0.4
or v0.5. See the [current grammar](syntax-v0.md),
[static operations](static-operations.md), and [SC/FC contracts](function-contracts-v0.1.md).

## Responsibilities beyond ownership

**Require every new abstraction to identify an obligation it removes from the
algorithm author, the evidence that replaces that obligation, and the checker
that enforces it.** Use the six [imaginary algorithm drafts](imaginary-v1/README.md)
to evaluate that benefit. A shorter gate listing or another annotation is not
sufficient. The intended user experience is ordinary component composition;
library authors and evidence producers may still need to supply proofs.
Inference is bounded: failure to establish a required capability or contract
must produce a diagnostic, never unchecked acceptance.

The names in this table describe design roles, **not new `.qli` types or APIs**.

| Responsibility | Existing finite foundation | Next design direction and obligation removed |
| --- | --- | --- |
| Ownership: who may use a resource | Linear `Q<A>`, complete call/branch frames, no use after measurement | Preserve the same accounting under parameterized operations and register structure, so authors need not track individual wire lifetimes. |
| Capability: which operations are available | Eligible closed unitary bodies support static adjoint, control, and repetition | Make phase-fixed unitary meaning, adjoint access, and controlled access explicit at operation-parameter boundaries. Derive capabilities only from supported implementations or checked access evidence, so callers need not reconstruct those derivations. |
| Effect: what a computation does | Declared classifications and inferred body effects using `Unitary <= Iso <= Observe` | Consider finer summaries and inference only where they simplify composition. Preserve observation instruments and declared contracts; do not conflate allocation, measurement, classical selection, or host I/O with transformation access. |
| Typestate: which invariant has been established | Consumed/live ownership and certified computed scopes | Track established auxiliary/encoding invariants across specified boundaries, so cleanup obligations can be checked automatically. A proposed `Clean` label requires exact zero/separation evidence; `Dirty` means no such established invariant, not a measured physical state. |
| Proof contracts: why the implementation has its promised meaning | Bounded SC/FC checks, immutable evidence, independent final-IR verification | Reuse evidence and move proof production behind library boundaries while checking its binding independently. General proof search, import, and symbolic equality remain separate design tasks. |
| Resource accounting: what execution costs | Documented finite limits and selected component costs | Later expose useful bounds for wires, depth, gates and oracle calls, separating compilation, checking, quantum execution, and classical work. A resource type system is not needed for the maintenance series. |

Mathematical unitarity alone does not supply controlled access to an opaque
operation or its inverse implementation. Preserve the operation's phase;
`U` and `exp(i theta) U` can differ observably under control. Finite repeated
application does not imply efficient or unit-cost access to large powers.
Likewise, an isometric initializer is not freely invertible on its whole
output space. `Measurable`, `Allocate`, and `Discard` are not adopted as
synonyms for unitary transformation capabilities.

Auxiliary cleanup must hold for every permitted input and arbitrary reference
system. In an exact pure cleanup contract, for an implementation
`F : H_in -> H_data tensor H_aux`, the required factorization is
`F = (I_data tensor |0_aux>) V` with `V : H_in -> H_data` an isometry
when cleanup is promised on all physical inputs. For an isometric entry
encoding `E_in : H_logical -> H_in`, the encoded-input contract instead requires
`F E_in = (I_data tensor |0_aux>) V`, with `V : H_logical -> H_data`
an isometry and separately established entry evidence. Both equations extend
by the identity on any reference system. Ownership, an inverse capability, scope exit, a
typestate name, or an approximately zero measurement result alone does not
establish this equation. General entanglement-region inference and dependent
or graded type systems remain research options, with no selected release.

## Maintenance work targets: v0.1.4 through v0.1.9

These rows assign priorities and reviewable outputs. They are not a requirement
to manufacture six releases: compatible work may be regrouped before selecting
each version. v0.1.9 is the planned consolidation checkpoint, not a SemVer
ceiling; a necessary later maintenance fix may use v0.1.10. Do not ship a new
public feature under a patch merely to meet this table.

| Target | Work and deliverable | Completion evidence | Current state |
| --- | --- | --- | --- |
| v0.1.4 | Synchronize the project version; adopt this roadmap, responsibility split, and v0.1.9 boundary. | Linked English plan, release record, conformance entry, metadata and documentation checks; complete local candidate preparation under P014. | P014-1–P014-4 complete locally: planning, independent review, Rust/Lean/Python/examples and candidate distribution. [P014-5](releases/v0.1.4.md#v014-roadmap-and-completion-evidence) actual commit/CI/publication evidence is recorded in the [GitHub release](https://github.com/MGYamada/Qleisli/releases/tag/v0.1.4). |
| v0.1.5 | Audit the finite language's ownership, effects, name/scope and static-transform acceptance against the published rules. | A rule-to-implementation/test inventory; dispositions for gaps; a reproducer and targeted regression for every repaired defect, including zero-width owners, pending/caller frames and zero repetitions where relevant. | Planned; no new audit or fix claimed here. |
| v0.1.6 | Audit existing contract/evidence boundaries and exact cleanup. | Review implementation substitution, frozen source/dependency binding, phase, output axes, references and invalid certificates through final IR; record fixes and independent counterexamples for discovered gaps. Retain numerical execution limits separately from exact checking. | Planned; existing V01-C1–C6 evidence remains the baseline. |
| v0.1.7 | Consolidate correspondence and proof obligations for the existing finite implementation. | Map R1/T1–T3/Q1–Q3 and C1–C5 to implementation paths, local proof artifacts and remaining premises; review the trusted boundary and separate the Qleisli/Physlib audits. Advance compatible internal proof work where useful. | Planned; no promise of whole-Rust soundness or new public Lean APIs. |
| v0.1.8 | Prepare the next-minor decision dossier from all six imaginary drafts. | Resolve or explicitly defer capability/access, size, QPE angle/evidence, instrument/error, host and migration choices, tracing R01–R14. Classify each proposed facility and state accepted/rejected cases and its intended IR evidence. Record blockers rather than implementing imaginary syntax. | Planned; six initial drafts already exist, but selected extension specifications remain open. |
| v0.1.9 | Consolidate and review the supported finite baseline. | Satisfy B019-1–B019-6 below, record full release validation on the final candidate, and decide next-minor readiness. | Planned; neither its release checks nor its completion are claimed by 0.1.4. |

The ordinary [release validation policy](versioning.md#release-records-and-validation)
applies whenever one of these versions is actually released, not only at
v0.1.9. A document change can record narrower checks without being called a
fully validated release. Public Lean declarations are part of compatibility:
new exported facilities require classification under the minor-version policy,
even when motivated by proof work.

## v0.1.9 acceptance boundary

The corresponding [release milestone](release-milestones.md#v019-maintenance-boundary)
adopts these conditions as the maintenance endpoint. All are future acceptance
conditions; this document does not mark them complete.

| ID | Required at the consolidation checkpoint |
| --- | --- |
| B019-1: compatibility | Preserve the published finite grammar, standard APIs, Rust/IR/evidence and Lean interfaces, CLI conventions, semantic premises, capacities and supported toolchains. For any erroneous acceptance repaired under the patch exception, record the already violated rule, before/after behavior, diagnostic and regression. No new restriction on valid programs or hidden public API change. |
| B019-2: finite assurance | Revalidate V01-C1–C6 in their declared bounds: one fixed client with substitutable implementations, retained final-IR evidence, exact phase and cleanup, complete ownership, and positive/negative reference-sensitive cases. The finite checker may still use bounded dense matrices. |
| B019-3: audit dispositions | Publish the finite-rule and evidence-boundary inventories from the maintenance audits. Resolve discovered violations of the supported contracts before release; list proof gaps and out-of-profile requests separately. Regressions are evidence for specific cases, not a general theorem. |
| B019-4: honest proof ledger | State which rules have paper proofs, which lemmas are Lean-checked, how they relate to actual Rust paths, and all remaining adequacy/verifier/numerical assumptions. Preserve separate project/external-library axiom audits. Whole-compiler soundness is not a mandatory completion claim. |
| B019-5: design handoff | Keep the six imaginary drafts and R01–R14 review current; publish a smallest-next-scope recommendation with requirement classification, semantic premises, compatibility, verification method, and explicit unresolved decisions. A documented no-go because symbolic checking or QPE angle evidence is unresolved still completes this dossier; it does not authorize feature implementation. |
| B019-6: reproducibility | Record the final candidate's primary-toolchain Rust fmt and primary/MSRV tests/Clippy, retained research-package checks, document/helper suites, pinned Lean build and both audits, representative CLI/Shor runs, package/source-archive and attribution checks. Distinguish local results, exact-commit CI, tagging, push and publication, with platform omissions explicit. |

**Outside v0.1.9:** new capability or typestate syntax; general operation/size
parameters; fine-grained effect or instrument APIs; new public standard-library
facilities; arbitrary-angle or approximation support; portable proof loading;
symbolic-kernel extensions or production integration; generalized QPE/Grover/
Shor; resource grades or entanglement regions; external backends; and a promised
proof of the entire Rust compiler. Compatible corrections, documentation and
existing proof obligations remain in scope. No new public feature is adopted
by describing its future contract here.

## v0.2 toward v1: capability-led generalization

The following minor-series themes provide a dependency order and evaluation
targets. Their precise feature sets and release dates are **not fixed**. They
may be narrowed or moved after specification review; a later version number
does not excuse an unmet prerequisite. Maintenance and useful local proof work
can continue alongside them.

| Planning target | Main direction | Evidence needed before calling the target delivered |
| --- | --- | --- |
| v0.2 | Operation capabilities and static operation parameters, initially the smallest supported unitary/adjoint/control profile (R02–R03, R14). | English extension rules; phase-fixed access and implementation binding; the same algorithm body accepts distinct checked operations; unsupported control/inverse access is rejected. No automatic support for arbitrary black-box operations or sizes. |
| v0.3 | Static sizes, ownership-preserving register structure, and evidence-backed auxiliary lifecycle (R01, R04, R06, R14). | Reuse definitions at multiple sizes; preserve all owners and exact cleanup, including correlated references; independently compose contracts without global dense expansion. Clean/dirty surface annotations are optional until justified by author needs. |
| v0.4 | Effect/instrument composition and the precision/measurement boundary needed by QPE (R05, R08, R12). | Explicit outcome/residual-state contracts, phase/bit order, chosen angle and exact/approximate policy, and rejection of observation in pure transforms. Finer effect inference extends the existing checker rather than replacing it by an unspecified effect algebra. |
| v0.5 | Reusable proof production and library contract composition (R14 and required parts of R06–R08). | Ordinary calls discharge supported obligations from checked library evidence; independent checking rejects stale or mismatched proofs. Any prover/import boundary is specified and tested; general theorem search is not required. |
| v0.6 | Shared algorithm-level QPE and amplitude-amplification/Grover components. | Compiling, checked source exposes preparation, oracle/reflection or controlled powers, transforms and measurement across supported sizes and operations. Amplitude estimation tests reuse where its extra contracts are available. |
| v0.7 | Reversible arithmetic and the complete Shor workflow (R09, R13). | Efficient construction within declared bounds, shared QPE, actual sampling, period/factor validation and explicit failure/retry. State whole-space arithmetic behavior and exact scratch cleanup. |
| v0.8 | Cost reporting, diagnostics and usability across the three v1 families. | Separate circuit-generation, verification, execution, oracle and classical costs; compare implementation choices while preserving contracts and readable source. Adopt resource annotations only when needed, with their own specification. |
| v0.9 | Stabilization against V1-C1–C5. | Independently review all three executable families, supported bounds, substitutions, failures and public contracts; complete migration and release evidence. v1 follows the evidence, not the numbering. |

This is not a promise that every theme needs an entire minor release, that
the listed features are sufficient by themselves, or that full general
compiler mechanization finishes by v0.9. Walk and QSVT remain design stress
tests; implementing all six drafts is not a new v1 requirement. External
backends, entanglement analysis, dependent types and general resource grades
have no assigned release in this plan.

### Cross-release prerequisite: symbolic contract checking

The [symbolic kernel remains deferred](../ROADMAP.md#future-work-symbolic-semantic-kernel),
with **no selected target release**. Retain its design, research implementation
and regressions. This roadmap does not resume its implementation or assign its
integration to v0.2, v0.3, or the 0.1.x series. Before work depending on it starts,
make a separate scope/resumption decision through G020-1 and record the chosen
production contract profile.

The [R14 scaling condition](imaginary-v1/requirements.md#scaling-prerequisite-for-r14)
still gates generalization: compose symbolic meanings, encodings and evidence,
check interfaces and actual-IR binding independently, and use dense matrices
only for bounded leaves/regressions. Capability propagation alone cannot prove
that a concrete implementation realizes its promised logical operation.
Existing finite composition and the research prototype do not discharge this
production gate. Any roadmap row requiring it waits until it is met.

Before a generalized QPE claim, select its supported widths, Fourier-angle
representation, exact or approximate checking, error metric/budget and capacity
diagnostics as required by [R08/R12/R14](imaginary-v1/requirements.md#first-generalized-qpe-profile-decisions-required-by-r08r12r14).
Approximate algorithm accuracy never weakens exact auxiliary zero return.
The next-minor dossier may document these as blockers; finishing v0.1.9 alone
does not make v0.2 ready or satisfy executable V1-C1–C5.
