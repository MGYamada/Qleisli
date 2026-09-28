<a id="qleisli-v0x-roadmap-and-the-v019-boundary"></a>

# Qleisli milestones toward v1

Status: **revised development direction selected on 2026-09-27 for 0.1.5**.
The [decision dossier](decisions/2026-09-27-v1-path.md) selects the next scope
and bounded kernel restart. [Current states](current-status.md) are generated
from one record; the current [release record](releases/v0.1.9.md) separates local
validation and publication. The [0.1.5 record](releases/v0.1.5.md) retains the
original selection. This plan supersedes the 0.1.4 schedule, not its
historical evidence or the current finite language contracts.

<a id="decision-consolidate-the-finite-foundation-through-v019"></a>

## Decision: milestones are independent of release numbers

Use M0–M5 to schedule work. Choose a product version from the
[compatibility policy](versioning.md) when shipping a concrete change.
A compatible JSON diagnostic or sampling feature may ship in PATCH within
0.y.z (y > 0); incompatible changes require MINOR. No capability/size theme
reserves a release number. Audits run continuously and need no release of their own.

The [2026-09-28 version-policy revision](versioning.md) permits compatible
features in 0.1.x without exceptions. X1 check/run is recorded in the
[0.1.7 record](releases/v0.1.7.md); fixed-width operation parameters and meanings
are implemented in the [0.1.8 record](releases/v0.1.8.md), with their previously
selected version and explicit migrations preserved. The historical v0.1.9
checkpoint remains B019, without requiring patches 6–9 before new features.
New work retains its specification, semantic and validation gates, regardless
of the numeric bump. Later compatible work may use 0.1.10.

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

<a id="maintenance-work-targets-v014-through-v019"></a>
<a id="v02-toward-v1-capability-led-generalization"></a>

## Active milestones and dependencies

| Milestone | Selected scope and dependencies | Completion evidence |
| --- | --- | --- |
| M0: decide the path | Next-scope dossier, before new features. | Select a feasible M1 scope, capability representation, meaning language, angle policy, joint IR/evidence direction and bounded kernel go/no-go. A no-go needs dated reconsideration and cannot count as a completed handoff. [Scope selected](decisions/2026-09-27-v1-path.md); [M1 extension rules](next-minor-spec.md) and [machine interfaces](machine-interface-spec.md) specified. |
| M1: fixed-width composition and external interfaces | Depends on M0 and G020-1 specification. Static operation parameters with checked capabilities and conjugation; bounded basis-derived meanings; preserve existing special forms as elaboration. Portable finite evidence, JSON diagnostics and sample/trial APIs are separately shippable slices, versioned by compatibility. | One fixed-width body accepts distinct checked implementations, rejects unavailable access and stale/wrong-phase evidence; independent interchange mutation cases; actual samples and explicit failure results. Existing finite dense checks are permitted within unchanged bounds. No size-generalization or V1-C2 claim. |
| M2: scalable checking and QPE | Depends on M1's operation/evidence interfaces; specify hierarchical IR and proof binding together during M1. Bounded kernel production path, static sizes, ideal dyadic angles and shared multi-width QPE. | R14 and hierarchical-IR gates below, exact entry/cleanup, supported schema checks and phase/reference-sensitive QPE instrument cases. Same source across declared multiple widths and operations; QPE's contribution to V1-C2, not completion of all V1 criteria. |
| M3: Grover and host trials | Depends on M2 and R06 predicate synthesis. | Reusable preparation, oracle, reflection and iteration; no whole-space table construction for the declared predicate fragment; fresh sampling, candidate checks and retries. Evaluate Grover against V1-C1–C5. |
| M4: Shor with shared QPE | Depends on M2 and R09 arithmetic synthesis; may progress alongside M3. | Add/compare/reduce/uncompute implementation, whole-space modular meaning, controlled modular powers, exact scratch cleanup, shared QPE, actual samples, period/factor validation and explicit retry. Evaluate Shor against V1-C1–C5. |
| M5: costs and stabilization | Depends on M3 and M4. | Separate generation, checking, execution, oracle and classical costs; migration and stable public contracts; all executable V1-C1–C5 evidence. |
| Continuous maintenance and proof | Independent of release cadence; follow the verifier/kernel-first [proof order](formal-core.md#4-theorem-status-and-proof-work). | Rule/evidence audit dispositions, compatible fixes with regressions, Qleisli axiom audit (and a separate external audit if Physlib is reintroduced), honest proof premises and reproducible releases when selected. |

Walk and QSVT remain design stress tests, not additional executable v1 gates.
The [2026-09-28 interoperability direction](interoperability-roadmap.md) adds
independently shippable M1 slices: Python access to the shared compiler/checker,
bounded OpenQASM 3 import/export and QIR Base output/input, followed by a
specified adaptive fragment. [M1.1-A](interop-m1.1.md) now specifies and implements
the bounded OpenQASM adapter and QIR output; QIR import, adaptive behavior and
Python extension specifications/implementations remain pending. Early finite interoperability can precede operation parameters and M2,
while the hierarchical IR/evidence and R14 gates remain prerequisites for sizes.

The [2026-09-28 source-authoring corpus](qli-authoring-feedback.md) supplies
executable evidence for missing tuple/basis ergonomics and type-level QPE reuse.
Its finite-template-before-R14 suggestion is an open scheduling alternative;
it changes neither the current size gate nor the V1 acceptance criteria.
The [v0.2.0 backlog](v0.2.0-backlog.md) collects these authoring issues with
stable IDs, source evidence and acceptance experiments. It supplies scope-review
inputs without duplicating active milestone states or assigning all M2 work to 0.2.0.

The [coefficient-domain recommendation](coefficient-domains.md), also recorded
on 2026-09-28, keeps future exact-domain parameterization separate from
approximation and device contracts. It is preparation for uncertain future
gate sets, not an implementation or a change to the selected M2 profile.

No release date or completion of general compiler mechanization follows from
this table. The **2026-10-04 JST** scope checkpoint in the dossier evaluates
M1 specification and M2 kernel/IR feasibility, not release publication.

<a id="cross-release-prerequisite-symbolic-contract-checking"></a>

### Cross-release prerequisites

| Prerequisite | Gate |
| --- | --- |
| Symbolic meaning/encoding/evidence composition (R14) | Before size generalization in M2, independently check actual implementation binding with bounded leaves and shared proofs, without a global dense operator. Fixed-width M1 may retain current bounded whole-function checking. |
| Hierarchical IR and evidence binding (R02/R04) | Design with proof interchange in M1; validate shared calls, static loops, parameterized families and checked transformations in M2. Compact proofs over fully expanded IR do not pass. Breaking public enum/field changes require MINOR migration. |
| Reversible synthesis without truth tables (R06/R09) | Required for M3 predicates and M4 arithmetic. Construct and certify circuits from a declared expression fragment, including zeroed scratch and whole-space behavior. No enumeration of every basis input as the delivered general construction. |

These are complementary gates. Satisfying one does not establish the others.
[R14 and the QPE profile](imaginary-v1/requirements.md#scaling-prerequisite-for-r14)
state the detailed obligations; the [dossier](decisions/2026-09-27-v1-path.md)
selects ideal dyadic QPE angles and a limited per-size checker. General symbolic
equality, arbitrary proof search and an all-n theorem are not required.
Production integration remains unimplemented.

<a id="v019-acceptance-boundary"></a>

## Finite maintenance checkpoint (legacy B019)

The old v0.1.9 name remains a linkable checkpoint, not a mandatory release train.
It requires all rows below and does not delay independent M1 specification work.
New public features and symbolic-kernel development/integration follow the
M1/M2 gates above rather than this maintenance checklist. This is a scope
distinction, not a ban on compatible features in 0.1.x.

The [initial boundary check](reviews/b019-2026-09-28.md) found B019 incomplete.
The subsequent [completion record](reviews/b019-completion.md) records the F2
repair, completed review dispositions and actual candidate validation. The
[code-driven handoff](code-driven-development.md) fixes the next work packets
and obstacles without changing the acceptance conditions below.

| ID | Required evidence |
| --- | --- |
| B019-1: compatibility | Preserve grammar, APIs, semantics, capacities and toolchains. For a patch fixing erroneous acceptance, record the already violated rule, before/after result, diagnostic and regression. |
| B019-2: finite assurance | Revalidate V01-C1–C6 within declared bounds, including unchanged clients with substitutable implementations, phase, layout, complete ownership, exact cleanup and reference-sensitive cases. |
| B019-3: audit dispositions | Publish rule/implementation/test/proof and evidence-boundary inventories; resolve discovered supported-contract defects. Inventory coverage and audit completion are separate. |
| B019-4: proof ledger | Separate paper/Lean results, Rust correspondence and remaining verifier/numerical assumptions; retain project/external axiom audits. Whole-compiler proof is not a completion condition. |
| B019-5: selected next scope | Keep the six drafts and R01–R14 current; select the next scope under G020-1 and provide its complete extension specification, compatibility and checking decisions. Record a bounded kernel go/no-go with a date and owner; no-go permits only dated reconsideration, not checkpoint completion. [M1 specification](next-minor-spec.md), [machine interfaces](machine-interface-spec.md), [M2 profile](hierarchical-ir-spec.md) and dated go decision now supply this handoff. M2 sized source grammar remains separate. |
| B019-6: reproducibility | On an actual release candidate run the version policy's primary/MSRV Rust, research, docs/helpers, pinned Lean/audits, representative execution and distribution/attribution checks. Separate local results, exact-commit CI, tag, push and publication. |

## Tracker handoff

Use M1–M5 as GitHub milestone titles without product-version numbers. The
following issue titles and linked acceptance bodies are ready for a requested
tracker publication. The maintainer owns scope decisions; an implementer is
assigned when work starts. This local handoff creates no external issue,
notification or second mutable status ledger. Current states remain in
[project-status.json](project-status.json); link tracker records back to it.

| Issue title | Milestone / acceptance body | Dependency |
| --- | --- | --- |
| Implement fixed-width static operations and meaning contracts | M1 / [N1–N6](next-minor-spec.md#implementation-acceptance-matrix) | Selected specification |
| Add versioned JSON command results | M1 / [X1](machine-interface-spec.md#required-conformance-before-shipping) | None of M2 |
| Add independently checked finite IR interchange | M1 / [X2–X3](machine-interface-spec.md#required-conformance-before-shipping) | QIRF1 first; QIRF2 depends on new meaning evidence |
| Add trajectory sampling and typed trial outcomes | M1 / [X4–X5](machine-interface-spec.md#required-conformance-before-shipping) | Existing verified IR; JSON mode after X1 |
| Add bounded source loading with explicit legacy migration | M1 / [X6](machine-interface-spec.md#required-conformance-before-shipping) | MINOR capacity change |
| Specify and implement the Python host binding and wheel distribution | M1 / [interoperability gates](interoperability-roadmap.md#required-evidence-and-scheduling) | Complete Python extension contract; X4 before exposing sampling |
| Bounded OpenQASM 3 import/export | M1.1-A / [terminal profile](interop-m1.1.md) | Bounded terminal profile implemented, validated and released in [0.1.7](releases/v0.1.7.md); extensions need their own gates |
| QIR Base output/input | M1.1-A/B / [connection gates](interop-m1.1.md#acceptance-and-remaining-gates) | Bounded output validated and released in [0.1.7](releases/v0.1.7.md); standard-reader input and its adversarial acceptance checks pending |
| Implement bound hierarchical proofs and the QPE schema profile | M2 / [H1–H5](hierarchical-ir-spec.md#migration-and-implementation-gates) | M1 operation interfaces; required Lean schemas and sized source specification |
| Synthesize predicate oracles and shared Grover | M3 / [Boolean DAG contract](hierarchical-ir-spec.md#synthesis-without-complete-truth-tables), V1-C1–C5 | M2 and sampling |
| Synthesize modular arithmetic and shared-QPE Shor | M4 / [arithmetic contract](hierarchical-ir-spec.md#synthesis-without-complete-truth-tables), V1-C1–C5 | M2 and sampling |
| Stabilize cost reports and executable v1 evidence | M5 / [V1-C1–C5](release-milestones.md#v1-acceptance-target-textbook-algorithm-structure) | M3 and M4 |

Continuous verifier/kernel proof work and finite audits are not separate
mandatory patch milestones. A discovered defect gets a concrete issue with
the violated current rule and reproducer; an audit alone does not demand a release.

## Legacy ID mapping

Retain IDs and historical anchors instead of renumbering old evidence.

| Previous planning label | Active home |
| --- | --- |
| v0.1.5 conformance / v0.1.6 evidence audit | Continuous maintenance; current inventory links rules, implementations, tests and proof gaps. |
| v0.1.7 correspondence | Continuous verifier/kernel-first proof work, then frontend adequacy. |
| v0.1.8 decision dossier | M0, brought forward to this change. |
| v0.1.9 / B019 | Finite maintenance checkpoint above; no automatic no-go completion. |
| v0.2–v0.9 themes | M1–M5 by dependency, without a reserved version assignment. |
| G020-1 / G020-2 / G020-3 | Extension specification / implementation / validation gates for the selected scope; fixed-width M1 and sized M2 have different acceptance profiles. |
| G013-S0–S2 / G013-S3 | Retained initial research artifacts / M2 production integration obligation. |
| Stage/SPEC, A/L and local proof labels | Historical work areas and proof references, not new scheduling milestones or product versions. |
| R01–R14 / V01-C / V1-C | Requirements / finite and executable-v1 acceptance criteria; retain their semantic identities. |

[Historical release records](releases/v0.1.4.md) retain original plans, test
counts and publication evidence. This mapping changes scheduling, not theorem
statements or the current grammar.
