# Qleisli release milestones and north star

Status: **project direction adopted by the user on 2026-09-27; v0.1's declared
finite acceptance profile is implemented and checked; v1 remains unmet**.
This English document is the authoritative record
of the project north star and v0.1/v0.5.0/v1 release conditions. The English summaries in the
[roadmap](../ROADMAP.md) and [algorithm goal](algorithm-structure-goal.md)
follow it. It adopts the direction evaluated in the
[semantic-contract review](semantic-contract-proposal-review.md). The first
[finite checker and source extension](semantic-contracts-v0.1.md) and
[retained function evidence](function-contracts-v0.1.md) form the completed
bounded path. The [conformance ledger](specification-status.md) records its
acceptance evidence, capacity limits, and remaining proof obligations.

The finite core **specification v0**, the development **stages 0–5**, and
these **release milestones v0.1/v0.5.0/v1** are different labels. The existing Rust
package version and the standard-library ledger's “format v1” do not
establish completion of either release milestone. Release claims require the
evidence below, not a manifest version or successful fixed-size example.

The adopted initial product baseline is **0.1.0**. The
[versioning policy](versioning.md) defines compatibility, synchronized package
versions, release validation, and immutable Git tags. The
[changelog](../CHANGELOG.md) and [0.1.0 release notes](releases/v0.1.0.md)
record its contents and validation scope. The Git tag and GitHub release
identify the released commit and publication state; registry publication is
a separate operation.

Current version selection, milestone states and the finite-rule inventory are
in the [generated status](current-status.md). The [0.1.9 record](releases/v0.1.9.md)
separates compatible review maintenance and local validation from publication;
the [0.1.8 record](releases/v0.1.8.md) preserves M1/authoring migrations.
Compatible features follow the revised PATCH policy.
The [M0–M5 plan](v0x-roadmap.md) supersedes the 0.1.4 version-assigned schedule;
older [release records](releases/v0.1.4.md) retain their historical evidence.
The [six initial drafts and requirements](imaginary-v1/README.md), their
[semantic review](imaginary-v1/review.md), and the English specification
groundwork are complete as design artifacts. This satisfies the corpus
prerequisite below; future features still need their own specifications and
validation. Selecting this patch version does not complete v1.

The subsequent v0.1.3 research goal is a first-principles
[meaning/implementation architecture](symbolic-contract-architecture.md) and
an [independent exact-pure prototype](../research/semantic-kernel/README.md).
It checks a limited symbolic profile and binds evidence to supported actual
raw IR. Its non-published package does not change production compiler APIs.
The design's G013-S0–S2 gates concern this initial slice; G013-S3 source/entry/
release integration and generalized algorithms remain future work. Public
feature adoption still requires an extension specification, independently of
the compatibility-based version increment.
The [0.1.5 decision dossier](decisions/2026-09-27-v1-path.md) now selects a
bounded M2 continuation, replacing indefinite deferral. It does not change
past release conditions or implement production kernel features. Fixed-width M1
retains finite checking; size generalization requires R14 and hierarchical IR, and
general predicate/arithmetic construction additionally requires circuit
synthesis without whole-space truth tables.

## 0.2.0 foundation and 0.2.1 shared-QPE continuation

**User scope revision, 2026-09-29.** The [0.2.0 plan](v0.2.0-plan.md) now
ships implemented tuple/type and resource-policy changes, finite X2–X6, and
experimental Lean components with their actual proof limits. Its remaining
gate is migration/contract/status alignment and final primary/MSRV Rust,
corpus/docs/examples, pinned Lean build/audit and clean distribution validation.
Tagging, push and publication remain separately recorded operations.

The [0.2.1 target](v0.2.1-plan.md) carries the four remaining areas: full
hierarchical semantics/evidence, independently bound production verification,
sized source/shared QPE/QFT, and reference execution with integrated H1–H5.
The previous multi-size, instrument/reference, phase, mutation, capacity,
cost and reuse criteria move unchanged. They are deferred, not satisfied;
0.2.0 must not claim a production hierarchical checker or reusable sized QPE.
Existing experimental components remain built and audited, with external
schema acceptance disabled until the required proof/binding gates pass.

0.2.1 requires a compatible public extension. If implementation needs a
breaking AST/API/format or capacity change, select 0.3.0 under the existing
version policy. M0–M5, R14, S05-C1–C5, PR-C1–C4 and the independent QLT plan
retain their obligations. No manifest bump or release completion follows from
this scheduling revision.

## Qleisli Soundness Theorem (v0.5.0)

<a id="qleisli-soundness-theorem-v050"></a>

**Adopted target, 2026-09-29; not yet proved.** Proving the **Qleisli Soundness
Theorem** is the central v0.5.0 milestone, alongside the K3 transfer of production
verification to Lean and readiness for broader open-source development.

For the published v0.5.0 verification profile, let `p : RawIR₀.₅`,
`C : Contract₀.₅` and `π : Evidence₀.₅`. The target is a Lean theorem about
the actual executable checking definition:

\[
\forall p,C,\pi,\quad
\operatorname{verify}_{0.5}(p,C,\pi)=\mathrm{true}
\;\Longrightarrow\;
\operatorname{ResourceSafe}(p)\;\land\;
\operatorname{EffectSound}(p,C)\;\land\;
\llbracket p\rrbracket\models C.
\]

These are specification names for the planned definitions, not existing Lean
declarations. `C` is independently fixed by the caller; any entry premises are
explicit. Satisfaction covers every admissible input and arbitrary finite
reference system, including entangled inputs. Pure contracts compare complex
linear operators with exact phase and explicit type/axis encodings. Observing
contracts describe the complete classical–quantum instrument and its branch
probabilities and residual states. Auxiliary release requires exact zero
return and separation from the remaining system and reference. An isometry
contract alone does not grant inverse or controlled access.

| Gate | Required v0.5.0 evidence |
| --- | --- |
| **S05-C1: complete declared scope** | Publish the profile, capacities, entry premises and inventory of every enabled IR/evidence rule and production acceptance path. Preserve the required positive corpus and algorithm gates; a rejecting checker or a phase-word-only theorem cannot satisfy this milestone. Unsupported paths must reject explicitly, with versioned migration for any removed support. |
| **S05-C2: actual checker soundness** | Compose resource/effect, exact-arithmetic interpretation, semantic-contract, hierarchy and instrument proofs into the theorem above. Cover every enabled rule. No remaining assumption that a Rust checker or an unproved evidence producer accepts correctly may substitute for a required proof. |
| **S05-C3: reproducible proof and audit** | Bind the theorem and reviewed statement to the released executable definitions; reproducible builds, declaration/axiom audits and proof replay pass. Keep the runtime Mathlib-free and mathematical interpretation proofs separate. Record native compiler/runtime and transport assumptions explicitly. |
| **S05-C4: production binding** | Complete K3: reconstruct serialized evidence against the independent request, bind the accepted IR to the executed/emitted artifact, pass differential/adversarial/platform checks and fail closed on kernel/transport failure. No silent Rust fallback. |
| **S05-C5: public review and contribution readiness** | Publish the theorem explanation, coverage/assumption ledger and reproduction commands; record independent review and resolve blocking findings. Prepare contributor setup, bounded issues, proof/code review rules, maintainer responsibilities and release/security reporting procedures for the v0.5 community expansion. |

This is the **verification-kernel soundness theorem**. General source-lowering,
optimizer and backend meaning preservation remain K4 translation-validation
work. Native compilation, approximate numerical execution, algorithm success
and physical hardware correctness are separate claims. The existing cyclic
phase-word `verify_sound` is a proved precursor, not this completed theorem.
If a gate remains open, report v0.5.0 as pending rather than weakening the
theorem or relabeling local tests as its proof. No release date is selected.
Later releases must extend this coverage for newly enabled acceptance rules
and continue to publish the theorem profile and its remaining trust assumptions.

## Physical Realizability Theorem (v1)

<a id="physical-realizability-theorem-v1"></a>

Adopted target, 2026-09-29; not yet proved. By v1, prove the Physical
Realizability Theorem alongside a substantive Lean 4 backend. This is a
required continuation of soundness: valid quantum semantics must be connected
to the circuit actually produced for a declared target gate set.

For the finite, terminating supported profile and each admissible classical
input, derive CPTP semantics as a corollary of the Qleisli Soundness Theorem.
Retaining every outcome gives a classical–quantum CPTP map; summing the outcome
maps also gives a CPTP map. An individual measurement branch is generally only
completely positive and trace-nonincreasing, not trace preserving.

The realizability target constructs an isometric dilation of that complete
map, then synthesizes the isometry over the declared gate set, with specified
initialization, readout and environmental discard. Prove that the actual Lean
backend's output realizes the checked instrument, including outcome labels,
residual states and arbitrary reference systems. For pure operations, retain
operator phase and the stronger isometry/unitarity contracts; channel equality
alone does not justify coherent control. Environmental discard is not pure
auxiliary release: workspace promised clean must still return exactly to zero.

| Gate | Required evidence by v1 |
| --- | --- |
| PR-C1: semantic bridge | Prove the CPTP corollary and constructive dilation for the complete supported profile, with explicit entry/encoding premises, outcomes and references. |
| PR-C2: gate synthesis | Specify the target gates and preparation/readout capabilities, then prove synthesis of the dilation. State which operations are exact; any approximation needs a declared error metric and certified bound that accounts for arbitrary references and composition. A finite gate set's universality alone is not an exact-synthesis proof. |
| PR-C3: actual backend correspondence | Implement the relevant backend transformations in Lean and prove their connection from the accepted IR to the actual emitted target program, covering lowering, optimization, layout and emission. Bind every stage to its checked input/output; source-to-IR translation validation remains a separate prerequisite for source-level claims. |
| PR-C4: release evidence and trust | Publish the supported profile, proof/coverage and assumption ledger, reproducible audits and independent review. Include the three v1 algorithm families; unsupported target capabilities reject explicitly. Record remaining native compiler/runtime, transport and physical-device assumptions. |

These are adopted proof and implementation gates, not existing Lean declarations
or a hardware-noise guarantee. The executable backend follows the Mathlib-free
runtime boundary; separate proof libraries may provide its mathematical bridge.
The longer-term migration aims to cover the implementation beyond the frontend.
Under this project direction, a Lean backend with actual-transformation proofs
is necessary for the goal “LLMs write `.qli`; Lean guarantees it all the way
down”; merely moving code to Lean is insufficient. V1 requires PR-C1–C4 in
addition to the existing algorithm gates V1-C1–C5.

## Project north star

**Make the language people use to think about quantum algorithms coincide
with the language they use to write programs.**

State preparation, oracles, reflections, phase estimation, uncomputation,
and their composition should be usable program concepts with the same
mathematical meanings. Their contracts must survive implementation choices
and lowering. This calls for readable, executable abstractions with checked
meaning, not only familiar names or natural-language descriptions.

This wording, adopted on 2026-09-27, expresses the overarching direction.
The three algorithm families below remain its concrete v1 acceptance test.
The v0.1 contract layer supplies the link between those concepts and the
implementations that realize them.

## v0.1 minimum: semantic contracts

**v0.1 must carry a mathematical meaning contract through composition and
independently check that the actual implementation realizes it.** The first
fragment is finite-dimensional pure operations with exact phase:

```text
u : L_in -> L_out                 logical operation
U : P_in -> P_out                 ideal circuit/IR implementation
E_in : L_in -> P_in               input encoding
E_out : L_out -> P_out            output encoding

E_in† E_in = I,   E_out† E_out = I,   U† U = I,
U E_in = E_out u.
```

The contract fixes u, the encodings, exact types, phase conventions and layouts.
Entry evidence establishes the encoding promise. The implementation's global
isometry, and unitarity where required, must be checked independently of the
encoded-subspace equation. It remains subject to the ordinary resource/effect
checks, including zero-width owners.
The contract concerns ideal operators; it does not certify noisy hardware.

All conditions below are necessary. They can begin with a declared bounded
fragment and concrete function signatures; general size and operation
parameters are not prerequisites for this first milestone.

| ID | Minimum acceptance condition | Current status |
| --- | --- | --- |
| V01-C1 | Specify finite contract/evidence forms with well-typed spaces, checked isometric encodings, entry evidence, exact logical meaning, full ownership interfaces, and phase. Record source-to-IR attachment and trust boundaries. | Met in the declared finite profile: [SC specification](semantic-contracts-v0.1.md), [FC specification](function-contracts-v0.1.md), checked encodings, and exact source signatures. General encoded-state handles remain outside this profile. |
| V01-C2 | Implement an independent evidence checker with primitive identities, sequential/tensor composition, explicitly qualified inverse/control rules, and bounded exact matrix comparison. Record a soundness argument for its rules. Proof search is outside the trusted checker; failure to find/check evidence never authorizes a contract or cleanup. | Met: bounded exact checker, identity and compositional constructors; SC/FC paper soundness arguments and [kernel regressions](../tests/semantic_contracts.rs). Rust implementation is not formally proved. |
| V01-C3 | Bind evidence to the actual source/function contract and final IR, including parameters, output ordering and dependencies. Check transformations or recheck their results. Preserve existing type, ownership, effect and independent raw-IR validation. | Met: raw `CertifiedCompute` rechecks retained W/u; `FunctionEvidence` independently checks both complete raw functions and binds their frozen source/dependency snapshots. Final contract actions retain this evidence under axis remapping, adjoint, control, and repetition. [Raw evidence regressions](../tests/function_evidence.rs) cover binding and extraction. |
| V01-C4 | Through the implemented compiler/checker, certify a phase oracle, auxiliary H;H, and the f(x)=x data/auxiliary simultaneous X example using the same evidence rules. Establish exact zero return and separation over all encoded inputs and arbitrary references. | Met: [certified source tests](../tests/certified_source.rs) and [runnable examples](../examples/semantic_contracts/README.md) use the same exact full-column equation; the reference extension follows by tensoring that equation with identity. Numerical reference tests supplement it. |
| V01-C5 | Publish concrete function contracts that can be reused compositionally. Exchange at least two implementations of one fixed phase-oracle contract while leaving its logical client unchanged. Independently check the resulting IR, including reuse under coherent control and with a correlated reference. Different private auxiliary layouts must be hidden by checked interfaces. | Met: `apply_contract` fixes the client's specification. [One unchanged client](../tests/function_contracts.rs) accepts direct Z and two private-auxiliary implementations, with coherent control and an entangled reference. Calls share immutable evidence; nested composition and static transforms retain it. [Executable example](../examples/function_contracts/README.md). |
| V01-C6 | Reject auxiliary-only X, incorrect phase/predicate, incompatible encoding or layout, missing entry evidence, invalid inverse/control premises, stale or mismatched certificates, and lost/duplicated ownership. Record exact checks, limits, diagnostics, assumptions, and proof/implementation/test status separately. | Met in the bounded profile: kernel, source, and raw-function rejection tests, changed-source/dependency tests, and finite checking/execution budgets. Exact proof checks and approximate reference results are separately recorded in the [ledger](specification-status.md). |

The existing [39 exact example checks](../scripts/check_semantic_contract_examples.py)
and current regression tests are supporting evidence. They do not satisfy
V01-C2–C6 by themselves. A gate whitelist relaxation, a numerical simulation,
or a document containing the desired equation is insufficient.

The initial inverse rule may require both logical and implementation operators
to be unitary. Initial coherent control may require identical input/output
encodings. Mathematical evidence does not grant inverse/controlled access
to an unknown device. Exact cleanup must remain separate from approximate
logical accuracy; approximate leakage never permits pure release. Observation
uses instrument contracts, and general block encoding uses a projected-block
contract; neither is silently treated as exact pure intertwining.

Full mechanization of every Rust compiler path is not asserted by this
milestone. The checker rules, implemented fragment, source/IR correspondence
evidence, and remaining trusted implementation obligations must be explicit.
Existing [Stage 1 proof obligations](formal-core.md) remain in force; meeting
this release gate does not retrospectively mark all of SPEC-4 complete.

<a id="v019-maintenance-boundary"></a>

## v0.1.9 maintenance acceptance boundary

The broader legacy checkpoint was completed for the recorded 0.1.9
candidate; see the [six-condition completion evidence](reviews/b019-completion.md).
The conditions below remain unchanged, and are distinct from the new 0.2.0 gates.

**Legacy checkpoint, revised by the 0.1.5 review; subsequently completed in 0.1.9.** The
[B019-1–B019-6 conditions](v0x-roadmap.md#v019-acceptance-boundary) require
compatibility, finite assurance, audit dispositions, an honest proof ledger,
a selected next scope with a complete extension specification, and reproducible
release checks. Maintenance audits are continuous, not assigned to mandatory
patch releases. M1 specification can proceed alongside them.

B019-5 no longer accepts a no-go as completion. It requires G020-1 scope and
specification plus a dated kernel go/no-go decision; a blocker requires dated
reconsideration. [M0](decisions/2026-09-27-v1-path.md) selects fixed-width M1 and
a bounded M2 kernel path, with a 2026-10-04 JST implementation-readiness checkpoint.
The [M1 rules](next-minor-spec.md), [external contracts](machine-interface-spec.md)
and [M2 checker profile](hierarchical-ir-spec.md) complete the selected design
handoff. The completion record supplies the remaining audit and reproducibility
evidence. Pending M1/M2 features are separately tracked in the
[0.2.0 development record](releases/v0.2.0.md).

New public APIs, syntax, size generalization and kernel integration require
specification and validation. Use PATCH for compatible changes in 0.y.z (y > 0)
and MINOR for incompatible ones, under the [version policy](versioning.md).
R14 gates size generalization in M2; existing bounded dense checks remain
permitted for fixed-width M1. Hierarchical IR and circuit-based
predicate/arithmetic synthesis are complementary scaling gates. V1-C1–C5 are
unchanged. Later maintenance may use 0.1.10; patch 9 does not force a minor.

<a id="v1-north-star-textbook-algorithm-structure"></a>

## v1 acceptance target: textbook algorithm structure

**Shor, QPE, and Grover should read as the structure of the quantum algorithms
found in a textbook, rather than as circuit diagrams transcribed into code.**

This makes the project north star concrete for v1. Algorithm definitions should
show mathematical stages, their composition, and the assumptions necessary
to use them. Primitive gates, wire permutations, arithmetic decomposition,
auxiliary management and proof derivations belong inside checked components.
Readers can inspect those implementations, but should not need to reconstruct
a gate diagram to understand the algorithm definition.

The following describes required structure, **not proposed `.qli` syntax or
existing public function names**:

| Algorithm | Structure visible in its implementation source | Contracts visible at the relevant interface |
| --- | --- | --- |
| Grover | Prepare the search state; apply the marked-state phase oracle and the reflection about the prepared state; repeat the amplification step under an explicit iteration policy; measure and check the candidate. | Preparation and inverse access where required, the predicate and exact reflection/oracle phases, search size, iteration/success assumptions, and resource/effect boundaries. |
| QPE | Prepare the phase register; compose controlled powers of the input operation; apply inverse QFT; measure and decode the phase estimate. | Phase-fixed controlled/power access, register size/precision, bit order, approximation and statistical guarantees where used, and the outcome/residual-state instrument. Eigenstate promises must be explicit; general inputs have a distribution over eigencomponents. |
| Shor | Perform classical preprocessing and select a base; construct the modular-multiplication operation; obtain order information through the shared QPE structure; reconstruct and validate a period candidate; extract and validate factors; handle unsuccessful samples and retry according to a declared policy. | Coprimality and arithmetic domains including behavior outside the valid residue subspace, controlled modular powers, phase precision, classical reconstruction, failure conditions and resource/cost assumptions. A host retry boundary is explicit if used. |

Shor must reuse the QPE component rather than hide a second hand-expanded
phase-estimation circuit. A single top-level call named after an algorithm
is not enough: the delivered definition of that algorithm must expose these
stages. The quantum/classical boundary and retry behavior are part of the
delivered workflow, even when a documented host layer owns them.

For Shor, classical validation includes the early GCD factor case and checking
a positive period candidate r with `a^r mod N = 1`. Factor extraction checks
that r is even, `a^(r/2)` is neither `1` nor `-1` modulo N, and the resulting
GCDs give nontrivial factors. Failed checks follow the stated retry policy.
A period check alone does not establish that r is the least order. Samples
come through the declared execution/measurement interface; access to a
simulator's full output distribution cannot replace this workflow.

| ID | v1 acceptance condition |
| --- | --- |
| V1-C1 | Deliver real source definitions of all three algorithms that compile and run within a declared supported profile. A reviewer can map their named stages and composition to the table above without reading primitive gate bodies. Pseudocode, comments, a renamed monolithic circuit, or an unimplemented black-box API do not pass. |
| V1-C2 | Reuse the same definitions across multiple supported sizes, precisions, predicates/operations and problem inputs as appropriate. Size and operation parameters replace manually duplicated fixed instances; current 2/3-bit QPE and N=15 examples alone do not pass. |
| V1-C3 | Carry the v0.1 meaning contracts through component boundaries to checked IR. Demonstrate implementation substitution without rewriting algorithm structure. State access capabilities and all additional instrument/accuracy contracts used by the algorithms. |
| V1-C4 | Validate mathematical behavior as well as readability: phase-sensitive and reference-sensitive cases, failure/retry paths, and independently derived expected results. QPE sampling alone is not an order proof, an unverified candidate is not a factor, and a valid circuit alone is not an algorithm-correctness proof. |
| V1-C5 | Keep source structure stable when changing implementation layout or decomposition. Report circuit-generation and execution costs separately, including oracle access and classical work. Precomputed answers or whole-space truth-table enumeration cannot stand in for the delivered general arithmetic/algorithm construction. Publish supported bounds and proof status. |

V1 does not require a claim of practical hardware advantage, unlimited-size
execution, or completion of every algorithm in the corpus. It requires a
usable, checked abstraction for these three algorithm families. Any
approximation used to support larger QFTs or other components has an explicit
error contract; it does not weaken exact auxiliary-cleanup requirements.

The [Physical Realizability Theorem and PR-C1–C4](#physical-realizability-theorem-v1)
are additional v1 requirements under the 2026-09-29 backend migration decision.
V1-C1–C5 retain their algorithm-specific meanings.

<a id="pre-v020-imaginary-v1-code"></a>

## Prerequisite before v0.2.0: imaginary Qleisli 1.0 code

Status: **adopted by the user on 2026-09-27; initial code corpus and requirement
records completed and reviewed on 2026-09-27**. The
[artifact index](imaginary-v1/README.md), [requirements](imaginary-v1/requirements.md),
and [review](imaginary-v1/review.md) establish this limited prerequisite.
All code remains imaginary and uncompiled; future specification, implementation,
validation, and proof are separate.

The [0.1.2 roadmap](releases/v0.1.2.md) records the corpus and requirement
records as documentation deliverables. Completion follows the linked artifacts
and review, not the plan or version number, and does not fix future syntax/APIs.

**Write the ideal algorithm code in an imaginary Qleisli 1.0 first, before
starting v0.2.0 feature implementation and before releasing v0.2.0.** This
design prerequisite precedes size/operation generalization and the new
abstractions or standard APIs intended for that release. Existing finite-core
maintenance, regression checks, and open proof work can continue.

The initial corpus must include **QPE, Grover, amplitude estimation, Shor,
quantum walk, and QSVT**. Write each algorithm's intended definition, exposing
its mathematical stages, composition, and relevant parameters. A list of
algorithm names or calls to undefined whole-algorithm functions does not
satisfy this prerequisite. The code may use proposed syntax and APIs and
**need not compile yet**; label it explicitly as imaginary Qleisli 1.0 design
code, separate from executable examples and normative source syntax.

For each draft, record its intended input/output and meaning, required
capabilities, ownership/effects, phase and cleanup obligations, and any
accuracy, success/failure, or classical-processing assumptions. Mark unresolved
contracts explicitly. Link the drafts from a corpus index and identify the
missing language forms, sealed operations, ordinary definitions, evidence
rules, and source-to-IR support needed to make the code meaningful; record
unresolved classifications as such. These initial drafts and their requirement
records establish the prerequisite, without requiring implementation or proof
of all proposed operations.

Use the corpus with AI to work through those requirements one by one. Revise
both the imaginary code and the design when semantic analysis or counterexamples
expose a problem; the drafts do not freeze the 1.0 grammar or public APIs.
Keep draft, specification, implementation, validation, and proof status separate.
AI-generated code and evidence follow the same independent checking boundary.

This prerequisite does not expand the executable v1 acceptance target beyond
V1-C1–C5 for Shor, QPE, and Grover. The broader drafts test the proposed
abstractions; their existence does not establish executable support or v1
completion. Record corpus completion with artifact links in the conformance
ledger before advancing to v0.2.0 implementation or release. Adoption of this
policy alone does not complete the prerequisite or change the product version.

## Work order and design decisions

1. Continue the finite-core source/IR and ownership-state work needed to
   identify the contract boundary and preserve its premises.
2. Complete V01-C1–C6 as one finite implementation path: specification,
   independent checker, source/IR evidence, positive and negative examples,
   and exchangeable phase-oracle implementations. Publish the v0.1 evidence.
3. Complete the [imaginary Qleisli 1.0 code prerequisite](#pre-v020-imaginary-v1-code)
   before v0.2.0 feature implementation. Derive the required abstractions and
   contracts from the initial algorithm drafts.
4. Follow the [selected M1/M2 boundary](v0x-roadmap.md): first specify fixed-width
   operation/access/meaning interfaces using bounded finite checks, then
   generalize sizes with symbolic meanings/encodings, hierarchical implementation
   IR and independently checked evidence. R14 prohibits whole dense expansion
   at that second step. Specify ideal dyadic QPE angles, declared bounds and
   actual implementation binding; general predicate/arithmetic work must also
   avoid whole-space truth-table synthesis. Existing finite matrices remain
   a bounded reference path, not the scalable architecture.
5. Implement reusable Grover and QPE structures and use QPE in Shor's complete
   quantum/classical workflow. Evaluate V1-C1–C5 on real source and evidence.

For each proposed abstraction, ask which algorithm stage it makes readable,
which programmer obligation it removes, which mathematical contract and
replacement evidence it exposes, and how that evidence survives independent
checking, lowering and substitution. A more compact gate listing alone does
not meet the north star. Broader library work follows the needs and verified
reuse of these structures.

This order refines the [existing roadmap](../ROADMAP.md); it does not turn
the legacy stage numbers, A0–A4, or L0–L5 into release numbers. The algorithm
corpus and existing finite examples remain regression material. New source
forms and APIs still require their normal specification, ownership/effect,
semantics, IR and conformance records before implementation claims.
