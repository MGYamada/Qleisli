<a id="qleisli-ロードマップ"></a>

# Qleisli roadmap

Status: the [design principles](docs/design-philosophy.md) are fixed. [Goal 1: a quantum language for the AI era](docs/ai-era-goal.md) and [goal 2: structuring quantum algorithms](docs/algorithm-structure-goal.md) remain in development. [Layer 3: a standard algorithm vocabulary](docs/stdlib-roadmap.md) has a v1 contract ledger and finite static-operation implementations. Stage 0 is complete as documentation; Stage 1 has a normative finite-core v0 specification but unfinished proofs; Stages 2–4 are partially implemented. Alongside minimal examples such as Bell, shared components build finite Grover, BV, bit-flip correction, QPE, and N=15 order-finding examples. Completion is judged against documented criteria and evidence. The [frontend documentation](docs/frontend-v0.md) distinguishes executed `.qli` from unimplemented syntax proposals.

This is the authoritative English development plan. The [release milestones](docs/release-milestones.md) and version-specific release records govern acceptance and publication. Historical entries below retain the scope, dates, and counts of their original checks; English translation does not rerun those checks or adopt future syntax. See the [documentation map](docs/documentation-map.md) for authority and translation status.

<a id="採用したリリース到達条件2026-09-27"></a>

## Adopted release milestones (2026-09-27)

**North star: make the language people use to think about quantum algorithms coincide with the language they use to write programs.**

For v1, Shor, QPE, and Grover must be readable in their textbook quantum-algorithm structure. The v0.1 semantic contracts form the foundation connecting those concepts to actual implementations.

| Release | Required milestone | Status |
| --- | --- | --- |
| v0.1 | Compose finite semantic contracts and evidence for `U E_in = E_out u`, reuse them at function boundaries, and independently check implementation correspondence through final IR. Substitute multiple implementations of the same phase-oracle contract without changing the client. Preserve phase, ownership, and exact auxiliary zero return. | V01-C1–C6 implemented and tested in the declared finite profile: public function contracts, dependency/final-IR evidence, and implementation substitution are connected. |
| v0.1.1 | Collect compatible review fixes, diagnostics, and regressions while preserving finite-core public contracts. | Implementation and local candidate validation remain recorded. Actual commit, Linux CI, and publication are identified by the [GitHub release record](https://github.com/MGYamada/Qleisli/releases/tag/v0.1.1). |
| v0.1.2 | A design/documentation maintenance release with six imaginary-v1 initial drafts, a requirements index, and semantic review. | Released with Rust/Lean versions 0.1.2. The English specification framework, drafts, index, and review are complete. Subsequent English documentation consolidation, candidate checks, and publication are distinguished below. |
| v0.1.3 | Repair auxiliary matrix-checker shapes and nonfinite comparisons, verify the v0.1.2 review, retain independent semantic research, and add a compatible Physlib environment. | The [release notes](docs/releases/v0.1.3.md) record scope and validation; the [GitHub release](https://github.com/MGYamada/Qleisli/releases/tag/v0.1.3) identifies the commit, CI and publication. Further symbolic-kernel implementation remains deferred. |
| Before v0.2.0 | First write ideal imaginary Qleisli 1.0 code for QPE, Grover, amplitude estimation, Shor, quantum walk, and QSVT; record contracts, capabilities, and open questions. Compilation is not required. | The [six drafts and index](docs/imaginary-v1/README.md), with their [review](docs/imaginary-v1/review.md), satisfy the initial-code and requirement-record prerequisite. The code remains uncompiled. |
| v1 | Express textbook Shor, QPE, and Grover in actual source with shared components, size/operation parameters, and checkable contracts. Shor reuses shared QPE and exposes classical period validation, factor extraction, failure, and retry. | Concrete acceptance target for the north star; not achieved. Fixed examples or pseudocode alone do not suffice. |

Detailed V01-C1–C6 and V1-C1–C5 criteria are in the [authoritative milestones](docs/release-milestones.md); this section summarizes them. They are distinct from development stages 0–5, finite-core specification v0, ledger format v1, and the current Cargo version `0.1.3`. Do not infer release milestones from unrelated prior test results.

| Stage | Status | Deliverables |
| --- | --- | --- |
| 0. Source and standard-library organization | Complete as documentation | `.qli`, modules, standard APIs, built-in boundary |
| 1. Language specification | **Current priority.** Normative rules specified; ideal soundness of the stated rules proved on paper; correspondence with all accepted implementation paths unproved | Syntax, type/effect/ownership rules, semantics, conformance record |
| 2. Typed IR | Partially implemented | Rust IR, verifier, evidence formats |
| 3. `.qli` frontend | Minimal path implemented | Name resolution, nonrecursive calls, type/effect/ownership checking, IR generation, diagnostics |
| 4. Reference execution | Tested on finite examples | Bell, phase-oracle, feedback, and structured algorithms executed from `.qli` |
| 5. External backends | Not started | Output systems that check target capabilities |

<a id="v013-release-roadmap"></a>

## v0.1.3 maintenance release

The [0.1.3 record](docs/releases/v0.1.3.md) collects the matrix-helper repair,
regressions, version synchronization and candidate checks. The
[v0.1.2 review verification](docs/reviews/v0.1.2.md) confirms the supplied
findings against the tagged source and CI. The declared finite profile and
public contracts remain unchanged. The [GitHub release record](https://github.com/MGYamada/Qleisli/releases/tag/v0.1.3)
identifies the verified commit, tag and publication separately from candidate
checks. The final contents include the subsequent checker fixes and compatible
Physlib dependency addition.

Generalization must replace mandatory dense logical-matrix construction at
composition boundaries with symbolic meanings and checked evidence, including
encodings and actual-IR binding. This is an architectural prerequisite, not a
performance optimization to defer until after adding sizes. The
[R14 constraint and QPE profile decisions](docs/imaginary-v1/requirements.md#scaling-prerequisite-for-r14)
record the work needed. The subsequent [system design](docs/symbolic-contract-architecture.md)
and [independent prototype](research/semantic-kernel/README.md) start this work
as the v0.1.3 research goal. The initial artifacts are retained; further
kernel development, full production source/IR integration and generalized
algorithms are deferred to the future work below.

## Future work: symbolic semantic kernel

**Deferred (2026-09-27):** retain the experimental design, prototype and
regressions as research evidence. Further development and production adoption
are future roadmap work, not additional completion conditions for the current
0.1.3 maintenance release. No target release is selected. The production
finite checker still computes dense matrices; the prototype does not remove
that limitation from compiled `.qli` programs.

| Step | Required result | Status |
| --- | --- | --- |
| Select the production contract profile | Specify symbolic meanings, encodings, proof rules, supported source operations, capacity and compatibility. Fix the first generalized QPE angle representation and exact/approximate checking policy. | Future specification; the experimental design is input, not an adopted production API. |
| Connect source contracts to final IR | Bind the caller's required meaning to actual implementations; establish encoded entry states and certified auxiliary release; preserve evidence through lowering and transformations. | Future implementation, extending beyond the current limited raw-IR adapter (G013-S3). |
| Validate scaling and implementation correspondence | Compose nontrivial operations at multiple sizes without whole-operator matrix expansion; test substitution, phase, axis order, reference systems and invalid proofs. State leaf bounds, cost and remaining trusted components, and prove the relevant implementation/rule correspondence. | Future validation and proof; current large-frame examples and local Lean lemmas do not complete this step. |

The [system design](docs/symbolic-contract-architecture.md) records the semantic
and trust boundaries. Resume this work through G020-1 specification selection
before production size generalization. Dense-free composition remains a
prerequisite for that generalization; deferral does not relax it or V1-C1–C5.

The [Lean quantum-library investigation](research/quantum-libraries/README.md)
compares pinned Physlib/QuantumInfo and lean-quantum sources with isolated
mathematical interface probes. That preliminary research did not adopt a library.
The subsequent [Physlib environment addition](docs/physlib-environment.md)
pins the compatible `v4.30.0` commit while retaining Lean/Mathlib 4.30.0.
Dependency availability does not resume kernel work or establish source/IR
semantic correspondence.

<a id="v012-release-roadmap"></a>

<a id="v012のリリースロードマップ"></a>

## v0.1.2 release roadmap

**0.1.2 is the design/documentation maintenance release dated 2026-09-27 (JST).** The [authoritative release record](docs/releases/v0.1.2.md) defines scope and artifact-level criteria. This release targets the six imaginary drafts and their requirements while preserving the current finite-core specification, public APIs, dependencies, capacities, and minimum toolchain. Implementing imaginary syntax/APIs belongs to a subsequent minor release. The [GitHub release record](https://github.com/MGYamada/Qleisli/releases/tag/v0.1.2) identifies the actual tagged commit, CI, and publication; the date alone is not evidence of completion.

| Step | Completion condition | Current state |
| --- | --- | --- |
| P012-0: English specification groundwork | First establish a framework separating current English norms from future design notation and recording types, ownership, effects, semantic contracts, and IR correspondence. | Complete: [English design framework](docs/language-evolution.md) and corrected stale status summaries. No new syntax is adopted or implemented. |
| P012-1: version and plan | Synchronize Rust/Lean at 0.1.2, changelog, current-version summaries, English release plan, and conformance record. Check metadata, documents, and candidate package listing. | Complete. Metadata, fmt, document checks, 14 checker tests, and package-list inspection are in the [conformance record](docs/specification-status.md). |
| P012-2: six ideal-code drafts | Show mathematical stages, parameters, and component composition in each of QPE, Grover, amplitude estimation, Shor, quantum walk, and QSVT. Label all code imaginary and uncompiled. | Complete: [six initial drafts](docs/imaginary-v1/README.md); Shor and amplitude estimation reuse shared QPE. |
| P012-3: contracts and requirements index | Record input/output, meaning, capabilities, ownership, effects, phase, exact cleanup, accuracy, success/failure, and classical processing; trace shared requirements to uses. | Complete: [R01–R14](docs/imaginary-v1/requirements.md) and per-draft contracts, classifications, IR plans, and open questions. |
| P012-4: semantic review | Cross-check contracts and composition, incorporate counterexamples and ambiguities, expose remaining questions, and record artifact links and prerequisite evidence. | Complete: [semantic review](docs/imaginary-v1/review.md) and 52 independent finite mathematical checks; these do not execute imaginary code. |
| P012-5: final candidate validation | Check Rust all-target tests/fmt/Clippy, documents/exact examples, Lean build/axiom audit, representative CLI/Shor examples, source package, and attribution. | Local pre-translation candidate passed: 258 tests and Clippy on each of Rust 1.98.1/1.85.0, Lean audit of 527 declarations, 14 document tests, 39 exact examples, 52 design-math checks, all ten CLI examples and Shor, and 155-file packaging/rebuild. Subsequent English consolidation passed independent review, document checks, the same mathematical fixtures, and updated 156-file packaging/rebuild; see the release record. Linux CI belongs to P012-6. |
| P012-6: commit and publication | Package/rebuild and pass required CI from a clean commit containing final artifacts; separately record annotated v0.1.2 tag, push, and GitHub source release. | Publication requires all listed gates. The actual commit, CI, source archives, annotated tag, and publication are recorded in the [GitHub release](https://github.com/MGYamada/Qleisli/releases/tag/v0.1.2). Registry distribution is separate. |

Initial drafts are design material separate from executable examples. See the [artifact index](docs/imaginary-v1/README.md) and release plan. Listing API names alone does not satisfy P012-2. Existing fixed-width examples or v0.1.1 checks do not substitute for draft creation or 0.1.2 candidate validation.

The English consolidation requested after the corpus translates current Japanese design foundations and planning documents, preserves the historical conformance ledger, and records authority in the [documentation map](docs/documentation-map.md). Its completed editorial review and checks are recorded separately from the earlier candidate execution checks.

<a id="v020からv1へ進む順序"></a>

### Order from v0.2.0 toward v1

| Step | Prerequisites and deliverables | Status |
| --- | --- | --- |
| G020-1: select the next specification scope | After P012-2–4, select the smallest scope from shared size/operation parameters and access capabilities. Specify types, ownership, effects, accepted/rejected cases, IR evidence, capacity, and compatibility in English. Require symbolic contract/encoding composition without whole dense matrices and select the first QPE angle and checking profile. | Draft, requirements, and review prerequisites complete; concrete syntax and standard APIs undecided. |
| G020-2: generalize while preserving contracts | Implement the selected specification from source to independently verified IR. Preserve implementation substitution, phase, and exact cleanup for all inputs and references. | Not started. |
| G020-3: reuse and release validation | Reuse the same definitions at multiple sizes, precisions, and operations/predicates within the selected scope. Check phase, references, failures, rejections, and existing regressions. Publish migration guidance, limits, and validation scope before 0.2.0 release checks. | Not started. Selecting and publishing version 0.2.0 are separate actions. |
| V1: three actual source programs | Satisfy V1-C1–C5 with QPE, Grover, and Shor using shared QPE; identify public contracts to stabilize. | Not achieved; completing 0.2.0 alone does not suffice. |

Algorithmic approximation error/success probability and exact auxiliary zero return are separate contracts. The amplitude-estimation, walk, and QSVT drafts evaluate abstractions without expanding the three executable v1 targets to six. Finite-core regressions and the open general proofs in SPEC-3/4 continue alongside design work.

<a id="v011-release-roadmap"></a>

<a id="v011のリリースロードマップ履歴"></a>

## v0.1.1 release roadmap (historical)

**0.1.1 was selected for compatible fixes.** Its [authoritative release notes](docs/releases/v0.1.1.md) define scope and gates. This table records local preparation and publication conditions; the GitHub release record identifies actual commits, CI, tags, and publication. Public syntax, APIs, IR, capacities, and minimum Rust were preserved; imaginary-v1 code was treated as a pre-v0.2.0 prerequisite.

| Step | Completion condition | Recorded state |
| --- | --- | --- |
| P011-1: compatible fixes | Fix contract reuse, source-location/exact-counterexample diagnostics, auxiliary leakage detection, and exact-arithmetic boundaries; add regressions. | Implemented and reviewed; see the [response record](docs/reviews/claude-v0.1.0.md). |
| P011-2: version and records | Align Rust/Lean versions, changelog, current summaries, and roadmap; check metadata and documents. | Complete at 0.1.1; metadata, package listing, fmt, document checks, and 14 checker tests recorded in the [ledger](docs/specification-status.md). |
| P011-3: final candidate checks | Check Rust all-target tests/fmt/Clippy, documents/exact examples, Lean build/audit, CLI/Shor examples, package, and attribution. | Locally complete: after leakage-warning underflow repair, 258 tests and Clippy on each of Rust 1.98.1/1.85.0, all ten examples and Shor, package generation/rebuild. Retained the preceding successful audit of 527 unchanged Lean declarations. Uncommitted candidate checks were distinct from the next step. |
| P011-4: commit, package, CI | Commit all changes including date/final notes; package/rebuild a clean candidate; record Linux Rust 1.98.1/1.85.0, document, and Lean CI success. | Required for publication; actual commit and CI belong in the GitHub release record. |
| P011-5: publication | Annotated v0.1.1 tag on the verified commit including final docs; separately record tag push and GitHub source release. | Publication is confirmed by the annotated tag and GitHub release record. Registry distribution is separate. |

Implementation and local candidate validation were completed. The [ledger](docs/specification-status.md) distinguishes version-selection, review, and candidate-check results. The recorded main ruleset requires a PR, four required checks, resolved conversations, and an up-to-date base. Updates/deletions of v* tags are prohibited, so the merged main commit's CI must be checked before tagging. These are separate from general implementation-correspondence and soundness proofs.

<a id="現在の優先工程-段階1へ戻る"></a>
<a id="現在の優先工程-v01の有限契約基盤"></a>
<a id="現在の優先工程-仮想qleisli-10コードの先行作成"></a>

<a id="v020以前の前提工程-仮想qleisli-10コードの先行作成"></a>

## Pre-v0.2.0 prerequisite: imaginary Qleisli 1.0 code first

**Write ideal imaginary Qleisli 1.0 code before v0.2.0 generalization, feature implementation, or release.** Following the [authoritative prerequisite](docs/release-milestones.md#pre-v020-imaginary-v1-code), show the six algorithm bodies and their composition, with a draft/requirements index. Compilation is not required; revise drafts in response to semantics and counterexamples. Distinguish initial drafting, specification adoption, implementation, validation, and proof, while preserving executable v1 acceptance. Finite-core maintenance and unfinished implementation-correspondence/soundness proofs continue in parallel.

<a id="v01の有限契約基盤と継続課題"></a>

### The finite v0.1 contract foundation and continuing work

Retaining the finite-core priority of 2026-09-26, the 2026-09-27 goal connects **finite v0.1 semantic contracts and independent evidence checking to Stage 1 source-to-IR correspondence before size generalization**. Preserve existing algorithms and library code as regressions. Broader layer-2/3 extensions follow the completion of one path for semantic contracts and implementation substitution.

| Step | Status | Criteria and artifacts |
| --- | --- | --- |
| SPEC-0: fix scope | Complete | Include finite basis types, static operations, and restricted auxiliary evidence in v0; defer generalization. |
| SPEC-1: normative documents | Complete | Align types, effects, ownership, accepted/rejected cases, and IR correspondence in [v0](docs/language-spec.md), [grammar](docs/syntax-v0.md), and [sealed APIs](docs/standard-library.md). |
| SPEC-2: implementation comparison | Complete for finite conformance cases | Record capacities, evidence restrictions, and checks in the [ledger](docs/specification-status.md); add specification-boundary regressions. |
| SPEC-3: formal system and proofs | **Ideal soundness Q1–Q3 proved on paper for the stated rules** | Connect [pure operations and instruments](docs/source-soundness.md) by induction over all syntax. [Lean](docs/lean-resource-proof.md) covers local ownership/Kraus-composition lemmas. Correspondence to every accepted Rust path remains open. |
| SPEC-4: translation/verifier correspondence | Conditional preservation C1–C5; scope projection extracted and locally modeled in Lean | [Translation contracts](docs/source-ir-correspondence.md) and [state refinement](docs/lowering-state-refinement.md) documented. Adequacy for all successful Rust paths and formal verification of the implemented verifier remain open. |

SPEC-1 specification adoption and SPEC-2 finite tests do not complete Stage 1. Its proof-bearing completion conditions below remain in force. The order is source-to-IR contract boundaries → finite v0.1 evidence/independent checking/substitution → **imaginary-v1 code and requirements before v0.2.0** → sized types and operation parameters → the three v1 algorithm structures and required standard APIs. Consider effects on norms, conformance examples, and proofs before each step.

<a id="v01の有限契約の成果物"></a>

### Finite v0.1 contract artifacts

| Minimum condition | Artifact | Status |
| --- | --- | --- |
| V01-C1 | Finite contract/evidence specification connected to BC/C1–C5, fixing logical action, encodings, entry evidence, ownership, phase, and axis order. | [SC rules](docs/semantic-contracts-v0.1.md), [FC rules](docs/function-contracts-v0.1.md), and finite APIs implemented. Entry assertions remain distinct from proofs about runtime states. |
| V01-C2 | Independent checks for primitive equality, composition, tensor, conditional adjoints/control, and small exact comparisons; explanations of rule soundness. | Exact checker and immutable evidence-composition APIs implemented, with local paper derivations. General Rust formal verification unfinished. |
| V01-C3–C4 | Connect actual source function contracts and final-IR evidence; accept phase oracle, auxiliary H;H, and simultaneous data/auxiliary X using the same rule. | Three examples, CertifiedCompute retaining actual W, and FunctionEvidence retaining raw function IR/source dependencies implemented. Contract actions preserve evidence after adjoints/control/repetition. |
| V01-C5–C6 | Substitute phase-oracle implementations without changing clients, including control/references; reject wrong phase, auxiliary-only X, missing entry evidence, mismatched evidence, etc. | apply_contract fixes client requirements and reuses checked evidence; direct and two private-auxiliary implementations are compared. Dependency tampering and phase/axis/type/ownership/capacity rejection are tracked. |

Follow the [authoritative conditions](docs/release-milestones.md#v01-minimum-semantic-contracts). Complete this finite path with explicit correspondence evidence and trust boundaries, without claiming machine verification of the whole Rust implementation.

**v0.1 result:** the finite path connects public function requirements, implementations, and dependencies, retaining immutable evidence through final IR. The [ledger](docs/specification-status.md) records V01-C1–C6 and checks. **Next design target:** with the [six imaginary drafts and requirements](docs/imaginary-v1/README.md) in place, select a minimal specification for sizes, operation parameters, access capabilities, and semantic contracts that preserves this boundary. Specify English rules and IR evidence before implementing generalization and connecting shared Grover/QPE/Shor structure. General SPEC-4 implementation correspondence remains open, separately from the history below.

The [QPE → amplitude amplification → Shor proposal](docs/quantum-bookkeeping.md) suggests an evaluation order for deepening implementation and contracts after initial drafting. It is a supporting design note testing the quantum-bookkeeping principle through algorithm descriptions; formal release criteria remain in the release milestones.

<a id="spec-3の最初の到達点2026-09-26"></a>

### First SPEC-3 result (2026-09-26)

The [source resource rules](docs/source-resource-rules.md) separate name bindings, pending results, and current register mappings, defining a unique location for every owner including `Q<Unit>`. Callee-external resources and pending arguments form frames; branch result positions and surviving frames produce complete φ mappings. Paper results include R1 resource preservation for the rule system, resource closure at a closed entry, and a φ axis-renaming lemma with references. The [formal-core overview](docs/formal-core.md) was also translated into English, separating proved local results from unfinished theorems.

The implementation audit added seven regressions for mixed arguments and partially evaluated tuples, nested branches, zero-width φ, reset with references, classical φ, and ownership rejection. These do not complete general source soundness or Rust formal verification.

<a id="資源モデルの検証基盤2026-09-26"></a>

### Resource-model verification foundation (2026-09-26)

Lean 4/Mathlib 4.30.0 checked ownership counts for mixed values and `Q<Unit>`, local resource transitions, frames, complete ownership-covering φ, and composition. Thirteen boundary lemmas, axiom auditing, and Lean/Rust/document CI definitions were added. [Coverage and omissions](docs/lean-resource-proof.md) are recorded separately. This does not machine-check all of paper R1, the Rust implementation, or quantum semantics.

<a id="ソース意味論と構造的なir対応2026-09-26"></a>

### Source semantics and structural IR correspondence (2026-09-26)

The [source semantics](docs/source-semantics.md) defines classical results and ordered quantum interfaces of mixed values, lexical environments, and unnormalized states retaining probabilities. Conditional local paper theorems cover evaluated-value function substitution S1, correlated-frame extension S2, classical branching with simultaneous φ S3, and structural IR correspondence S4. Normative v0 was translated into English without changing accepted/rejected cases or existing section links.

Four regressions were added after auditing Rust: single evaluation of measured arguments with sharing of classical arguments, name shadowing, phase/Bell correlations across calls, and φ order with zero-width results. These are distinct from complete source soundness, preservation of every translation, or Rust formal verification.

All 119 Rust tests, fmt, Clippy, and document links passed. Translation did not change rules; local paper proofs S1–S4 were not claimed as machine checked.

<a id="有限静的変換の位相軸順の対応2026-09-26"></a>

### Phase and axis order in finite static transformations (2026-09-26)

The [static semantics](docs/static-semantics.md) gives paper results F1–F5 for token-to-ordered-axis mapping, return-order permutations, inverse-phase reindexing, finite repetition, nested quantum control, and restricted auxiliary phase cancellation. Premises include one quantum input/output, no classical ports, and verified supported constructors. Operators are compared exactly including phase, scalar phase on `Q<Unit>`, and arbitrary reference systems.

The [static-operation contracts](docs/static-operations.md) were translated into English, clarifying name resolution after input evaluation, declared effects, full checking even for zero repetitions, and pending control ownership in `qif`. Acceptance rules and section links were preserved; no language forms or standard APIs were added.

[Five exact-arithmetic tests](tests/static_semantics.rs) compared 38 input columns and 186 matrix entries of twelve compiled circuits against independent analytic formulas. All 124 Rust tests, fmt, Clippy, and document checks passed. The audit found no implementation bug requiring repair; Lean was unchanged. Paper proofs, finite exact checks, and general Rust correctness remain distinct.

<a id="全構文の型効果名前スコープ規則2026-09-26"></a>

### Type/effect/name/scope rules for all syntax (2026-09-26)

The [inference-rule supplement](docs/source-typing-rules.md) connects type formation, every basis/ordinary expression, argument lists, patterns, statements, blocks, declarations, and name resolution to the existing resource rules. It maps all AST constructors, including static forms and auxiliary evidence. Paper results T1–T3 establish typed totality of basis computation; uniqueness of result type, syntactic effect, and residual bindings; non-resurrection of consumed bindings; conservativity of declared effects; and a conditional IR effect bound. They do not claim unique generated IR or Rust correctness.

[Six regressions](tests/source_judgments.rs) cover declared effects stronger than expanded IR, branch-local names and consumed outer names, exact product types, basis-context separation, auxiliary-evidence effects, and resolution in the defining module. All 130 Rust tests, fmt, Clippy, and document checks passed. No implementation bug requiring repair was found; acceptance rules, public APIs, and Lean were unchanged.

<a id="数学的ソース規則の理想健全性2026-09-26"></a>

### Ideal soundness of the mathematical source rules (2026-09-26)

[Paper theorems Q1–Q3](docs/source-soundness.md) establish deterministic outputs for fixed classical inputs, pure isometry/unitarity, and complete positivity with summed trace preservation for finite observation/adaptive composition. Induction uses all-owner interfaces including remaining environments, pending values, and frames; it handles history-dependent intermediate dimensions, zero-probability branches, hidden classical histories, and arbitrary references. The target is the stated mathematical derivations, not a proved correspondence to all Rust-accepted source.

As a needed Lean extension, [Kraus.lean](lean/Qleisli/Kraus.lean) checked five exact-complex-matrix lemmas for singleton isometric operators, isometry composition, outcome-dependent output correspondence, and adaptive Kraus-completeness composition. Positivity, trace, and full source induction were not ported to Lean. Build and the audit of 456 declarations passed.

[Four additional tests](tests/source_soundness.rs) use seven compiled examples to check probabilistic addition of opposite-phase hidden histories, adaptive observation/marginalization of nonuniform correlations, coherence under injective lifting versus loss under reset, and zero-probability branches. All 134 Rust tests, fmt, Clippy, and document checks passed. No language forms or standard APIs were added.

**Next priority at that historical point (finite contracts are now complete as above):** define the BC/C1–C5 semantic-contract boundary, then V01-C1 and its finite checker. Build on local scope-projection theorems to compose state refinement for input generation, moves, binding, and pending values, checking snapshots/rebinding and all-owner coverage. Track implicit frames/issued-ID history in calls and branch snapshot/merge, C1–C5 table/axis implementation adequacy, and independent-verifier correctness as separate obligations. Restrict Lean work to useful local lemmas. Finite-contract implementation, complete Stage 1 proof, algorithm correctness, and hardware assurance remain distinct.

<a id="ソースirの具体的変換契約と意味保存2026-09-27"></a>

### Concrete source-to-IR contracts and semantic preservation (2026-09-27)

[Translation contracts C1–C5](docs/source-ir-correspondence.md) specify type-tree encoding/decoding, left-associated multiargument Pack, all-input table generation, primitive/observation Kraus actions, auxiliary Z/T token chains, and complete φ using result positions and surviving slots. Intermediate boundaries retain every classical record readable by the continuation; histories move into common coordinates before CP maps are summed. Induction on dependency rank and syntax composes S1–S4 and F1–F5 to show conditional preservation of pure operators including phase and observation instruments for this mathematical translation.

[Six regressions](tests/source_ir_correspondence.rs) check 401 accepted cases, two rejected cases, and one case of valid IR with meaning different from the source. Independent sparse-state formulas and the Born rule supply expectations for type trees containing Unit, width extension/references, observation weights, auxiliary phase, and complete φ. Results are in the [ledger](docs/specification-status.md). Proofs that all Rust executions implement this translation, that the verifier implementation is correct, and that floating-point execution has an error guarantee remain open. SPEC-4 is not complete.

<a id="スコープ射影の実装対応と局所証明2026-09-27"></a>

### Scope-projection refinement and local proof (2026-09-27)

[State refinement](docs/lowering-state-refinement.md) organizes relations between values, environments, registers, and pending owners, with proof premises for inputs, moves, binding, functions, branches, and auxiliary regions. Rust block closure was extracted into [`close_scope`](src/frontend/compile/lower/scope.rs), preserving rejections, diagnostics, and work accounting. Equal slots and values do not make rebinding the same binding; `rebound` records are required.

The [Lean Scope model](lean/Qleisli/Scope.lean) distinguishes absent, consumed, and live names. It proves restoration of classical bindings and the entry name set, non-resurrection of consumed bindings, rejection of escaping local quantum ownership, and preservation of quantum-owner lists on success. Correct snapshots/rebinding on every Rust path and full frame coverage remain premises; SPEC-4 is not complete.

A comparison with an independent binding-ID model covers 7,225 cases, alongside [three source regressions](tests/source_scope.rs). All 169 Rust tests, 14 document-checker tests, fmt, Clippy, reference checks, Lean build, and the audit of 527 declarations passed. Scope and results are in the [ledger](docs/specification-status.md).

<a id="実装の保守基盤2026-09-26"></a>

## Implementation maintenance foundation (2026-09-26)

The [architecture document](docs/implementation-architecture.md) records dependency directions and trust boundaries for IR, the independent verifier, frontend, and reference execution. Lowering was split into private modules for expression evaluation, values/ownership, branches/complete φ, and sealed operations. Invariants include pending arguments, caller frames, consumed names, zero-width ownership, and fresh IDs across branches.

Six Rust test suites share temporary source-project setup/cleanup. Analytic expected distributions and exact-matrix checks remain in individual tests. Resource/type-rule correspondence tables link implementation items and test names; document checks verify those references exist. Existence is not a general correspondence or preservation proof.

This supports Stage 1 maintenance without extending language forms, standard APIs, acceptance rules, or Lean scope. All 134 Rust tests, fmt, Clippy, nine document-checker tests, reference checks, and `git diff --check` passed. Reference checks covered 490 local links, 50 anchors, 58 implementation references, 17 test references, and reachability of six Lean modules. Lean build/audit were not rerun in that step.

<a id="レビューに基づく表現力と規範の整合2026-09-2627"></a>

## Review-driven expressiveness and normative alignment (2026-09-26–27)

To resolve A1/A4, product patterns in `do` and ordinary `CBit` constants/Boolean operations were implemented as a specification revision. `true` and `false` became reserved words, requiring older same-named identifiers to be renamed. Whole-input injectivity, `Q<Unit>` linearity, and full left-to-right classical-operand evaluation were preserved. Static adjoints/control/repetition resolve closed classical branches while preserving all φ ownership, phase, and output-axis order.

The [normative specification](docs/language-spec.md), [grammar](docs/syntax-v0.md), inference rules, semantics, and IR correspondence were updated together. Basis-context/private-auxiliary-binding shadowing, nested classical products in `main`, Unicode lexing, and diagnostics were clarified. The twelve-public-definition ledger, examples matching actual files, and the relationship between English authority and Japanese supporting material were aligned; the [review-item record](docs/specification-status.md) collects traceability links.

All 153 Rust tests, fmt, Clippy, nine document-checker tests, and reference checks passed. Seven exact-matrix static-semantics tests cover classical branches and product patterns under adjoints/control. Relevant paper-proof cases were updated; Lean scope was unchanged. Correspondence to all accepted Rust paths and general semantic preservation remain SPEC-4 work.

<a id="コードレビューの境界不具合を修正2026-09-27"></a>

## Code-review boundary fixes (2026-09-27)

Import-cycle detection moved to an explicit DFS stack to avoid stack overflow on long dependency chains. Lean-audit reachability ignores imports inside comments/strings. CLI handling of non-UTF-8 OS arguments no longer panics. Reproducers, regressions, and platform-specific coverage are in the [ledger](docs/specification-status.md). Language rules and Lean proof scope were unchanged.

<a id="第2目標の進め方"></a>

## Advancing goal 2

Connect the [structure-extraction criteria](docs/algorithm-structure-goal.md#実装順と到達基準) to the north star and concrete v1 acceptance. A0–A4 identify work areas and existing results, not release numbers. After finite v0.1 contracts and the imaginary-v1 drafting prerequisite, generalize actual Shor/QPE/Grover source. Existing results and remaining work are:

- **A0, initial survey complete:** extracted eight common structures, input models, and additional evidence needs from twenty entries with primary sources.
- **A1, implemented/tested on finite cases:** five ordinary `std::routines` components reused by Grover, BV, and three-bit-code examples. Checks cover all targets, iteration counts, reference correlations, and counterexamples outside premises.
- **A2, finite subset achieved:** static `adjoint`, `qif`, `repeat_static`, and independent finite-unitary IR verification. QPE2/3 uses ordinary QFT2/3; checks cover phase distributions, references, reflection signs under control, and rejection. See [contracts/results](docs/static-operations.md). General sizes, angles, and operation arguments remain open.
- **A3, first finite-arithmetic result:** ordinary two-bit addition and multiplication modulo 15, N=15 order finding, and Rust-host continued fractions, period-candidate checks, and factor extraction. [Full-space/reference/retry checks](docs/arithmetic-order-finding.md) were performed. General arithmetic/Shor and VQE/QAOA with observables and host iteration remain open.
- **A4, finite part implemented/tested:** exact semantic contracts, evidence checking, and implementation substitution are connected as required v0.1 work. General preservation effects, code spaces, projected blocks, approximation evidence, and recomposition for different problems remain future work.

Reproducing existing examples and discovering new algorithms are separate achievements. Goal 2 as a whole is not complete.

<a id="第3層の将来計画-標準ライブラリ"></a>

## Future layer 3: standard library

Following the [standard-vocabulary plan](docs/stdlib-roadmap.md), develop layer-2 components into standard APIs with contracts, verification status, and compatibility. L0's document ledger, L1's finite operation transformations, and L3's finite arithmetic/classical processing are implemented. Existing fixed examples did not require general L2 support. Build on the v0.1 path connecting finite L0/L1/L4 contracts; use imaginary-v1 drafts to identify missing vocabulary before implementing generalizations required by the three v1 algorithms. Completing all L0–L5 is not a v0.1/v1 requirement.

| Stage | Layer-2 dependency | Result |
| --- | --- | --- |
| L0: contract ledger | A0/A1 | [Ledger format v1](docs/stdlib-contracts.md) records twelve bundled public definitions. Finite contracts/function evidence have Rust representations and source application. Machine-readable coverage of the whole ledger is future work. |
| L1: structure and data | A2 | Finite adjoints/control/repetition of same-type functions implemented/tested. Sized types and general operation parameters remain open. |
| L2: first skeletons | A2/L1 | Fixed-width QPE usage examples implemented. Standard amplify/QPE APIs and reuse evaluation for amplitude estimation/counting not started. |
| L3: arithmetic and hybrid plans | A3 | Fixed-width arithmetic, N=15 order finding, and classical reconstruction implemented/tested. General arithmetic, retry control, estimate, and VQE/QAOA remain open. |
| L4: evidence-bearing skeletons | A4 | Finite exact semantic contracts/auxiliary evidence precede other work in v0.1; their checking path is implemented. Method-specific contracts for walk, LCU, QSVT, simulate, and general syndrome extraction are future candidates, not implemented. |
| L5: adoption and maintenance | Validation in multiple uses | Per-component standard adoption, version/conformance checks, and feedback from AI proposals; not started. |

Completion requires traceable input/output, resources, effects, success conditions, errors, and generated IR, not only API names. Standard adoption primarily uses ordinary definitions; adding sealed operations requires separate semantics and checking rules.

<a id="0-ソースと標準ライブラリの構成"></a>

## 0. Source and standard-library organization

First prepare [README.md](README.md), [AGENTS.md](AGENTS.md), and [quantum-language requirements](docs/quantum-language-requirements.md). The [Stage 0 design](docs/standard-library.md) selects:

- The role/encoding of `.qli`, one-file/one-module correspondence, top-level declarations, visibility, imports, and entry functions.
- Minimal standard-library modules and automatically available names; boundaries between ordinary `.qli`, sealed operations, and language forms.
- Local module resolution, cycles, and initial treatment of external dependencies and host I/O.
- Multifile Bell preparation/measurement and phase-oracle design examples, identifying operations with quantum premises.

**Completion:** consistent documented choices, with examples readable under the same module rules. Grammar/type-checker implementation is not a Stage 0 condition.

Stage 0 organization is selected in the [standard-library specification](docs/standard-library.md). Multifile Bell/phase-oracle examples follow its public declarations and root-relative `use` rules. Final grammar and execution validation belong to later stages.

<a id="1-言語仕様"></a>

## 1. Language specification

The [finite-core v0 specification](docs/language-spec.md) and [normative grammar](docs/syntax-v0.md) align with Stage 0 modules/sealed APIs. Finite-core acceptance/rejection rules are specified. [Conformance](docs/specification-status.md) and [formalization](docs/formal-core.md) distinguish specified contracts, implementation, and proof targets. [Inference rules](docs/source-typing-rules.md) and resource rules cover all syntax, but correspondence to all accepted paths and general proofs remain open.

- Formalize effectful transformations of classical values and quantum resources from the [design philosophy](docs/design-philosophy.md) using input/output contexts and composition. Investigate the precise structure of Kleisli-inspired composition and its relationship/limits with free-vector-space `bind`.
- Specify grammar and name resolution for all examples.
- Give inferable type/effect rules for `basis`, `iso`, `unitary`, and `observe`, and ownership rules for classical branches and `qif`.
- Specify `split/join`, restricted `with_computed` protection, measurement's termination of logical ownership, and auxiliary evidence. General borrowing syntax/signatures belong to a later specification.
- Address the [central open problem](docs/design-philosophy.md): separate ownership contexts from global-state correlations and specify function-boundary checks for local operations, partial measurement, discard, and pure release. Initial support does not require general entanglement inference.
- Specify pure isometries, measurement-bearing instruments, and translation to typed IR.
- State finite-core [soundness targets](docs/ai-era-goal.md) as theorems. Prove resource preservation, complete positivity for each classical outcome, and summed trace preservation under sealed-primitive and certified-release premises.
- Check accepted/rejected examples and finite Bell/phase-oracle/feedback distributions, including one-sided measurement/discard and unsupported pure release after splitting a Bell pair.

**Completion:** Stage 0 examples can be typed or rejected with unambiguous effects and IR translation. Finite-core resource safety and instrument soundness have theorem statements and proofs. Ownership separation must not imply state separation; partial Bell measurement/discard is interpreted globally, and pure release without evidence is rejected. Arbitrary free-vector-space `bind` is not an execution API.

<a id="2-型付き-ir"></a>

## 2. Typed IR

Represent ownership tokens, logical wire IDs, effects, phases, and checkable constructors in Rust. The verifier rechecks injectivity, gate types, protected-region/target conflicts, nonuse of measurement-consumed handles, and structured `ComputeUseUncompute` zero-return conditions. This does not implement general source borrowing. Do not expose a standalone `Release0`. Document each constructor's ideal semantics and the trusted primitive boundary. The [prototype](docs/ir-prototype.md) records implemented checks and unachieved guarantees; the [finite-IR paper proof](docs/finite-core-proof.md) records constructor semantics and implementation obligations.

**Completion:** accept valid small IR and reject intentionally constructed duplication, implicit discard, invalid release, and effect violations. Apply the same verifier to handwritten/external IR regardless of origin, and show that accepted IR meaning satisfies Stage 1 theorem premises.

<a id="3-qli-フロントエンド"></a>

## 3. `.qli` frontend

Implement parsing, module resolution, and type/effect/ownership checking under Stage 0 file rules, producing verified IR.

Within the finite-core v0 profile, all-declaration name resolution, call-cycle rejection, type/effect/linear-ownership checking, and IR generation are implemented. Ordinary calls are expanded. The original two-argument `with_computed` path restricts/rechecks expanded bodies to identity and Z/T sequences; the later explicit logical-contract path is specified in [SC](docs/semantic-contracts-v0.1.md). Classical branches merge results and surrounding live resources through φ. Public entry points are `check_project`, `compile_project`, and `qleisli check/run`; all generated IR passes independent `verify`. Static adjoints/control/repetition lower to ApplyUnitary in the finite implementation. The [frontend reference](docs/frontend-v0.md) records rules, diagnostic codes, limits, and unsupported features.

Review work limited internal values/types to 4,096 nodes and depth 64, charging copied trees to the work budget. Ordinary-call argument errors point to caller actual arguments or the call expression. Regressions include reproducers and accepted in-limit cases.

**Completion:** automatically classify Stage 1 accepted/rejected examples, with file locations and machine-readable results. Pass frontend output through Stage 2 IR verification without varying checks by code origin.

<a id="4-参照実行系"></a>

## 4. Reference execution

Execute instruments including measurement/reset/discard using finite-dimensional vectors and density operators or an equivalent mixed-state representation. The Rust prototype runs verified closed IR as ensembles of unnormalized pure states. Bell, phase-oracle, and feedback projects compile from `.qli` and match expected distributions; finite IR tests for partial discard/reset are retained. Values are approximate `f64`; exact zero probabilities and an independent literal execution check of auxiliary wires remain open.

The [finite algorithm examples](docs/algorithm-routines.md) check all two-bit Grover targets/iteration counts, all BV hidden strings, reference correlations in bit-flip correction, and parity-measurement coherence. Their success conditions are separate from type/resource safety.

**Completion:** execute compiled closed `.qli` programs and match analytically known distributions, distinguishing finite checks from general soundness proofs.

<a id="5-外部バックエンド"></a>

## 5. External backends

Explicitly check target-format/device capabilities. Emit output only when fresh logical-wire allocation on measured physical elements and dynamic feedback can be implemented correctly.

**Completion:** reject unsupported features clearly and compare supported program meaning with reference execution.

<a id="その先の個別仕様"></a>

## Further individual specifications

Protocol properties such as state preservation in teleportation, algorithmic correctness/success probability, and noisy hardware/calibration are separate specification and proof tasks. They are not consequences of the basic resource-safety and quantum-soundness theorem.
