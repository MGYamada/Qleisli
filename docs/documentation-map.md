# Documentation authority and English consolidation

Status: **English documentation policy and translation inventory** (2026-09-27).
This map identifies the status of the current documents; it does not extend the
language, adopt imaginary syntax, or prove implementation correctness.

## How to read the documents

English is the authoritative language for production language specifications
and public standard-library names, contracts, references, source comments,
and example explanations. Authority is tied to a document's subject and status:

| Document class | Authority and limits |
| --- | --- |
| Current language and API specifications | [Language v0](language-spec.md), [grammar](syntax-v0.md), [modules/sealed APIs](standard-library.md), [static operations](static-operations.md), [SC](semantic-contracts-v0.1.md), [FC](function-contracts-v0.1.md), and the [ordinary-library ledger](stdlib-contracts.md) govern current specified acceptance and public contracts within their declared scope. |
| Formal rules and proof accounts | [Formal core](formal-core.md), [resource rules](source-resource-rules.md), [typing rules](source-typing-rules.md), [source semantics](source-semantics.md), [static semantics](static-semantics.md), [source soundness](source-soundness.md), [IR correspondence](source-ir-correspondence.md), and [state refinement](lowering-state-refinement.md) state their models, assumptions, and proved/open obligations. A paper proof is not a claim that Rust implements every derivation correctly. |
| Implementation and evidence records | [Frontend profile](frontend-v0.md), [IR prototype](ir-prototype.md), [architecture](implementation-architecture.md), [Lean ledger](lean-resource-proof.md), [Physlib environment](physlib-environment.md), and [conformance history](specification-status.md) describe implementation/dependency coverage and dated evidence. Finite tests and local Lean lemmas do not establish general compiler soundness. |
| Adopted design direction and development plans | The translated documents below are the English editions for their own principles, requirements, plans, and arguments. An accepted design principle may constrain future work without being implemented. Proposed facilities remain proposed. These documents do not override current language/API rules. |
| Release criteria and compatibility | [Release milestones](release-milestones.md), [versioning](versioning.md), the [v0.x plan and v0.1.9 boundary](v0x-roadmap.md), and version-specific [release records](releases/v0.1.6.md) determine acceptance, compatibility, and preparation/publication status. Roadmap themes do not adopt syntax or establish implementation. Product versions, development stages, specification v0, and ledger format v1 are distinct. |
| Future design material | The [language-evolution framework](language-evolution.md) and [imaginary-v1 corpus](imaginary-v1/README.md) organize future requirements. All six algorithm drafts remain imaginary and uncompiled; their existence does not adopt their notation or APIs. |
| Selected future specifications | [M1 language extension](next-minor-spec.md), [machine interfaces](machine-interface-spec.md), and [bounded M2 IR/checker profile](hierarchical-ir-spec.md) specify future contracts and acceptance matrices. They govern their selected future slices, not current v0 acceptance. Their examples and acceptance tests are not implemented/executed. |
| Independent semantic research | The [system design](symbolic-contract-architecture.md) specifies the intended meaning/implementation boundary; the [prototype record](../research/semantic-kernel/README.md) records the separately implemented and tested subset. The [quantum-library investigation](../research/quantum-libraries/README.md) records isolated mathematical interface experiments that did not adopt a dependency at that investigation step; the later [Physlib record](physlib-environment.md) preserves the compatible addition and its subsequent deferral to a future concrete bridge. None changes production source acceptance or proves Rust/source correspondence. |

Use the [terminology conventions](terminology.md) across these classes. If a
proposed design conflicts with a current contract, record the conflict and a
future specification decision explicitly; do not silently reinterpret accepted
programs. Selecting a feature, specifying it, implementing it, testing it, and
proving it are separate events.

## Current state and historical records

[project-status.json](project-status.json) is the single editable record for
active milestone states and the initial rule/implementation/test/proof
inventory. [current-status.md](current-status.md) is generated from it and the
Rust/Lean manifests; the document checker rejects version/view drift and
missing source/test links. It is not an automatic proof or exhaustive audit.
Detailed norms remain in their existing specifications; historical validation
entries remain dated. [M0–M5 and the legacy-ID map](v0x-roadmap.md#legacy-id-mapping)
replace version-assigned scheduling without renumbering theorem statements.
AGENTS.md links durable rules to [the decision dossier](decisions/2026-09-27-v1-path.md)
instead of repeating changing adoption paragraphs.

## Translation inventory

The following current Japanese documents were translated in place for the
English consolidation requested after the initial v0.1.2 corpus review. Their
paths remain stable. Old heading targets are retained as explicit anchors so
existing links, including links in historical records, continue to resolve.

| English edition | Scope retained | Status of its content |
| --- | --- | --- |
| [Project overview](../README.md) | North star, current implementation/proof limits, development goals, references, development commands, and licensing | Project summary; linked specifications and release records govern details. |
| [Interoperability direction](interoperability-roadmap.md) | Python, OpenQASM 3 and QIR entry points, compiler layers, translation obligations, IR emitter/debt inventory and reduction gates | Selected external direction with implementations pending; initial internal qif execution consolidation implemented. No current foreign-format/API guarantee or trusted-core removal claim. |
| [Terminology](terminology.md#desugaring-layer) | Shared definition of desugaring, its producer/checker boundary and distinction from parsing, source checking, runtime adaptation and approximation | Authoritative terminology; no new language/API acceptance rules. Relevant documents restate the definition locally. |
| [Coefficient domains](coefficient-domains.md) | Future gate-architecture risk, coefficient-domain type parameterization and distinct exact/approximate/device contracts | Recorded architectural recommendation with primary sources and mathematical rationale; generic scalar APIs, arbitrary-angle checking and STAR support remain unimplemented. Existing M1/M2 formats/profiles are unchanged. |
| [Source documentation](documentation-comments.md) | Rust-style ordinary/doc comments, attachment, sidecar APIs, Markdown command, trust boundary and source migration | Implemented bounded extension, retained in 0.1.6 by explicit user exception; doc text is not checked semantic evidence or full rustdoc support. |
| [Development roadmap](../ROADMAP.md) | P012/G020, SPEC, A/L work areas, stages 0–5, historical milestones and check counts | Accepted ordering and stated completion criteria; pending work remains pending. |
| [Design philosophy](design-philosophy.md) | Effectful composition, linear ownership, global-state reasoning, phase, cleanup, and implementation boundaries | Fixed design principles; future syntax and open semantic/composition work remain explicit. |
| [AI-era goal](ai-era-goal.md) | Assurance levels, resource/ideal-semantic proof targets, AI verification boundary, and exclusions | Adopted development goal, with bounded achieved results and open general proofs distinguished. |
| [Algorithm-structure goal](algorithm-structure-goal.md) | Common structures S1–S8, design contracts, A0–A4, corpus and future composition | Adopted goal and plan; higher-order/generalized facilities are not current APIs. |
| [Algorithm corpus](algorithm-corpus.md) | Twenty entries C01–C20, primary-source links, input models, promises, evidence needs, and unsupported parts | Research/design inventory, not twenty implemented algorithms. |
| [Quantum-language requirements](quantum-language-requirements.md) | Resource/effect/phase/reference conditions and specification obligations | Adopted requirements with implementation/proof scope stated separately. |
| [Standard-library roadmap](stdlib-roadmap.md) | Seven areas, contract fields, four proposed skeletons, adoption criteria, AI feedback, L0–L5 | Authoritative library design plan; proposed generalized APIs remain unimplemented. |
| [Quantum bookkeeping](quantum-bookkeeping.md) | Language responsibility, semantic composition, phase-sensitive QPE, and proposed evaluation order | Supporting design argument and proposal, subordinate to release acceptance criteria. |
| [Finite-IR paper proof](finite-core-proof.md) | Constructor equations, theorem premises, reference extension, resource invariants, and implementation obligations | English edition of a conditional mathematical argument for the stated finite IR; neither whole-compiler verification nor a new Lean result. |

The existing English current specifications, finite routine/static/arithmetic
contracts, language framework, and six imaginary algorithm drafts were used
as cross-references. Translation preserves mathematical premises and the
distinctions between proposal, adoption, implementation, finite testing, paper
proof, and machine checking. Stale summary wording is clarified against those
records without changing source acceptance or claiming new proof coverage.

## What remains in Japanese

- [AGENTS.md](../AGENTS.md) remains the repository's operational guidance in the
  maintainer's working language. It points to English production specifications;
  it is not an alternative grammar or standard-library reference.
- Dated Japanese entries in the [conformance ledger](specification-status.md)
  are retained as historical evidence in their original language. The English
  introduction and new entries identify current state and superseded status
  claims. A historical “not implemented” or “not rerun” describes that step,
  not necessarily the current tree. Historical test totals and publication
  actions are not rewritten as new results.
- Japanese legacy anchors and the bilingual glossary remain intentionally.
  They preserve references and terminology; they are not untranslated current
  specification prose.

Current design/planning prose in the ten inventory documents is English.
Historical records may later receive labeled English translations, with the
original date, scope, and evidence preserved. No duplicate Japanese normative
edition is maintained by this consolidation.

## Decisions this consolidation does and does not settle

The fixed foundation is linear quantum ownership, explicit effects, global
reasoning with arbitrary references, phase-sensitive composition/control,
exact evidence for pure auxiliary cleanup, and independent checking of finite
semantic contracts through final IR. The north star and executable V1-C1–C5
criteria remain in force.

The initial six-code prerequisite before v0.2.0 is complete as design material.
Sized source syntax, general instrument/accuracy evidence, and full arithmetic
APIs still require extension decisions. The subsequent
[0.1.5 dossier](decisions/2026-09-27-v1-path.md) and its linked specifications
settle fixed-width operation/access/meaning rules, machine interfaces and the
bounded M2 checker/QPE profile, without implementing them. The
[requirements index](imaginary-v1/requirements.md) records candidate facilities
and open questions; translation is not their adoption. General source-to-IR
adequacy, verifier correctness, and compiler soundness remain open.

## Review and validation record

The completed consolidation review compared each translated document with its Japanese
baseline for retained premises, formulas, code, links, historical counts, and
status. Review also checked alignment with current English specifications and
the imaginary corpus. Document-reference checks cannot by themselves establish
translation fidelity or mathematical correctness.

The commands and completed review results are recorded in the
[conformance ledger](specification-status.md#english-documentation-consolidation)
and [0.1.2 release record](releases/v0.1.2.md#english-documentation-consolidation).
All ten editions passed review; all 102 original heading/explicit-anchor targets
and original link destinations are retained. Document-checker tests (14),
mathematical fixtures (39 exact and 52 finite convention checks), reference and
whitespace checks, and updated 156-file packaging/rebuild passed. All 55 current
documentation/license/notice files were compared with the archive. The earlier
155-file candidate and its Rust/Lean suites precede this translation; those
suites were not rerun for it. The subsequent checks are recorded separately. This work does
not include committing, tagging, pushing, or publication.
