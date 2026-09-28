# Qleisli working guidelines

## Start from the design

This repository is design-first. Before working, read [README](README.md),
[design philosophy](docs/design-philosophy.md), the [AI-era goal](docs/ai-era-goal.md),
[algorithm-structure goal](docs/algorithm-structure-goal.md), [formal core](docs/formal-core.md),
[ROADMAP](ROADMAP.md), and [quantum-language requirements](docs/quantum-language-requirements.md).
Consult the relevant drafts. The user's latest instructions take precedence.

When adding algorithm components, read the [corpus](docs/algorithm-corpus.md)
and [routine contracts](docs/algorithm-routines.md). For standard-library work,
read the [layer-3 plan](docs/stdlib-roadmap.md) and [contract ledger](docs/stdlib-contracts.md);
record each public API's contract, verification state and adoption criteria.
Use the [static-operation contract](docs/static-operations.md) to determine the
implemented inverse/control/repetition scope. Planned notation is not an API.

`Cargo.toml` is authoritative for the current version. Consult the
[generated status and rule inventory](docs/current-status.md) and the matching
release record. Distinguish version selection, design adoption, implementation,
validation, proof, tagging and publication. Preserve the finite contract
foundation and follow the [acceptance criteria](docs/release-milestones.md),
[conformance history](docs/specification-status.md), [language v0](docs/language-spec.md)
and [grammar](docs/syntax-v0.md). General Rust adequacy and soundness proofs are open.

**North star: make the language people use to think about quantum algorithms
coincide with the language they use to write programs.** V1 requires actual
source for Shor, QPE and Grover that preserves textbook structure and meets
V1-C1–C5. Retain fixed-size examples as regressions; names or pseudocode alone
cannot satisfy these gates.

Prioritize executable `.qli` examples and source fixtures when evaluating
authoring ergonomics, especially for LLMs. Discover missing abstractions from
real programs, retain minimal failed attempts and semantic counterexamples,
and update the [authoring report](docs/qli-authoring-feedback.md). Keep the
[quick reference](docs/qli-quick-reference.md) copyable and its code CI-checked.
An authoring exercise is not a measured model benchmark or an algorithm proof.

Follow the [decision dossier](docs/decisions/2026-09-27-v1-path.md) and
[version-independent M0–M5 plan](docs/v0x-roadmap.md). In 0.y.z with y > 0,
compatible fixes and features use PATCH; breaking changes use MINOR. An audit
does not itself require a release. Fixed-width M1 may use existing finite
checks. Before generalizing sizes, establish composition of meanings, encodings
and evidence without global dense matrices, together with an evidence-bound
hierarchical IR. General predicates and arithmetic require reversible circuit
synthesis rather than full-space truth tables. The bounded symbolic-kernel
continuation is an M2 design decision, not production integration or blanket
permission to bypass the feature's specification and validation gates.

Evaluate abstractions by which user obligations they remove and which checker
validates their evidence. Mathematical unitarity does not imply access to an
inverse or controlled implementation. A `Clean` name or lifetime is not evidence
of zero return. Preserve existing special-form semantics and compatibility.

## Keep the trusted core small

Follow the authoritative [trusted-core principle](docs/design-philosophy.md#keep-the-trusted-core-small):
convenience belongs in untrusted desugaring/adapters, with independent checking
of the result. New checker rules must identify a semantic or evidence obligation
that the existing core cannot express; convenience alone is insufficient.

Treat verifier variants with no frontend producer as signs of compatibility
debt. Update the [producer/debt/reduction inventory](docs/interoperability-roadmap.md#ir-reduction-and-the-trusted-boundary).
Remove public APIs only through a versioned migration. Sharing numerical
execution code or moving files is not a reduction of the trusted acceptance base.

Use the [authoritative definition of desugaring](docs/terminology.md#desugaring-layer):
meaning-preserving translation of convenient syntax/representations to already
specified core operations with explicit ownership and effects. It introduces
no primitive meaning or acceptance rule. Proposed IR/evidence remains untrusted.
Parsing, source checking, approximate synthesis and post-verification execution
adapters are separate responsibilities. Verified output IR alone does not prove
preservation of the original input's meaning.

The [coefficient-domain note](docs/coefficient-domains.md) records future
parameterization and separation of exact and approximate contracts. It changes
neither the current `Z[ζ8,1/2]` implementation nor M2's selected angle profile.
Before adding a domain, specify its arithmetic, equality, complex interpretation,
limits and evidence binding. Arbitrary trait implementations or floating-point
tolerances cannot issue evidence. Keep ideal semantics, approximation error,
device noise and exact auxiliary zero return distinct.

Use the [M1 specification](docs/next-minor-spec.md), [machine interfaces](docs/machine-interface-spec.md)
and [M2 IR/checker profile](docs/hierarchical-ir-spec.md), distinguishing their
specifications from implementation. The [six imaginary-v1 drafts and index](docs/imaginary-v1/README.md)
and [semantic review](docs/imaginary-v1/review.md) satisfy the initial-draft
prerequisite only. Final syntax/APIs, implementation, validation and proof are
separate. Preserve [R14 and the QPE prerequisites](docs/imaginary-v1/requirements.md#scaling-prerequisite-for-r14)
and revise drafts when counterexamples require it.

## Proofs and records

Follow the [proof priorities](docs/formal-core.md#4-theorem-status-and-proof-work):
independent IR verification and the evidence kernel precede general frontend
adequacy. Keep Lean/Mathlib at 4.30.0 and run `Audit.lean` for proof work.
Physlib remains a [future dependency](docs/physlib-environment.md); recheck its
compatibility and external axioms when adding a concrete semantic bridge that
uses it. Library availability is not a proof of Qleisli semantics.

Update current state through `docs/project-status.json` and the manifests;
generate tables with `python3 scripts/check_docs.py --write-status`. Preserve
historical adoption and validation results. Record design decisions in the
dossier and executed results in conformance/release records.

## Licensing

- Unless individually stated otherwise, Qleisli's code, standard library,
  examples, tests, scripts, Lean proofs and documentation are **Apache-2.0**.
  Maintain [LICENSE](LICENSE), [NOTICE](NOTICE) and [CONTRIBUTING](CONTRIBUTING.md).
- Identify the project copyright holder as **Masahiko G. Yamada**, initially
  `Copyright 2026 Masahiko G. Yamada`. Keep LICENSE/NOTICE/README attribution
  consistent. Do not replace contributor or third-party attribution with it.
- Preserve existing copyright, license and attribution notices. Record the
  source and permission terms of third-party material, check compatibility,
  and retain required notices. Dependencies are not Qleisli-owned work.
- Include appropriate metadata in new public packages; Rust packages use
  `license = "Apache-2.0"`.

## Versioning and releases

[Versioning](docs/versioning.md) is authoritative.

The user adopted Cargo-compatible 0.y.z versioning on 2026-09-28. Compatible
features need no exception. Preserve historical release/migration records and
the selected development version 0.1.8, explicitly retained by the user for
the authoring continuation. Record its public Rust AST migration and remaining
gates in the [0.1.8 record](docs/releases/v0.1.8.md). Type/size
parameters and cross-interface QPE reuse remain future work at the user's request.

- `Cargo.toml`'s `package.version` is authoritative; synchronize Qleisli's own
  `lean/lakefile.toml`. Compiler, bundled library and proofs currently share a
  release. Do not synchronize dependency versions with the project version.
- Use `MAJOR.MINOR.PATCH` and annotated Git tags `vMAJOR.MINOR.PATCH`.
  Accumulate unreleased work in [CHANGELOG](CHANGELOG.md); do not bump per task
  or commit. Align version, changelog and current descriptions when selecting
  a release. Prereleases such as `0.2.0-rc.1` are allowed.
- In 0.y.z with y > 0, PATCH covers compatible fixes, refactoring, documentation,
  features, syntax additions and deprecations without removal. MINOR is for
  breaking changes, resetting PATCH to zero. In 0.0.z, successive PATCH releases
  are incompatible. Document migration and use the largest required increment
  for combined changes; new features still need specifications and validation.
- From 1.0.0, use PATCH for compatible fixes, MINOR for compatible additions and
  deprecations, and MAJOR for breaking changes. Reaching 1.0 requires evidence
  for V1-C1–C5 and explicitly stabilized public contracts.
- Compatibility includes `.qli` syntax/resolution; public Rust, IR and evidence
  APIs; standard APIs; CLI commands, exits and results; and public Lean
  declarations. Phase, bit/axis order, ownership, effects, entry premises and
  auxiliary zero return are public semantics. Enum variants and struct fields
  can also be breaking changes.
- Rejecting an input/evidence that already violated published rules can be a
  PATCH fix. Record the violated rule, before/after behavior, diagnostic and
  regression. A new restriction or changed meaning for previously supported
  inputs, or an incompatible Rust change, cannot use this exception.
  Reduced capacities and raised toolchain requirements need
  compatibility review and at least MINOR in 0.y.z with y > 0.
- Keep specification v0, ledger format v1, development stages and product
  versions separate. Never mechanically renumber historical checks/spec files.
- For release, check changelog, norms, conformance, Rust fmt/all-target tests/
  Clippy, document checks, Lean build/axiom audit, representative examples and
  package license notices. Record performed and skipped checks accurately;
  documentation-only edits do not justify claims of rerun Rust/Lean tests.
- Tag the verified commit containing the actual release changes. Never tag an
  older HEAD while implementation remains uncommitted. Do not mutate published
  tags/artifacts; corrections require a new version. Version selection, tagging,
  push, hosted publication and registry distribution are distinct actions;
  record authorization scope and what actually happened.

## Language and status discipline

- Write production language specifications in **English**, including normative
  grammar, typing/effect/ownership rules, semantics, examples and IR mappings.
  Standard-library public names, contracts, references, comments and example
  explanations must also be English.
- English is authoritative. Supporting Japanese design discussions/translations
  may coexist if their relationship is explicit. Follow the
  [documentation map](docs/documentation-map.md). Preserve dated Japanese
  conformance entries as historical evidence.
- Translate existing Japanese material when preparing it for production use;
  preserve mathematical premises, contracts and proposed/adopted/implemented/
  tested/proved status. These working guidelines are now English too.
- Distinguish proposal, provisional decision, adoption, implementation and
  validation. Parsable source is not executable without checking and lowering.
- Mathematical claims need types, premises and equations or counterexamples.
  Separate resource safety, ideal quantum soundness, protocol/algorithm
  correctness and hardware behavior. Do not claim that typing proves physical
  correctness before the applicable theorem is implemented and proved.
- Human/AI source, evidence proposals and raw IR follow identical verification.
  Author identity and prose are not evidence; never bypass sealed primitives
  or the independent verifier.
- Resolve conflicts between stage-0 decisions and [language v0](docs/language-spec.md)
  in the same change, or record them explicitly as unresolved.

## Quantum invariants

- Arbitrary free-vector-space `bind` is not a safe execution API. Distinguish
  isometries for pure operations from reversible unitary operations.
- `Q<A>` is an ownership type, not a computation-effect type. Composition tracks
  resources, classical values and effects with Kleisli-inspired principles;
  a strict monad structure is not proved.
- Quantum ownership is linear: no unknown-state cloning, aliased wire operands
  or implicit discard. Sharing basis indices does not copy quantum resources.
- Separate owners do not imply product states or absence of entanglement.
  Interpret local operations, measurement and discard globally; pure release
  requires evidence eliminating correlations.
- Keep measurement/reset/discard out of pure operations. Distinguish classical
  `if` from coherent `qif` and retain phase required by controlled operations.
- Initial `measure_z` consumes logical ownership and returns only `CBit`.
  Reusing a physical element does not resurrect that logical owner.
- Pure auxiliary release needs static zero-return/separation evidence for all
  inputs and reference systems. A borrow duration alone is insufficient.
- Diagnose unsupported backend capabilities; never silently change meaning.

## Recording specification changes

Classify each new `.qli` syntax or standard API as a language form, sealed
built-in operation, or ordinary `.qli` definition. For quantum/effectful forms,
record input/output types, ownership, effects, acceptance/rejection examples
and lowering. Specify totality and types of basis functions. Update
[standard-library organization](docs/standard-library.md) for stage 0, and
[language v0](docs/language-spec.md) plus [ROADMAP](ROADMAP.md) for stage 1.
Run relevant checks after Rust changes and record actual results. Semantic
prose alone does not make unimplemented tests pass.
