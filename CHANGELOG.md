# Changelog

Versions follow the [versioning and compatibility policy](docs/versioning.md).
Development milestones and the scope of their evidence are recorded
separately in [release milestones](docs/release-milestones.md).

## Unreleased

Selected development version: **0.1.8**, retained at the user's request. See the
[implementation/migration record](docs/releases/v0.1.8.md). Historical entries
retain the version policy used at the time; the revised policy below governs
new changes.

### Added

- Fixed three-bit iterative QPE in ordinary `.qli`, compared with coherent QPE
  and an independent Fourier-instrument oracle on off-grid entangled inputs.
- Preserved first-source and curated repair sessions, with actual diagnostics,
  revision snapshots and CI checks for record integrity.

- A living v0.2.0 issue backlog connecting authoring friction to concrete
  source evidence, acceptance experiments and existing checking dependencies.

- Basis function parameter patterns for product components, whole subtrees
  and ignored basis values, checked through existing finite tables.
- N-ary tuple types, values and patterns, left-folded to exact binary trees.
  Independently checked pair meanings, executable clients and negative
  ownership/shape/depth regressions exercise these forms.

- Runnable Bell/teleportation/dense-coding/swapping components and shared
  operation-parameter QPE, amplitude-amplification and Hadamard-test examples.
  A checked-in `.qli` corpus covers successful clients, rejected authoring
  attempts and type-correct algorithm faults, including reference correlations.
- A concise implemented-source reference whose complete code fences compile
  and execute in Rust CI, and an evidence-based authoring feedback report.
- Fixed-width static operation parameters, explicit access constraints and
  bracket arguments, phase-fixed permutation/phase meanings, `bind_op`, and
  six checked composition constructors. One unchanged client can accept
  independently checked implementations of the same meaning.
- `FiniteMeaning` / `MeaningEvidence` reuse existing monomial and function
  evidence. Final IR retains receipts; no core acceptance rule is added.
- Parametric access/type/ownership checking and concrete exact cleanup checks,
  bounded specialization, source/evidence rejection regressions and a runnable
  operation-contract example.

### Changed

- Include expected/actual exact types in concrete mismatch diagnostics and
  suggest the explicit logical-contract form for restricted cleanup failures;
  keep acceptance, source locations, error categories and JSON v1 unchanged.

- Replace public Rust `Param.name` with `Param.pattern`; this incompatible
  AST migration is documented while the user retains development version
  0.1.8. Existing accepted binary `.qli` programs retain their meaning.
- Locate unreturned quantum ownership at its actual binding, including
  nested patterns, shadowing, parameters and computed-region binders.

- Align initial-development versioning with Cargo: for 0.y.z with y > 0,
  compatible fixes/features/syntax additions use PATCH; breaking changes use
  MINOR. Compatible features need no exception. Preserve historical migrations
  and the 0.1.8 checkpoint; 1.0+ rules and verification gates are unchanged.
- Reserve the new M1 keywords and extend public AST/token/error records;
  follow the release record's source and Rust migration. JSON v1 gains emitted
  `capability` / `contract` cases within its specified category set.
- Render meaning definitions and access requirements in source documentation.
- Split parser routines to preserve existing deep-syntax acceptance/rejection
  without increasing stack requirements. Keep old IR, toolchains and limits.

No tagging or publication has been performed for this development work. QIR import, remaining
machine interfaces, size generalization and M2 remain separate work.

## 0.1.7 — 2026-09-28

Start M1 with JSON results and bounded OpenQASM 3/QIR connections, under the
user's explicit feature-release exception. This is new functionality, not
compatible-maintenance-only work. The [release record](docs/releases/v0.1.7.md)
and [GitHub publication evidence](https://github.com/MGYamada/Qleisli/releases/tag/v0.1.7)
separate implementation, validation and publication.

### Added

- Start M1.1-A with bounded OpenQASM 3 import/export and QIR 2.0 Base text output.
  Require explicit OpenQASM initialization, retain exact gate phases and output
  order, and independently verify imported ownership through the existing core.
  Add a Rust host example, adversarial/exact tests and independent parser/LLVM
  validation. See the [connection contract](docs/interop-m1.1.md).
- Start M1 X1 with opt-in `--format=json` for `check` and `run`: one version-1
  `qleisli.result` object on stdout, including failures, stable categories,
  nullable original-source locations, and lexicographically ordered distributions.
- Add structured frontend diagnostic APIs alongside the unchanged legacy error
  APIs. Preserve parser/load provenance and coordinates from the loaded source
  snapshot, including Unicode, CRLF and empty EOF spans.
- Validate JSON independently with Python's JSON decoder as well as Rust CLI
  golden and diagnostic regressions; run the JSON suite in primary/MSRV CI.

### Changed

- Adopt the project title “Qleisli: A Language for Structured Quantum Algorithms”
  and the tagline “Write quantum algorithms in the language you use to think
  about them.” in a shorter README with a runnable introduction.
- Translate AGENTS.md into English, preserving the working rules and explicit
  version exceptions. Retain historical Japanese validation records, bilingual
  glossary terms and legacy link anchors.

### Compatibility and scope

- Human output and existing successful invocations remain unchanged. Unknown,
  duplicate or missing-value flags are usage errors. Prefix a path starting with
  `-` by `./`. `doc` keeps its existing Markdown interface and rejects JSON mode.
- JSON mode requires UTF-8 path identities. Non-UTF-8 paths report `project`
  without an invented location; legacy human mode retains its path support.
- Clamp only JSON probability endpoint roundoff within 2^-40; reject nonfinite
  or materially out-of-range output as `numerical`. The numerical reference
  simulator and exact evidence checker are unchanged.
- No new `.qli` form, core checking rule, IR variant, production dependency, existing capacity or
  toolchain requirement. New adapters have explicit local bounds; validation-only
  OpenQASM/ANTLR and LLVM dependencies run separately. QIR import, adaptive
  connections and Python distribution remain pending. X2–X6, N1–N6 and M2 remain unimplemented.

## 0.1.6 — 2026-09-28

IR/evidence maintenance plus the user's explicit version-policy exception for
the comment/docstring extension. Rust and Lean project versions remain at
0.1.6. The [implementation and validation record](docs/releases/v0.1.6.md)
separates local checks from exact-commit CI, tagging and publication in the
[GitHub release record](https://github.com/MGYamada/Qleisli/releases/tag/v0.1.6).

### Documentation feature and migration

- Add nested `/* ... */` comments and Rust-style `//!`, `///`, `/*! ... */`
  and `/** ... */` documentation. Check attachment, retain original byte spans
  and expose metadata separately through `parse_documented_module`; existing
  public AST fields and lexer token variants stay unchanged.
- Add `qleisli doc <source-file>` and Markdown rendering without execution or
  a verification claim. Document every bundled module and all twelve public /
  three private definitions in English; ordinary stdlib checking is unchanged.
- Doc spellings previously treated as arbitrary comments now require valid
  placement. Line comments end at LF/EOF; bare CR is forbidden in doc text.
  Use ordinary comment spellings or LF/CRLF when migrating, as described in
  the [extension specification](docs/documentation-comments.md).
- Keep 0.1.6 at the user's explicit request despite the normal MINOR rule.
  This feature and its source-acceptance changes are not compatible-only
  maintenance; the exception does not apply to future feature work.

### Fixed

- Enforce the existing raw-IR limit of 64 nested classical branches before
  entering either arm. Previously a 65th branch with empty arms was accepted;
  it now receives the existing depth-limit diagnostic at that branch.

### Validation

- Add raw-IR cases at 63, 64 and 65 levels, with empty/nonempty deepest arms
  on both sides, checking acceptance and rejection locations.
- Check function-evidence preflight at 31, 32 and 33 levels in both the
  implementation and specification, including inactive empty branches and
  complete zero-width ownership. Its existing 32-level bound is unchanged.

### Design

- Select future Python bindings and bounded OpenQASM 3/QIR import/export to
  reduce adoption cost through a shared checked compiler core. Record phase,
  ownership, measurement-reuse, evidence-binding and wheel-installation gates.
  This is a [direction](docs/interoperability-roadmap.md), not implemented
  interoperability or a completed extension specification; features require MINOR.
- Adopt the small trusted-core boundary: convenience belongs in untrusted
  desugaring, not in the checker. Inventory raw-only IR variants as compatibility
  debt and specify the obligations for a future versioned core reduction.
- Define desugaring consistently as meaning-preserving translation to already
  specified core operations with untrusted output for independent checks.
  Distinguish it from source checking, runtime adaptation and approximation.
- Record the risk of fixing the design to one future gate architecture and the
  recommendation to parameterize coefficient domains, separating exact,
  approximation and device/noise contracts. Cite STAR primary work; keep the
  current R8 implementation and selected M2 angle profile unchanged.

### Internal

- Route legacy raw `QuantumIf` arm execution through the existing finite
  `CircuitStep` vocabulary. Preserve public IR, independent exact extraction,
  in-place primitive execution and existing execution-step limits. This removes
  duplicate numeric interpretation, not verifier rules or evidence obligations.
- Compare all legacy arm primitives, both polarities, empty/Unit arms and mixed
  sequences with independent exact extraction, including coherent references,
  reversed physical axes, exact budget boundaries and state-vector reuse.

The IR/evidence changes preserve existing valid core programs and public IR.
The comment extension adds APIs and the documented lexical/attachment changes
above. Quantum rules, declared capacities, dependencies and toolchains are
unchanged; no original M1/M2 slice or general proof is implemented.

## 0.1.5 — 2026-09-27

Compatible review/design maintenance release. Rust and Lean versions are
synchronized at 0.1.5. The [release record](docs/releases/v0.1.5.md) separates
local validation from the exact commit, CI, tagging and publication recorded
in the [GitHub release](https://github.com/MGYamada/Qleisli/releases/tag/v0.1.5).

### Changed

- Reflect the [v0.1.4 review](docs/reviews/v0.1.4.md) with a concrete next-scope
  dossier and version-independent M0–M5 milestones. Fixed-width M1 may retain
  existing finite checking; bounded kernel continuation and hierarchical IR
  gate M2 size generalization. Replace indefinite deferral and no-go completion
  with a selected path and dated scope checkpoint.
- Advance the local v0.1.5 maintenance roadmap with explicit completion
  evidence for review/specifications, checks and distribution; keep exact-commit
  CI, tagging and publication as pending release gates.
- Complete the selected future M1 language and machine-interface specifications:
  static grammar/access judgments, permutation/phase meanings, portable finite
  IR/evidence, JSON diagnostics, trajectory sampling, typed retries and source
  limits with legacy migration. Specify the bounded M2 hierarchy/schema/QPE
  profile and implementation acceptance matrices; no new feature is implemented.
- Correct the follow-up specification review: retain and independently validate
  exact root input/output type trees in portable IR, reject equal-width tree
  substitutions in requested contracts, and define controlled operations in
  the existing least-significant-control basis order. Add future acceptance
  cases; these interfaces remain unimplemented.
- Make truth-table-free reversible synthesis and hierarchical IR/evidence
  binding explicit scaling prerequisites. Record basis-derived semantic
  vocabulary, ideal dyadic QPE angles, early portable evidence/JSON/sampling
  slices and special-form/public-IR migration as future MINOR work.
- Prioritize independent IR-verifier and evidence-kernel proof obligations;
  select finite instrument/CPTP semantics as the first planned Physlib use.
- Defer Physlib to that future concrete bridge: remove its direct requirement
  and five exclusive transitive packages, drop its default CI build/audit,
  and preserve the external probe under research. Retain all nine Mathlib
  dependency records, Lean/Mathlib 4.30.0 and Qleisli proof declarations.
- Centralize mutable planning state and a fourteen-group rule-to-code,
  test and proof inventory in JSON; generate Markdown and reject drift in the
  existing document checker. Preserve historical records and legacy IDs.
- Correct AE's conjugation-based access/cost account, Shor indentation and
  dependency-history wording; simplify AGENTS.md to durable rules and links.

### Validation

Add five document-checker regressions and six phase-sensitive conjugation
convention fixtures. The [validation record](docs/releases/v0.1.5.md#local-validation)
states actual local checks and remaining publication gates. Numerical fixtures
do not establish general theorems or execute imaginary source.

No production/research Rust, Qleisli proof declaration, public behavior,
supported capacity or toolchain change. The unused external Lean dependency
is removed as above; no `.qli` migration is needed. Experiments importing
QuantumInfo directly must declare their own Physlib dependency.

## 0.1.4 — 2026-09-27

Compatible documentation/plan maintenance release. Rust and Lean project
versions are synchronized at 0.1.4. The [release record](docs/releases/v0.1.4.md)
records validation scope; the [GitHub release](https://github.com/MGYamada/Qleisli/releases/tag/v0.1.4)
identifies the exact commit, CI, tag and published source distribution.

### Changed

- Adopt the [v0.x plan](docs/v0x-roadmap.md) and B019-1–B019-6 boundary through
  v0.1.9: finite-core compatibility and conformance, evidence-boundary review,
  explicit proof obligations, next-minor decisions and reproducible validation.
- Make operation capabilities the next design focus alongside ownership,
  effects, established auxiliary invariants and proof contracts. Require new
  abstractions to remove an author obligation through independently checked
  evidence. Existing finite effects and certificates remain the foundation.
- Assign conditional themes from v0.2 toward v1 without adopting new syntax
  or APIs. Preserve the symbolic-kernel deferral with no selected release,
  the scaling prerequisite, six imaginary drafts and executable V1-C1–C5.
- Align current-version guidance and remove the stale README statement that
  the preceding 0.1.3 release was still awaiting publication.

No production/research Rust or Lean source, public contract, supported capacity,
toolchain requirement or dependency changes. The independent non-published
research package retains 0.1.3. No migration is needed.

### Validation

Fresh local candidate checks pass on macOS with Rust 1.98.1 and 1.85.0:
258 production and 43 research tests each, primary fmt and all-target Clippy
for both packages. Pinned Lean builds and separate audits pass for 577 Qleisli
and eight Physlib declarations. All 43 Python tests, 52 mathematical checks,
39 exact assertions and all ten CLI projects and Shor pass. The
[P014 record](docs/releases/v0.1.4.md#local-candidate-validation) separates
candidate distribution checks, clean-commit CI and publication. These results
do not complete later maintenance audits or new language features.

## 0.1.3 — 2026-09-27

Compatible maintenance and mathematical-research release. The Rust and Lean
packages remain aligned at 0.1.3. The [release record](docs/releases/v0.1.3.md)
states validation scope; the [GitHub release](https://github.com/MGYamada/Qleisli/releases/tag/v0.1.3)
identifies the exact commit, CI, tag and published source distribution.

### Fixed

- Reject empty, ragged and dimensionally incompatible matrices in the
  imaginary-design and exact semantic-contract helpers before `zip` can
  silently truncate data. Preserve valid rectangular/scalar fixtures and
  rational/quadratic arithmetic.
- Reject NaN and infinity in either comparison operand, including complex
  components, with `ValueError`. Invalid input cannot make positive or
  negative mathematical checks pass. Finite comparison tolerance is unchanged.
- Add 29 helper regression tests across the two suites and run both in CI.
  Preserve the existing 52 imaginary-design checks and 39 exact assertions.

### Design and independent research

- Verify the supplied v0.1.2 review against the tag and release CI. Require
  composition without whole logical dense matrices before size generalization,
  with an explicit first-QPE angle and exact/approximate checking profile.
- Record a first-principles meaning/implementation/evidence architecture and
  an independent, non-published symbolic semantic-kernel prototype. Its typed
  terms, frozen requested contracts and bounded exact leaves support a limited
  raw-IR adapter; it does not change production source acceptance or execution.
- Add 20 local Lean semantic lemmas with explicit premises. These mathematical
  rule proofs do not prove correctness of the Rust checker or compiler.
- Retain the prototype and regressions while deferring further kernel development
  and production integration to future roadmap work, with no target release.
- Record isolated Physlib/QuantumInfo and lean-quantum interface experiments,
  with pinned sources, reproducible probes and declaration-level axiom evidence.

### Lean environment

- Add Physlib's compatible `v4.30.0` commit
  `f5242c99d796b59a390d26cd7d1a8057e04c46b5`, preserving Lean/Mathlib 4.30.0
  and all pre-existing dependency revisions. Lock the inherited documentation
  dependencies and record their licenses.
- Build selected QuantumInfo state/channel/measurement dependencies in CI and
  audit eight external declarations separately from all Qleisli declarations.
  Library availability does not establish source/IR semantic correspondence.

### Validation and compatibility

Local macOS release checks pass on Rust 1.98.1 and minimum Rust 1.85.0:
258 production tests and 43 research tests each, primary fmt, and Clippy on both.
The 43 research tests include 5,425 exact differential cases within one test.
Python checks cover 18 imaginary-helper, 11 exact-helper and 14 document-checker
regressions, plus the 52 mathematical checks and 39 exact assertions.
The release record separates local checks, hosted Linux CI, package validation
and publication evidence.

Production Rust behavior, existing public contracts, capacity limits and
supported toolchains are unchanged. No source migration is needed.
Imaginary source and production symbolic integration remain unimplemented;
these checks do not establish general compiler soundness.

## 0.1.2 — 2026-09-27

Documentation/design maintenance release. Both project manifests are
synchronized at 0.1.2. The [release notes](docs/releases/v0.1.2.md) record scope
and validation; the [GitHub release record](https://github.com/MGYamada/Qleisli/releases/tag/v0.1.2)
identifies the tagged commit, required CI, source archives, and publication.

### Changed

- Align current-version records and define a staged roadmap for six imaginary
  Qleisli 1.0 algorithm drafts, per-draft semantic contracts, a shared
  requirements index, semantic review, and release validation.
- Make the next-minor sequence explicit: complete the existing imaginary-v1
  prerequisite, select and specify the smallest required generalization,
  then implement and validate it with evidence retained in final IR.
  V1-C1–C5 remain the separate executable acceptance target.
- Translate ten current Japanese design, planning, overview, and finite-IR
  proof documents into English. Preserve semantic premises, proposal/proof
  status, historical evidence, source links, and legacy heading anchors.
  Add a documentation authority/inventory map; retain Japanese operational
  guidance and original dated conformance entries as supporting records.
- Correct the review summary's odd-QSVT direction to right-to-left singular
  spaces, matching the unchanged `L p(Sigma) V†` contract and circuit.

### Added

- An English language-evolution framework separating current normative rules,
  imaginary notation, extension specifications, implementation and proof.
  Correct stale v0.1 status summaries without changing acceptance rules.
- Six original imaginary-v1 algorithm bodies for QPE, Grover, amplitude
  estimation, Shor, a symmetric Szegedy walk and QSVT; per-draft contracts,
  shared requirements R01–R14 and a semantic/counterexample review.
- A reproducible 52-check mathematical script covering Fourier/phase conventions,
  residual/reference coherence, amplification signs, factor validation, walk
  reflections, and QSVT parity/selector boundaries, also run in documentation CI.

### Validation and limits

Before English consolidation, the local 0.1.2 candidate passed 258 Rust tests and Clippy on both Rust 1.98.1
and 1.85.0, Lean build and its 527-declaration axiom audit, 14 documentation
checker tests, 39 exact examples, 52 new mathematical checks, all ten CLI
projects and Shor, and 155-file source-candidate packaging/rebuild. Linux CI
and clean-release-commit packaging are publication gates; their final results
belong in the GitHub release record. Subsequent
English translation passed independent fidelity review, document checks and
14 checker tests, the 39/52 mathematical fixtures, and updated 156-file
packaging/rebuild, recorded [separately](docs/releases/v0.1.2.md#english-documentation-consolidation).
It does not claim to rerun Rust execution tests, Clippy, or Lean suites.

The initial design-corpus prerequisite before 0.2.0 is met by the recorded
artifacts and review. All imaginary source remains uncompiled; no new language
forms, standard APIs or general proof guarantees are delivered. The
[release record](docs/releases/v0.1.2.md) and
[conformance ledger](docs/specification-status.md) distinguish local candidate
validation from clean-commit CI, tagging and publication. The compiler fixes
and historical results of 0.1.1 remain recorded under 0.1.1.

## 0.1.1 — 2026-09-27

Compatible maintenance release. Both project manifests are synchronized at
0.1.1. See the [release notes](docs/releases/v0.1.1.md) for scope and checks;
the [GitHub release record](https://github.com/MGYamada/Qleisli/releases/tag/v0.1.1)
identifies the published commit and its CI evidence.

### Changed

- Require an initial imaginary Qleisli 1.0 code corpus before v0.2.0 feature
  implementation or release, covering QPE, Grover, amplitude estimation,
  Shor, quantum walk, and QSVT. Noncompiling, revisable design code and its
  semantic requirements are distinct from executable v1 acceptance evidence.
  The policy is adopted; the corpus is still pending and is not a prerequisite
  for this compatible maintenance release.

### Fixed

- Reuse immutable function evidence within one frozen compiler project without
  repeatedly comparing and charging its source/raw snapshots. New artifacts
  still pay for snapshot copies; external binding checks remain exact.
- Point independent IR contract errors at the originating source expression,
  including nested branches, and report an exact counterexample entry.
  Parser messages identify parse failures without changing public error codes.
- Detect material numerical leakage before certified auxiliary projection,
  preserving exact release certification and unnormalized probability weights.
  Scale only the diagnostic ratio to prevent subnormal or underflowed weights
  from hiding leakage; preserve stored amplitudes and non-finite-weight alarms.
- Harden signed dyadic scaling against a future denominator-bound change and
  make contract-composition basis invariants explicit.
- Clarify CLI bit order and tiny numerical weights; address the reported
  older-Clippy expression/lifetime patterns and add Clippy to the MSRV CI job.
  Actual Rust 1.85 validation also identified test bit-packing expressions;
  explicit parentheses preserve their meaning and satisfy MSRV Clippy.

### Verification

- Validate the 0.1.1 candidate on macOS: 258 tests and all-target Clippy pass
  on both Rust 1.98.1 and minimum Rust 1.85.0. Documentation checks, 39 exact
  assertions, Lean build and the 527-declaration axiom audit, all ten CLI
  projects, Shor, and candidate source packaging/verification pass. Linux CI
  and clean-release-commit packaging are separate publication gates, recorded
  against the exact release commit in the GitHub release record.
- Reproduce the cleanup alarm's underflow failure before fixing it. Add a
  scale-invariance regression covering real/imaginary leakage, both sides of
  the alarm threshold, subnormal and zero-rounded weights, the smallest
  positive amplitude, and unchanged projected amplitude bits.
- Add deterministic generated comparisons of exact circuit matrices with
  numerical execution, adjoints, controls, and retained physical auxiliary
  implementations. See the [review disposition](docs/reviews/claude-v0.1.0.md)
  for checked findings, deferred design changes, and validation results.

## 0.1.0 — 2026-09-27

Initial source release. See the [release notes](docs/releases/v0.1.0.md)
for usage, verification scope, and known limits. The annotated `v0.1.0` tag
identifies the release commit; the GitHub release records publication.

### Added

- Finite `.qli` parsing, module resolution, type/effect/linear-ownership
  checking, independent raw-IR verification, and reference execution.
- Bundled finite basis, algorithm-routine, transform, and arithmetic
  definitions, with executable quantum-algorithm examples.
- Exact finite semantic contracts `U E_in = E_out u`, compositional evidence,
  and independently checked auxiliary zero return.
- `apply_contract` with immutable function evidence retained through
  composition, axis remapping, adjoint, coherent control, and repetition;
  interchangeable phase-oracle implementations under one fixed client.
- Explicit ownership, semantics, and source/IR specifications; a separate
  Lean development for the recorded ownership and matrix lemmas.
- Apache-2.0 licensing for Qleisli's own code, proofs, examples, and
  documentation, with contribution and versioning policies and explicit
  attribution to Masahiko G. Yamada.
- A Japanese design note on quantum bookkeeping as a language responsibility,
  with QPE, amplitude amplification, and Shor as successive design tests.
- CI coverage for the declared minimum Rust version, 1.85.0, alongside the
  primary Rust toolchain, Lean build/axiom audit, and documentation checks.

### Verification and limits

The [release validation record](docs/specification-status.md) reports the local
245 Rust tests, 14 documentation-checker tests, 39 exact mathematical example
assertions, Lean build and 527-declaration axiom audit, and package validation.
Those are implementation/model checks, not a general proof of the Rust compiler
or noisy-hardware behavior. General size/operation parameters, portable proof
loading, and the v1 algorithm-structure milestone remain open.
