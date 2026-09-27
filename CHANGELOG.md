# Changelog

Versions follow the [versioning and compatibility policy](docs/versioning.md).
Development milestones and the scope of their evidence are recorded
separately in [release milestones](docs/release-milestones.md).

## Unreleased

No unreleased changes.

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
