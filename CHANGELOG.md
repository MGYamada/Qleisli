# Changelog

Versions follow the [versioning and compatibility policy](docs/versioning.md).
Development milestones and the scope of their evidence are recorded
separately in [release milestones](docs/release-milestones.md).

## Unreleased

No unreleased changes.

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
