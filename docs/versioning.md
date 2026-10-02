# Versioning and compatibility

Cargo.toml authoritative, [release procedure](crates-io-release.md). Selected0.2.7 development/unpublished; latest published0.2.6 [evidence](../tests/fixtures/releases/v0.2.6/publication.json). Synchronize Cargo/lock/both lakefiles/Python metadata+runtime/std Qargo, never dependencies. Unreleased accumulates work, no per-task bump; annotated vMAJOR.MINOR.PATCH, prereleases synchronized. Edition/spec/ledger independent.

## Choosing the next version

0.y.z(y>0) compatible fix/feature/deprecation/docs/maintenance PATCH; supported break MINOR/resetPATCH. 0.0.z PATCH may break; from1.0 fixesPATCH/additionsMINOR/breaksMAJOR. Combined largest increment. New enum variants/required fields/reserved valid names can break. Narrow user exceptions0.2.1 identity and0.2.3 manifests authorize no other PATCH break.

## What compatibility covers

Source/resolution/Rust/IR/evidence/stdlib/CLI/Lean plus phase/order/owners/effects/entry/cleanup. Reduced capacities/raised toolchains MINOR. Reject formerly accepted invalid input PATCH only under published violated rule, before-after diagnostic/regression. Future break requires Issue naming0.x.0/contracts/reason/migration/criteria before implementation; no duplicate backlog. V1 stable contracts/evidence gates.

## Release records and validation

Exact candidate norms/conformance/fmt/all-targets/Clippy/doctest/docs/examples/research/Lean source+compiled axiom-runtime audits/native comparisons/package notices/distribution; skipped checks honest, docs-only no Rust/Lean rerun. Tag exact clean checked commit, immutable published artifacts; correction new version. Selection/check/tag/push/publication/PyPI/binaries distinct within current authorization.
