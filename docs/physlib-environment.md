# Physlib in the Lean proof environment

Status: **dependency installed; scoped build and axiom audits passed**, 2026-09-27. This adds mathematical
infrastructure to the existing Lean environment. It does not resume the deferred
symbolic-kernel implementation or add source-language/IR semantics.

## Version selection

| Component | Selected version | Locked commit |
| --- | --- | --- |
| Qleisli | 0.1.3 maintenance candidate, unchanged | No new release/tag created |
| Lean | 4.30.0, unchanged | Selected by [lean-toolchain](../lean/lean-toolchain) |
| Mathlib | 4.30.0, unchanged | `c5ea00351c28e24afc9f0f84379aa41082b1188f` |
| Physlib | Upstream compatibility tag `v4.30.0` | `f5242c99d796b59a390d26cd7d1a8057e04c46b5` |

The [Physlib tag's toolchain](https://github.com/leanprover-community/physlib/blob/f5242c99d796b59a390d26cd7d1a8057e04c46b5/lean-toolchain)
and [dependency configuration](https://github.com/leanprover-community/physlib/blob/f5242c99d796b59a390d26cd7d1a8057e04c46b5/lakefile.toml)
both match the existing Lean/Mathlib 4.30.0 baseline. Qleisli's
[lakefile](../lean/lakefile.toml) pins Physlib by the full commit rather than a
moving branch. The [manifest](../lean/lake-manifest.json) locks every transitive
dependency. All nine pre-existing dependency records remain unchanged.

At the time of the remote-ref check on 2026-09-27, the newest published Physlib
tag was `v4.34.0` (`58d73ebd01edb1c5caa3ea5db07b0245afe93cb0`); master was
`44c66d54be78db4693be9f8f92bd3b5ad124ed6f`, requiring Lean/Mathlib 4.34.1.
These are different from the compatibility tag selected here. Physlib's tag
numbers track Lean compatibility; its inspected Lake configuration does not
declare a separate package version.

The [earlier library survey](../research/quantum-libraries/README.md) tested that
newer master commit in a separate 4.34.1 environment. Those results remain
historical evidence for that commit, not validation of this older dependency.
The checks below validate the version actually installed in Qleisli.

No supported toolchain requirement, Qleisli public declaration, Rust dependency,
or language feature changes in this step. Under the [version policy](versioning.md),
this was recorded as compatible environment maintenance under `Unreleased` and
then included in [0.1.3](releases/v0.1.3.md), without selecting a new product version.
A future move of the supported baseline to
Lean 4.34.1 would require a separate compatibility and release decision.

## Use and validation boundary

From the repository root:

```sh
cd lean
lake exe cache get
lake build Qleisli QuantumInfo.Channels.CPTP QuantumInfo.Measurements.POVM
lake env lean -DwarningAsError=true Audit.lean
lake env lean -DwarningAsError=true PhyslibAudit.lean
```

The initial dependency fetch/cache population needs network access. Normal
builds use the committed manifest; run `lake update Physlib` only when deliberately
changing the lock. Generated `.lake` contents stay excluded from version control.

Physlib exposes its quantum-information API under `QuantumInfo`, for example
`import QuantumInfo.Measurements.POVM`, not `Physlib.QuantumInfo`.
The selected module build imports the channel/state dependencies used by POVM;
it does not build every module in Physlib or the `QuantumInfo` umbrella.

[PhyslibAudit.lean](../lean/PhyslibAudit.lean) imports both Qleisli and the selected
QuantumInfo interface and checks transitive axiom dependencies of eight external
declarations: independent-auxiliary partial trace, Kraus conjugation CP, channel
identity/product/partial traces, and the POVM measurement map and its matrix
formula. It rejects every axiom outside `propext`, `Classical.choice` and
`Quot.sound`, including `sorryAx` and native-evaluation axioms. The separate
[project audit](../lean/Audit.lean) continues to cover every imported Qleisli
declaration. Both checks are included in [CI](../.github/workflows/ci.yml).

This dependency integration does not import QuantumInfo into `Qleisli.lean`,
replace Qleisli's existing matrix definitions, or establish a source/IR
correspondence theorem. Physlib's POVM chooses a square-root/Lüders instrument;
arbitrary instruments and phase-sensitive coherent operators remain distinct
contract-design obligations. The [symbolic-kernel deferral](../ROADMAP.md#future-work-symbolic-semantic-kernel)
remains in force.

## Validation record

Version and lock inspection confirmed the tag/commit/toolchain correspondence
and unchanged pre-existing dependency records. Local macOS validation:

| Check | Result |
| --- | --- |
| `lake build Qleisli QuantumInfo.Channels.CPTP QuantumInfo.Measurements.POVM` | Passed (8,537 Lake jobs, including dependencies/cache hits) |
| `lake env lean -DwarningAsError=true Audit.lean` | Passed: 577 Qleisli declarations; only `propext`, `Classical.choice`, `Quot.sound` |
| `lake env lean -DwarningAsError=true PhyslibAudit.lean` | Passed: eight selected Physlib declarations; the same three allowed axioms |
| `python3 scripts/check_docs.py` | Passed local links, anchors and proof-module coverage |
| `python3 scripts/test_check_docs.py` | All 14 tests passed |
| `git diff --check` | Passed |

These are local results; adding the CI steps does not establish a hosted CI
run. The full Physlib/QuantumInfo umbrella was not built or audited. Rust tests
were not rerun for this dependency-only change; Rust source and dependencies
were unchanged. Commit, tag, push and release publication were not performed.

## Dependency attribution

Physlib remains third-party software under its
[Apache-2.0 license](https://github.com/leanprover-community/physlib/blob/f5242c99d796b59a390d26cd7d1a8057e04c46b5/LICENSE).
Its original source-file authorship and notices are retained in the dependency
checkout; it is not relabeled as Qleisli's work and no implementation is vendored.
The newly inherited packages `doc-gen4`, `leansqlite`, `UnicodeBasic` and
`BibtexQuery` have Apache-2.0 root licenses; `MD4Lean` has an MIT root license.
Their own notices and any nested third-party notices continue to apply.
The manifest records their source repositories and immutable revisions.
These inherited documentation-tool dependencies are not Rust runtime dependencies.
