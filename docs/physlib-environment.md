# Physlib in the Lean proof environment

Status: **future dependency candidate; removed from the required environment**
(2026-09-27, v0.1.5 maintenance candidate). Lean/Mathlib remain at 4.30.0.
The historical addition and its successful tests are retained below; they do
not describe the current dependency graph.

## Current decision and reintroduction gate

No module in `lean/Qleisli/`, the Qleisli root, or the project axiom audit imports
QuantumInfo. Only the separate external integration probe used it. Remove the
Physlib requirement and its exclusively inherited documentation dependencies
from Lake resolution, and remove the corresponding build/audit from default
CI. Preserve all Qleisli declarations and the normal `Audit.lean` check.
The old local dependency cache need not be deleted; it is not an active
requirement or part of the released source.

Physlib remains the first candidate for the future **finite IR instrument/CPTP
bridge**: relate measurement, discard and reset Kraus branches to a
classical–quantum channel while preserving coordinate and arbitrary-reference
conventions. This task follows the verifier-first proof plan, independently
of the M1 language implementation; it is not a v0.1.5 completion condition.
Do not add the dependency merely to show that imports coexist.

Reintroduce it in the same change as a concrete Qleisli bridge module and a
named theorem obligation that uses its declarations. That change must:

1. State the bridge's domains, coordinate order, complete outcome instrument,
   reference extension and exact phase/cleanup boundary. A POVM's Lüders
   instrument alone does not represent every Qleisli instrument.
2. Re-evaluate compatible Lean/Mathlib/Physlib versions and pin the chosen
   commit. The old `f5242c99d796b59a390d26cd7d1a8057e04c46b5` is a reproducible
   baseline, not automatic approval of that version for future work.
3. Restore a scoped external declaration audit alongside the project audit,
   test the actual bridge, measure build cost and retain third-party notices.
4. Record specification, implementation, checked theorem, Rust correspondence
   and release compatibility separately; a toolchain increase is a MINOR issue.

The [preserved external probe](../research/quantum-libraries/PhyslibAudit.lean)
has no current build target. After explicitly restoring a compatible dependency
in an isolated experiment or a reviewed integration change, it can be run from
`lean/` with `lake env lean -DwarningAsError=true
../research/quantum-libraries/PhyslibAudit.lean`, after building its selected
QuantumInfo modules. This is an optional research reproduction, not a command
for the default environment. Keep it separate from the earlier 4.34.1 survey.

Current required checks from `lean/` are:

```sh
lake build Qleisli
lake env lean -DwarningAsError=true Audit.lean
```

The [v0.1.5 record](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/releases/v0.1.5.md) records dependency-removal validation.
Qleisli does not re-export QuantumInfo, so no public Qleisli Lean declaration
is removed. A downstream experiment importing QuantumInfo directly must declare
its own Physlib dependency instead of relying on Qleisli's former environment.

## Historical addition (superseded)

The following sections describe the earlier dependency addition, including the
then-current commands and successful external audit. Physlib was included in
v0.1.3/v0.1.4. Their release history and original test results are unchanged.

## Version selection

| Component | Selected version | Locked commit |
| --- | --- | --- |
| Qleisli | 0.1.3 maintenance candidate, unchanged | No new release/tag created |
| Lean | 4.30.0, unchanged | Selected by [lean-toolchain](../lean/lean-toolchain) |
| Mathlib | 4.30.0, unchanged | `c5ea00351c28e24afc9f0f84379aa41082b1188f` |
| Physlib | Upstream compatibility tag `v4.30.0` | `f5242c99d796b59a390d26cd7d1a8057e04c46b5` |

The [Physlib tag's toolchain](https://github.com/leanprover-community/physlib/blob/f5242c99d796b59a390d26cd7d1a8057e04c46b5/lean-toolchain)
and [dependency configuration](https://github.com/leanprover-community/physlib/blob/f5242c99d796b59a390d26cd7d1a8057e04c46b5/lakefile.toml)
both match the existing Lean/Mathlib 4.30.0 baseline. At that addition, Qleisli's
[lakefile](../lean/lakefile.toml) pinned Physlib by the full commit rather than a
moving branch. The then-current manifest locked every transitive dependency;
all nine pre-existing dependency records remained unchanged. The current
[lakefile](../lean/lakefile.toml) and [manifest](../lean/lake-manifest.json)
now reflect the removal above.

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
then included in [0.1.3](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/releases/v0.1.3.md), without selecting a new product version.
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

[preserved PhyslibAudit.lean](../research/quantum-libraries/PhyslibAudit.lean) imports both Qleisli and the selected
QuantumInfo interface and checks transitive axiom dependencies of eight external
declarations: independent-auxiliary partial trace, Kraus conjugation CP, channel
identity/product/partial traces, and the POVM measurement map and its matrix
formula. It rejects every axiom outside `propext`, `Classical.choice` and
`Quot.sound`, including `sorryAx` and native-evaluation axioms. The separate
[project audit](../lean/Audit.lean) continues to cover every imported Qleisli
declaration. Both checks were included in CI at that stage; current [CI](../.github/workflows/ci.yml)
retains only the required Qleisli build/audit.

This dependency integration does not import QuantumInfo into `Qleisli.lean`,
replace Qleisli's existing matrix definitions, or establish a source/IR
correspondence theorem. Physlib's POVM chooses a square-root/Lüders instrument;
arbitrary instruments and phase-sensitive coherent operators remain distinct
contract-design obligations. The first selected use from the
[0.1.5 dossier](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/decisions/2026-09-27-v1-path.md#proof-priority-and-first-physlib-use)
is a finite IR instrument bridge: measurement/discard/reset Kraus branches and
their classical–quantum CPTP map, with explicit coordinate/reference conventions.
That bridge is planned and has not been implemented or proved. The current
decision above defers the dependency until this concrete use is introduced.

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
The historical release manifests record their source repositories and immutable revisions.
These inherited documentation-tool dependencies are not Rust runtime dependencies.
