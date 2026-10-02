<a id="qleisli-ロードマップ"></a>

# Qleisli roadmap

Status: the [design principles](docs/design-philosophy.md) are fixed. [Goal 1: a quantum language for the AI era](docs/ai-era-goal.md) and [goal 2: structuring quantum algorithms](docs/algorithm-structure-goal.md) remain in development. [Layer 3: a standard algorithm vocabulary](docs/stdlib-roadmap.md) has a v1 contract ledger and finite static-operation implementations. Stage 0 is complete as documentation; Stage 1 has a normative finite-core v0 specification but unfinished proofs; Stages 2–4 are partially implemented. Alongside minimal examples such as Bell, shared components build finite Grover, BV, bit-flip correction, QPE, and N=15 order-finding examples. Completion is judged against documented criteria and evidence. The [frontend documentation](docs/frontend-v0.md) distinguishes executed `.qli` from unimplemented syntax proposals.

This is the authoritative English development plan. The [release milestones](docs/release-milestones.md) and version-specific release records govern acceptance and publication. Current targets and implementation boundaries below do not adopt future syntax or imply completed proofs. See the [documentation map](docs/documentation-map.md) for authority and translation status.

## Published v0.2.6: observing verification and finite corpus

Published on 2026-10-02: VM-26 observing/SSA/branch-function checking and proofs,
60 finite translations, docs reduced by at least half, bounded AGENTS.md,
CI policy and compatible review repairs. [Publication evidence](tests/fixtures/releases/v0.2.6/publication.json)
binds exact-source CI, matching Linux/macOS packages, fresh registry installation,
hosted docs and complete source downloads. Rust remains authoritative;
VM-27–29 and general source/backend/theorem gates remain open.

## Published v0.2.5: refactoring, documentation and finite corpus

Selected on 2026-10-01. Consolidate CLI source execution, canonical numeric
argument parsing and sample-result transport; separate sized argument validation
from execution. Encapsulate frontend flattening state, separate finite numerical
state/circuit execution, consolidate explicit IR wire maps, and isolate native
hierarchy response/process handling. Refactor the Lean conditional checker,
capacity constants and protocol/CLI modules with compatibility proofs and audits.
Retire 17 obsolete docs, condense current specifications and add six small
translations from frozen corpus inputs, bringing the count to 54. The
[development record](https://github.com/MGYamada/Qleisli/blob/b316a5065527c84f3dbcb059750637e2b14b0965/docs/releases/v0.2.5.md) records actual checks.
VM-25 pure raw-IR migration retains its separate proof/binding gates;
refactoring does not complete that packet or publish a release.

## Published v0.2.4: documentation, corpus and finite evidence

Published and verified on 2026-10-01. Documentation reduction, six small finite
corpus translations and the VM-24 finite component are recorded with their
[validation and publication evidence](https://github.com/MGYamada/Qleisli/blob/7bfcd36916199b05d5ab11851d38d53375ccf71e/docs/releases/v0.2.4.md). Production
Rust authority, edition 2026 and public contracts remain unchanged.

## Published v0.2.3: Qleisli edition 2026

The user selected v0.2.3 on 2026-09-30 for [explicit language editions](docs/language-editions.md).
All current `.qli` sources and `.qlt` drafts use `"2026"`, declared in each
source tree's `Qargo.toml`. The `std` qrate lives in `stdlib/`; other source trees
will all migrate to qrate management in the future. No repository-root manifest
is used. The [first VM-23 arithmetic/equality and H/T slice](tests/fixtures/verification_v023/README.md)
now satisfies its arithmetic proof/comparison gates, with general scalar/matrix
meaning, canonicality and exact work/capacity proofs. Later evidence and native
production integration remain pending. The
[publication record](https://github.com/MGYamada/Qleisli/blob/7bfcd36916199b05d5ab11851d38d53375ccf71e/docs/releases/v0.2.3.md#successful-publication-2026-10-01)
binds the immutable source and package to their validation.

## v0.2.2–v0.2.9: staged verification migration

**User-selected plan, 2026-09-30:** move verification implementation from Rust
to Lean through [eight bounded packets](docs/verification-migration-v0.2.md).
0.2.2's [VM-22 acceptance/boundary freeze and comparison fixtures](tests/fixtures/verification_v022/README.md)
are implemented; 0.2.3–0.2.4 migrate exact arithmetic
and finite evidence; 0.2.5–0.2.6 cover pure/observing raw IR; 0.2.7 closes selected
hierarchy/root obligations; 0.2.8–0.2.9 integrate and audit production dual
checking. Each packet requires actual-definition proofs, independent small-system
comparisons and preserved public compatibility. Current production authority
remains in Rust; Lean-only transfer still requires the v0.5.0 S05 gates.

This revises the former K1/0.3.0 and K2/0.4.0 schedule, not the theorem goals.
The user subsequently resumed the unfinished shared measured-QPE feature track
in 0.2.2. The [current checkpoint](tests/fixtures/authoring_sessions/measured-qpe-v021/checkpoint.md)
records bounded Rust sized source, named provider/instrument proofs, native
checking, execution and measured clients, with scoped R14/H1–H5 evidence.
Remaining validation uses small qubit systems; maximum cases are waived rather
than claimed passed. General source/runtime correspondence and full-profile
migration remain separate. No external schema is enabled;
[VM-26 observing checking](tests/fixtures/verification_v026/README.md), including
original complex instrument refinement, matrix-free CP/TNI/TP and retained
branch-functions, is checked; VM-27–29 integration remains open. The bounded 0.2.2 scope is now
[published and verified](https://github.com/MGYamada/Qleisli/blob/7bfcd36916199b05d5ab11851d38d53375ccf71e/docs/releases/v0.2.2.md#successful-publication-2026-09-30).

## v0.3.0: Qleisli type-system specification

**docs/ cleanup boundary at v0.3.0:** retain the active v0.2.x goals during
their implementation, aggressively delete obsolete documentation now, and
retire all remaining pre-v0.3.0 `docs/` files at the boundary. Write the v0.3.0
documentation from scratch; Reference migration does not gate deletion.
The [cleanup policy](AGENTS.md#docs-cleanup-boundary-at-v030) supersedes earlier
requirements to keep historical pages in the working tree.

**User-selected plan, 2026-09-29:** formulate the Qleisli type system as part
of the v0.3.0 breaking-change release. Specify concrete rules, checking
obligations and public migrations before implementation; the
[current finite contract](docs/type-system.md) remains in force. This target
builds on the migrated checker and requires corresponding rule/proof updates in the
[detailed plan](docs/v0x-roadmap.md#v030-qleisli-type-system-specification).
QLT implementation moves to **v0.4.0 or later**, after the type-system work.
Current release is 0.2.6; the type-system decision remains future work.

## v0.5.0: Qleisli Soundness Theorem and community foundation

**Adopted target, 2026-09-29:** prove the **Qleisli Soundness Theorem** in Lean
for the complete declared production verification profile, then make Lean the
production acceptance authority. The [S05-C1–C5 gates](docs/release-milestones.md#qleisli-soundness-theorem-v050)
require actual-checker soundness, complete coverage, reproducible proof/audit,
artifact binding and independent review. The theorem remains unproved; the
current phase-word theorem is an initial component.

The revised 0.2.2–0.2.9 sequence migrates verification implementation and
selected dual integration; later type-system changes and full-profile proof
composition feed this milestone. During 0.4.x, prepare contributor
onboarding, review responsibilities and maintenance/release procedures.
**From v0.5 onward, expand individual development into a full-scale,
community-oriented open-source project** on that verified foundation.
[The community roadmap](docs/v0x-roadmap.md#community-development-from-v05)
keeps source/optimizer/backend translation validation in K4 from 0.6.0, and
retains M0–M5 and the v1 algorithm gates. Apache-2.0 licensing is already in
place. This selects a future milestone, not a release date or a version bump.

By v1, also prove the
[Physical Realizability Theorem](docs/release-milestones.md#physical-realizability-theorem-v1)
with a substantive Lean backend: derive CPTP semantics as a soundness corollary,
construct an isometric dilation and prove its synthesis over the declared gate
set. K4 must connect the actual emitted circuit to the checked meaning, with
explicit exact/approximate contracts and remaining device assumptions. The
longer-term direction extends Lean implementation beyond the frontend; backend
proofs are required for the intended end-to-end Lean guarantee. This adds
PR-C1–C4 to the v1 gates without changing M0–M5's algorithm dependencies.

The **2026-09-30 amendment** adds the
[Resource Safety Theorem](docs/release-milestones.md#resource-safety-theorem-v1)
as the third pillar toward v1, **to prove** under RS-C1–C5. Establish finite,
statically computed resource bounds and preserve their contracts through
actual lowering, optimization and emission. Develop
[resource semantics](docs/resource-semantics.md) alongside types, meanings and
effects. Current ownership checks, work limits and cost reports do not prove
this target; the trusted/untrusted partition remains unchanged.

<a id="採用したリリース到達条件2026-09-27"></a>

## Implementation stages

| Stage | Current boundary |
| --- | --- |
| 0. Source organization | Specified modules, imports and sealed APIs. |
| 1. Language specification | Finite rules and paper soundness; general implementation adequacy remains open. |
| 2. Typed IR | Rust verification/evidence; staged Lean replacement. |
| 3. Frontend | Finite source and bounded experimental sized source; independent IR checking. |
| 4. Execution | Small ideal reference tests and fresh-shot clients; no hardware guarantee. |
| 5. Backends | Bounded foreign-format adapters; full proved backend remains a v1 target. |

Future QLT, QDB and QCP work is tracked in Issues
[#50](https://github.com/MGYamada/Qleisli/issues/50),
[#51](https://github.com/MGYamada/Qleisli/issues/51) and
[#103](https://github.com/MGYamada/Qleisli/issues/103).
M0–M5, capability/evidence obligations and release gates remain in the
[version-independent roadmap](docs/v0x-roadmap.md) and
[release milestones](docs/release-milestones.md).
Historical development reports are available in Git history and published tags;
actual first sources, counterexamples, proofs and validation fixtures remain intact.

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

The [finite-core v0 specification](docs/language-spec.md) and [normative grammar](docs/syntax-v0.md) align with Stage 0 modules/sealed APIs. Finite-core acceptance/rejection rules are specified. [Conformance](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/specification-status.md) and [formalization](docs/formal-core.md) distinguish specified contracts, implementation, and proof targets. [Inference rules](https://github.com/MGYamada/Qleisli/blob/7bfcd36916199b05d5ab11851d38d53375ccf71e/docs/source-typing-rules.md) and resource rules cover all syntax, but correspondence to all accepted paths and general proofs remain open.

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

Represent ownership tokens, logical wire IDs, effects, phases, and checkable constructors in Rust. The verifier rechecks injectivity, gate types, protected-region/target conflicts, nonuse of measurement-consumed handles, and structured `ComputeUseUncompute` zero-return conditions. This does not implement general source borrowing. Do not expose a standalone `Release0`. Document each constructor's ideal semantics and the trusted primitive boundary. The [prototype](docs/ir-prototype.md) records implemented checks and unachieved guarantees; the [finite-IR paper proof](https://github.com/MGYamada/Qleisli/blob/7bfcd36916199b05d5ab11851d38d53375ccf71e/docs/finite-core-proof.md) records constructor semantics and implementation obligations.

**Completion:** accept valid small IR and reject intentionally constructed duplication, implicit discard, invalid release, and effect violations. Apply the same verifier to handwritten/external IR regardless of origin, and show that accepted IR meaning satisfies Stage 1 theorem premises.

<a id="3-qli-フロントエンド"></a>

## 3. `.qli` frontend

Implement parsing, module resolution, and type/effect/ownership checking under Stage 0 file rules, producing verified IR.

Within the finite-core v0 profile, all-declaration name resolution, call-cycle rejection, type/effect/linear-ownership checking, and IR generation are implemented. Ordinary calls are expanded. The original two-argument `with_computed` path restricts/rechecks expanded bodies to identity and Z/T sequences; the later explicit logical-contract path is specified in [SC](docs/finite-contracts.md). Classical branches merge results and surrounding live resources through φ. Public entry points are `check_project`, `compile_project`, and `qleisli check/run`; all generated IR passes independent `verify`. Static adjoints/control/repetition lower to ApplyUnitary in the finite implementation. The [frontend reference](docs/frontend-v0.md) records rules, diagnostic codes, limits, and unsupported features.

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
