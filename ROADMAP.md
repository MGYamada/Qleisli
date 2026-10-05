<a id="qleisli-ロードマップ"></a>

# Qleisli roadmap

Status: the design principles are fixed. Goal 1: a quantum language for the AI era and goal 2: structuring quantum algorithms remain in development. Layer 3: a standard algorithm vocabulary has a v1 contract ledger and finite static-operation implementations. Stage 0 is complete as documentation; Stage 1 has a normative finite-core v0 specification but unfinished proofs; Stages 2–4 are partially implemented. Alongside minimal examples such as Bell, shared components build finite Grover, BV, bit-flip correction, QPE, and N=15 order-finding examples. Completion is judged against documented criteria and evidence. The frontend documentation distinguishes executed `.qli` from unimplemented syntax proposals.

This is the English development plan. Current targets and implementation boundaries do not adopt future syntax or imply completed proofs. The verification migration plan and fixture records distinguish bounded checks from pending guarantees; source validation, tagging and publication remain separate.

## Selected v0.3.0-alpha: prerelease preparation and documentation cleanup

Selected 2026-10-04: synchronize the product versions to `0.3.0-alpha` and
complete the planned documentation cleanup. This is an unpublished prerelease
development version; the latest published release is 0.2.9. Its implementation
and validation records remain the baseline,
including identical checked Codex/Claude rules, TRUSTBOUNDARY.md and nine small
translations from frozen corpus sources (87 total).
Local validation and publication remain separate. Selected source/raw/foreign/
Python paths now reach Lean, and sized hierarchy execution no longer repeats
Rust finite-leaf acceptance. Actual native acceptance also implies independent
classical scope safety. After the bounded timing and acceptance comparisons,
the user approved [Decision #276](https://github.com/MGYamada/Qleisli/issues/276):
a one-time breaking v0.2.9 migration to a single Lean production verifier.
The [adopted order and cutover criteria](https://github.com/MGYamada/Qleisli/issues/276)
separate implementation unification from the unfinished v0.5.0 Soundness
milestone. Production callers now use native acceptance, including retained
function evidence, encoded contracts and finite leaves. The Rust verifier,
`VerifiedProgram` and `interchange::dual` have been removed. All release gates,
platform distribution validation and full-profile proofs remain explicit;
implementation unification alone is not a theorem or a published release.

The earlier VM-22–29 packet results remain beside their fixtures. The adopted
v0.2.9 exception supersedes the former Rust-authoritative transition schedule.
The deleted migration-plan document is not an active specification. Source and
runtime preservation and full Soundness remain separate obligations; no external
schema has been enabled.

## v0.3.0: Qleisli type-system specification

The [Constitution and governance adoption](docs/src/design/ratification.md)
took effect on 2026-10-04 (Asia/Tokyo), including the initial Guardian appointment.
Work now proceeds through the [authority hierarchy](docs/src/reference/authority.md).
The initial QS/PR/RS interpretations were separately adopted as three binding
pending obligations. Two narrower QLV1 ownership and classical-scope guarantees
were subsequently admitted after proof review and explicit human approval; the
[guarantee record](docs/src/design/initial-guarantees.md) states their exact
scope and assumptions. The three broader obligations remain pending. The
[release-readiness umbrella](https://github.com/MGYamada/Qleisli/issues/142)
tracks the 110 selected issues, including the exactness interpretation in #311
and ordinary-body effect inference in #315.
Edition 2026 identifies the constitutional
regime and remains unchanged by the syntax, type-system and CLI migration.

**Documentation cleanup completed for v0.3.0-alpha:** `docs/` retains the entire
`imaginary-v1/` tree and
[lean-backend-plan-v0.3.md](docs/src/lean-backend-plan-v0.3.md). The temporary
`docs-old/` tree is deleted, with no redirects or replacement copies of retired
prose. Executable source, proofs, counterexamples, validation artifacts and
notices remain in their source/fixture locations. Write new documentation in
`docs/` from adopted decisions, code, proofs and executable examples; consult
Git history for retired documents. The
[documentation policy](AGENTS.md#documentation-after-the-v030-cleanup) governs new work.

**User-selected plan, 2026-09-29:** formulate the Qleisli type system as part
of the v0.3.0 breaking-change release. Specify concrete rules, checking
obligations and public migrations before implementation; the
current finite contract remains in force. This target
builds on the migrated checker and requires corresponding rule/proof updates
before adoption.
QLT implementation moves to **v0.4.0 or later**, after the type-system work.
Current development version is `0.3.0-alpha`; selecting it and completing the
documentation cleanup do not complete the type-system specification or its
implementation/proof gates.

## v0.3.1–v0.3.9: proposed accelerated Lean backend expansion

The [backend plan](docs/src/lean-backend-plan-v0.3.md) targets earlier retirement of
Rust transformations, hierarchy construction, target lowering, emitters and
duplicate execution dispatch. Each stage requires a checked input/output
relation, independent bounded validation and an explicit Rust deletion list;
full Soundness remains the separate v0.5.0 milestone. The small acceptance
kernel policy stays fixed while the Mathlib-free backend package grows.
This advances the proposed backend portion of #273/#132; update their staged
scope before implementation. It does not silently adopt new source syntax,
move QLT/QDB/QCP earlier or permit PATCH API breaks.

## v0.5.0: Qleisli Soundness Theorem and community foundation

**Adopted target, 2026-09-29:** prove the **Qleisli Soundness Theorem** in Lean
for the complete declared production verification profile. The implementation
authority transfer is advanced to v0.2.9 under Decision #276. The S05-C1–C5 gates
require actual-checker soundness, complete coverage, reproducible proof/audit,
artifact binding and independent review. The theorem remains unproved; the
current phase-word theorem is an initial component.

The revised 0.2.2–0.2.9 sequence migrates verification implementation and
native integration; later type-system changes and full-profile proof
composition feed this milestone. During 0.4.x, prepare contributor
onboarding, review responsibilities and maintenance/release procedures.
**From v0.5 onward, expand individual development into a full-scale,
community-oriented open-source project** on that verified foundation.
Bounded backend translation validation is proposed for v0.3.1–v0.3.9 under the
plan above, advancing that part of the former blanket v0.6.0 schedule. Broader
source/optimizer preservation remains a target from v0.6.0. Apache-2.0 licensing is already in
place. This selects a future milestone, not a release date or a version bump.

By v1, also prove the
Physical Realizability Theorem
with a substantive Lean backend: derive CPTP semantics as a soundness corollary,
construct an isometric dilation and prove its synthesis over the declared gate
set. K4 must connect the actual emitted circuit to the checked meaning, with
explicit exact/approximate contracts and remaining device assumptions. The
longer-term direction extends Lean implementation beyond the frontend; backend
proofs are required for the intended end-to-end Lean guarantee. This adds
PR-C1–C4 to the v1 gates without changing M0–M5's algorithm dependencies.

The **2026-09-30 amendment** adds the
Resource Safety Theorem
as the third pillar toward v1, **to prove** under RS-C1–C5. Establish finite,
statically computed resource bounds and preserve their contracts through
actual lowering, optimization and emission. Develop
resource semantics alongside types, meanings and
effects. Current ownership checks, work limits and cost reports do not prove
this target; the trusted/untrusted partition remains unchanged.

<a id="採用したリリース到達条件2026-09-27"></a>

## Implementation stages

| Stage | Current boundary |
| --- | --- |
| 0. Source organization | Specified modules, imports and sealed APIs. |
| 1. Language specification | Finite rules and paper soundness; general implementation adequacy remains open. |
| 2. Typed IR | Rust proposals; native Lean acceptance for IR and evidence. |
| 3. Frontend | Finite source and bounded experimental sized source; independent IR checking. |
| 4. Execution | Small ideal reference tests and fresh-shot clients; no hardware guarantee. |
| 5. Backends | Bounded foreign-format adapters; full proved backend remains a v1 target. |

Future QLT, QDB and QCP work is tracked in Issues
[#50](https://github.com/MGYamada/Qleisli/issues/50),
[#51](https://github.com/MGYamada/Qleisli/issues/51) and
[#103](https://github.com/MGYamada/Qleisli/issues/103).
Capabilities and evidence must be specified and reviewed before future syntax
or library APIs are adopted.
Historical development reports are available in Git history and published tags;
actual first sources, counterexamples, proofs and validation fixtures remain intact.

## 0. Source and standard-library organization

The source organization described in [README.md](README.md), [STDLIB.md](STDLIB.md)
and the executable examples uses:

- The role/encoding of `.qli`, one-file/one-module correspondence, top-level declarations, visibility, imports, and entry functions.
- Minimal standard-library modules and automatically available names; boundaries between ordinary `.qli`, sealed operations, and language forms.
- Local module resolution, cycles, and initial treatment of external dependencies and host I/O.
- Multifile Bell preparation/measurement and phase-oracle design examples, identifying operations with quantum premises.

**Completion:** consistent documented choices, with examples readable under the same module rules. Grammar/type-checker implementation is not a Stage 0 condition.

Multifile Bell/phase-oracle examples exercise public declarations and root-relative
`use` rules. Their executable acceptance tests remain the current conformance evidence.

<a id="1-言語仕様"></a>

## 1. Language specification

The finite-core v0 specification and normative grammar align with Stage 0 modules/sealed APIs. Finite-core acceptance/rejection rules are specified. Conformance and formalization distinguish specified contracts, implementation, and proof targets. Inference rules and resource rules cover all syntax, but correspondence to all accepted paths and general proofs remain open.

- Formalize effectful transformations of classical values and quantum resources from the design philosophy using input/output contexts and composition. Investigate the precise structure of Kleisli-inspired composition and its relationship/limits with free-vector-space `bind`.
- Specify grammar and name resolution for all examples.
- Give inferable type/effect rules for `basis`, `iso`, `unitary`, and `observe`, and ownership rules for classical branches and `qif`.
- Specify `split/join`, restricted `with_computed` protection, measurement's termination of logical ownership, and auxiliary evidence. General borrowing syntax/signatures belong to a later specification.
- Address the central open problem: separate ownership contexts from global-state correlations and specify function-boundary checks for local operations, partial measurement, discard, and pure release. Initial support does not require general entanglement inference.
- Specify pure isometries, measurement-bearing instruments, and translation to typed IR.
- State finite-core soundness targets as theorems. Prove resource preservation, complete positivity for each classical outcome, and summed trace preservation under sealed-primitive and certified-release premises.
- Check accepted/rejected examples and finite Bell/phase-oracle/feedback distributions, including one-sided measurement/discard and unsupported pure release after splitting a Bell pair.

**Completion:** Stage 0 examples can be typed or rejected with unambiguous effects and IR translation. Finite-core resource safety and instrument soundness have theorem statements and proofs. Ownership separation must not imply state separation; partial Bell measurement/discard is interpreted globally, and pure release without evidence is rejected. Arbitrary free-vector-space `bind` is not an execution API.

<a id="2-型付き-ir"></a>

## 2. Typed IR

Represent ownership tokens, logical wire IDs, effects, phases, and checkable constructors in Rust. The verifier rechecks injectivity, gate types, protected-region/target conflicts, nonuse of measurement-consumed handles, and structured `ComputeUseUncompute` zero-return conditions. This does not implement general source borrowing. Do not expose a standalone `Release0`. Document each constructor's ideal semantics and the trusted primitive boundary. The prototype records implemented checks and unachieved guarantees; the finite-IR paper proof records constructor semantics and implementation obligations.

**Completion:** accept valid small IR and reject intentionally constructed duplication, implicit discard, invalid release, and effect violations. Apply the same verifier to handwritten/external IR regardless of origin, and show that accepted IR meaning satisfies Stage 1 theorem premises.

<a id="3-qli-フロントエンド"></a>

## 3. `.qli` frontend

Implement parsing, module resolution, and type/effect/ownership checking under Stage 0 file rules, producing verified IR.

Within the finite-core v0 profile, all-declaration name resolution, call-cycle rejection, type/effect/linear-ownership checking, and IR generation are implemented. Ordinary calls are expanded. The original two-argument `with_computed` path restricts/rechecks expanded bodies to identity and Z/T sequences; the later explicit logical-contract path is specified in SC. Classical branches merge results and surrounding live resources through φ. Public entry points are `check_project`, `compile_project`, and `qleisli check/run`; all generated IR obtains independent native Lean acceptance. Static adjoints/control/repetition lower to ApplyUnitary in the finite implementation. The frontend reference records rules, diagnostic codes, limits, and unsupported features.

Review work limited internal values/types to 4,096 nodes and depth 64, charging copied trees to the work budget. Ordinary-call argument errors point to caller actual arguments or the call expression. Regressions include reproducers and accepted in-limit cases.

**Completion:** automatically classify Stage 1 accepted/rejected examples, with file locations and machine-readable results. Pass frontend output through Stage 2 IR verification without varying checks by code origin.

<a id="4-参照実行系"></a>

## 4. Reference execution

Execute instruments including measurement/reset/discard using finite-dimensional vectors and density operators or an equivalent mixed-state representation. The Rust prototype runs verified closed IR as ensembles of unnormalized pure states. Bell, phase-oracle, and feedback projects compile from `.qli` and match expected distributions; finite IR tests for partial discard/reset are retained. Values are approximate `f64`; exact zero probabilities and an independent literal execution check of auxiliary wires remain open.

The finite algorithm examples check all two-bit Grover targets/iteration counts, all BV hidden strings, reference correlations in bit-flip correction, and parity-measurement coherence. Their success conditions are separate from type/resource safety.

**Completion:** execute compiled closed `.qli` programs and match analytically known distributions, distinguishing finite checks from general soundness proofs.

<a id="5-外部バックエンド"></a>

## 5. External backends

Explicitly check target-format/device capabilities. Emit output only when fresh logical-wire allocation on measured physical elements and dynamic feedback can be implemented correctly.

**Completion:** reject unsupported features clearly and compare supported program meaning with reference execution.

<a id="その先の個別仕様"></a>

## Further individual specifications

Protocol properties such as state preservation in teleportation, algorithmic correctness/success probability, and noisy hardware/calibration are separate specification and proof tasks. They are not consequences of the basic resource-safety and quantum-soundness theorem.
