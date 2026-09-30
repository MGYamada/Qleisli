# Qleisli milestones toward v1

Current version and latest published release: [**0.2.2**](releases/v0.2.2.md#successful-publication-2026-09-30).
The [current plan](v0.2.2-plan.md) and [VM-22–VM-29](verification-migration-v0.2.md)
replace old release work plans. Product versions follow [compatibility](versioning.md):
compatible changes use PATCH in 0.y.z, public breaks use MINOR. Milestone IDs
express dependencies, not reserved version numbers.

## v0.3.0: Qleisli type-system specification

The user selected v0.3.0 for the breaking type-system specification. Define type
formation/equality, moves/borrowing, effects/capabilities, sizes/conversions,
source/IR checking obligations and public migration. Follow Rust for unresolved
type/ownership choices while retaining quantum linearity, explicit discard and
proved clean release. The [current type contract](type-system.md) remains in force.

Resolve the [coefficient/phase-domain split](coefficient-domains.md#review-inventory-and-v03-decision)
with explicit arithmetic, equality, interpretation, capacity and binding rules.
A flat triple return for `toffoli` requires migration from its existing nested
return ([#15](https://github.com/MGYamada/Qleisli/issues/15)). Concrete successor
rules and syntax remain undecided. QLT implementation is deferred until v0.4.0
or later ([#50](https://github.com/MGYamada/Qleisli/issues/50)); its [desired source/faults](../tests/fixtures/qlt_design/README.md)
remain preserved. QDB is tracked in [#51](https://github.com/MGYamada/Qleisli/issues/51).
Neither planned tool is an implemented language API.

### Documentation discipline for v0.3.0

**docs/ cleanup boundary at v0.3.0 — user decision, 2026-09-30.**
Keep the active v0.2.x goals and VM-22–VM-29 migration plan during their
implementation. Aggressively delete obsolete plans and historical reports now.
By v0.3.0, retire every remaining pre-v0.3.0 file under `docs/` and write that
release's documentation from scratch. This supersedes the content-preserving
migration rule in [#48](https://github.com/MGYamada/Qleisli/issues/48).

The enduring direction is the three theorems and six v1 algorithm goals in
[README](../README.md#project-goals). Build the new documentation from adopted
v0.3.0 decisions, actual code, proofs and executable examples; do not archive or
transplant the old tree. Historical lookup uses Git history and published tags.
Source attempts, counterexamples, validation artifacts, proof code and required
notices outside `docs/` remain intact.

Deletion precedes the new Reference. The rewrite must give each rule one home,
state its implemented/tested/proved scope and pass link/example checks. This
cleanup changes no present language acceptance or theorem status.

## Community development from v0.5

| Target | Required result |
| --- | --- |
| 0.2.2–0.2.9 | Acceptance inventory, exact/finite evidence, pure/observing raw IR, hierarchy and explicitly selected production dual checking under VM-22–VM-29. Rust retains authority. |
| 0.3.x | Adopt, migrate and reprove changed type rules at the breaking boundary. |
| 0.4.x | Prepare S05 proof coverage, contributor setup, bounded issues, review/maintenance responsibilities and independent review; evaluate QLT separately. |
| 0.5.0 | Prove the actual production **Qleisli Soundness Theorem**, complete [S05-C1–C5](release-milestones.md#qleisli-soundness-theorem-v050), then transfer authority to Lean. |
| 0.5.x onward | Begin mathlib-style stdlib growth under [STDLIB.md](../STDLIB.md) and expand community participation. From 0.6, K4 develops translation validation and a proved Lean backend. |
| 1.0 | Meet [V1-C1–C5](release-milestones.md#v1-acceptance-target-textbook-algorithm-structure), [PR-C1–C4](release-milestones.md#physical-realizability-theorem-v1) and [RS-C1–C5](release-milestones.md#resource-safety-theorem-v1), with Physical Realizability and Resource Safety proofs and stabilized contracts. |

These are adopted targets, not completed guarantees, fixed dates or claims of
existing external maintainers. The supported production checker and complete
declared profile determine S05 scope; phase-word/component proofs are precursors.
General source/backend preservation follows K4. CPTP semantics is a soundness
corollary; realizability must construct/synthesize a dilation over a declared gate
set. Resource Safety covers actual execution under declared cost models, beyond
linear ownership and checker budgets. Apache-2.0 and the three-source corpus
policy continue to apply.

## Active milestones and dependencies

| Milestone | Scope | Acceptance boundary |
| --- | --- | --- |
| M0: choose the path | [Decision dossier](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/decisions/2026-09-27-v1-path.md), capability/meaning/angle policy and joint IR/evidence design. | Scope and bounded-kernel feasibility selected; a no-go is not completion. |
| M1: fixed-width composition/interfaces | Checked static operation parameters, conjugation, bounded basis meanings, finite interchange, diagnostics and host trials. | Distinct checked implementations compose; unavailable access and wrong/stale phase/body evidence reject. Existing finite dense bounds remain. |
| M2: scalable checking/QPE | Hierarchical IR, static sizes, dyadic phases, shared source across widths and operations. | R14/H1–H5, exact entry/cleanup and phase/reference-sensitive full QPE instrument; production integration remains open. |
| M3: Grover | M2 plus reversible predicate synthesis and fresh host trials. | Preparation/oracle/reflection/iteration and candidate/retry results meet V1-C1–C5 without full-space truth-table synthesis. |
| M4: Shor | M2 plus reversible whole-space modular arithmetic; may proceed alongside M3. | Shared QPE, clean scratch, controlled powers, samples, period/factor checks and explicit retries meet V1-C1–C5. |
| M5: costs/stability | M3/M4 and all executable v1 evidence. | Separate generation/checking/execution/oracle/classical costs, public migrations and stable contracts. |

Walk and QSVT remain stress tests, not extra executable v1 gates. [Bounded connections](connections-v021.md)
are shipped finite slices, without a general adaptive or hierarchical guarantee.
Maintain the [verifier/kernel-first proof order](formal-core.md#4-theorem-status-and-proof-work),
axiom/runtime-policy audits and independent checking throughout [pipeline migration](lean-kernel-migration.md#pipeline-migration-with-a-stable-ir-verification-boundary).
Search/evidence producers stay untrusted; correctness-critical checkers belong
in Lean, including the planned LeafRealizer role. Moving code does not prove it.

### Cross-release prerequisites

- **R14:** compose actual meanings, encodings and evidence without global dense
  matrices before size generalization. Compact proof over expanded IR is insufficient.
- **R02/R04 and H1–H5:** bind shared calls/repeats, interfaces, requested roots and
  checked transformations to the actual hierarchical artifact and pinned proofs.
- **R06/R09:** synthesize reversible predicates/arithmetic over a declared fragment,
  including outside-residue behavior and zeroed scratch, without full truth tables.

The [detailed QPE prerequisites](imaginary-v1/requirements.md#scaling-prerequisite-for-r14)
and [hierarchy gates](hierarchical-ir-spec.md#migration-and-implementation-gates)
remain authoritative. Validation follows the [small-system scope](v0.2.2-plan.md#remaining-validation-scope-small-qubit-systems-2026-09-30).

## Responsibilities beyond ownership

Every abstraction must name the author obligation it removes, the replacing
evidence and its independent checker. Mathematical unitarity does not provide
an inverse or controlled implementation; preserve global phase under control.
Large repeated powers are not automatically unit-cost access. An initializer's
isometry is not a freely usable inverse.

For pure cleanup, `F : H_in → H_data ⊗ H_aux` must factor as
`F = (I_data ⊗ |0_aux⟩) V`, with isometry `V : H_in → H_data`.
Under an isometric entry encoding `E_in`, instead prove
`F E_in = (I_data ⊗ |0_aux⟩) V` and establish the entry premise separately.
Both extend by identity to every reference. Ownership, scope duration, typestate
names and approximately-zero measurements do not establish these equations.
General entanglement-region inference and dependent/graded types remain research.

<a id="v019-acceptance-boundary"></a>

## Finite maintenance checkpoint (legacy B019)

The completed finite foundation is recorded in the [B019 review](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/reviews/b019-completion.md)
and [0.1.9 release](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/releases/v0.1.9.md). Preserve original failed cases and executed
evidence; the old maintenance schedule is no longer active.

## Legacy ID mapping

| IDs | Meaning retained |
| --- | --- |
| B019 | Completed finite maintenance checkpoint; not a prerequisite to ship patches in numerical order. |
| G020-1 / G020-2 / G020-3 | Extension specification / implementation / validation, with separate fixed-width and sized profiles. |
| G013-S0–S2 / G013-S3 | Research artifacts / production integration obligation. |
| X1–X6 / CD-1–CD-4 | Finite interfaces and [program-first packets](code-driven-development.md). |
| K0–K4 / VM-22–VM-29 | Lean migration axis / current eight verification packets. |
| M0–M5 / A/L / SPEC | Dependency milestones / work areas / historical specification labels; no mechanical renumbering. |
| R01–R14 / V01-C / V1-C | Requirements and finite/v1 acceptance identities. |

Actual adoption and publication evidence remains in the [dossier](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/decisions/2026-09-27-v1-path.md)
and [release records](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/releases/v0.2.1.md). A version selection does not publish.
