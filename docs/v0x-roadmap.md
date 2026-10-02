# Milestones toward v1

Selected development **0.2.6**; latest published [0.2.5](https://github.com/MGYamada/Qleisli/blob/b316a5065527c84f3dbcb059750637e2b14b0965/docs/releases/v0.2.5.md#successful-publication-2026-10-02).
[Continuation](v0.2.2-plan.md) and [VM-22–29](verification-migration-v0.2.md) replace
old work plans. Milestones express dependencies, not reserved versions: compatible
0.y.z changes use PATCH, public breaks MINOR under [versioning](versioning.md).

## v0.3.0: Qleisli type-system specification

Specify formation/equality, moves/borrowing, effects/capabilities, sizes/conversions,
source/IR obligations and public migration. Follow Rust for unresolved discipline,
retaining quantum linearity, explicit discard and proved cleanup; [current types](type-system.md)
remain authoritative. Resolve [domains](coefficient-domains.md) with bound arithmetic/
equality/interpretation/capacity. Flat Toffoli return needs explicit nested-return
migration ([#15](https://github.com/MGYamada/Qleisli/issues/15)); concrete successor
rules remain undecided. [QLT #50](https://github.com/MGYamada/Qleisli/issues/50) waits
until v0.4+; [QDB #51](https://github.com/MGYamada/Qleisli/issues/51) remains planned.
Preserve [QLT sources/faults](../tests/fixtures/qlt_design/README.md).

### Documentation discipline for v0.3.0

User decision 2026-09-30: retire obsolete/completed/history now; keep active v0.2.x
goals and migration usable. At v0.3 retire all remaining legacy docs and write from
adopted decisions, actual code/proofs/examples. No archive, old-tree transplant or
redirect stubs; history uses Git/tags. [#48](https://github.com/MGYamada/Qleisli/issues/48)
tracks cleanup. Preserve executable source, attempts, faults, evidence/proofs/notices
outside docs. Give every new rule one home with implemented/tested/proved scope and
link/example CI. Cleanup changes no semantics or theorem status.

## Community development from v0.5

0.2.2–0.2.9 implements exact/finite/raw/hierarchy and selected dual checking; Rust
retains authority. v0.3 adopts/migrates/reproves type breaks; v0.4 prepares coverage,
contributor/reviewer/maintenance roles and independent S05 review. v0.5 proves full
production [Soundness S05-C1–C5](release-milestones.md#qleisli-soundness-theorem-v050),
then transfers acceptance and starts mathlib-style library/community growth. K4 from
v0.6 develops substantive proved Lean translations/backend. v1 additionally requires
[Realizability/Resource Safety](release-milestones.md) and V1-C1–C5 with stabilized
contracts. These are targets, not dates/completed guarantees/existing maintainers.

## Active milestones and dependencies

| ID | Scope and gate |
| --- | --- |
| M0 | Select joint meaning/access/angle/IR/evidence path with bounded feasibility; no-go is not completion. |
| M1 | Fixed-width static operations, conjugation, basis meanings, finite interchange/diagnostics/trials; distinct implementations compose, wrong/stale meaning/access rejects within finite bounds. |
| M2 | Shared sizes/hierarchy/dyadic QPE; R14/H1–H5 and full phase/reference instrument/entry/cleanup/production binding, without global dense matrices. |
| M3 | Grover: reversible predicate synthesis, preparation/oracle/reflection/iterations and fresh validated trials, without full-space truth tables. |
| M4 | Shor, alongside M3: full-space reversible modular arithmetic/clean scratch, shared QPE/powers, samples, validated periods/factors/retries. |
| M5 | Separate generation/checking/execution/oracle/classical costs, all v1 evidence and stable migrated contracts. |

Walk/QSVT stress-test designs; six initial drafts do not add executable v1 gates.
[R14](imaginary-v1/requirements.md#scaling-prerequisite-for-r14), R02/R04 and H1–H5
bind actual shared calls/interfaces/roots/transforms; R06/R09 require reversible
predicate/arithmetic synthesis. [Small systems](v0.2.2-plan.md#remaining-validation-scope-small-qubit-systems-2026-09-30)
remain the validation scope. Proof order is independent verifier/kernel before general
frontend adequacy, with source/compiled audits at every migration boundary.

## Responsibilities beyond ownership

Every abstraction names the removed author obligation and replacing independent
checker. Mathematical unitarity grants no inverse/control access or cheap power.
Initializer isometry supplies no unrestricted inverse. Pure cleanup requires
F=(I_data⊗|0_aux>)V with V isometric, or F E_in=(I_data⊗|0_aux>)V with separately
established entry. Both preserve arbitrary references; lifetimes, typestate and
approximate zeros do not prove them. Broader entanglement/dependent types are research.
Legacy B019/G020/G013/X/CD/K/VM/M/A/L/SPEC/R/V labels retain their original identities;
completed schedules live in Git, never mechanically renumbered. Apache-2.0, approved
corpus sources and independent specification review persist.

<a id="legacy-id-mapping"></a>
