# Release milestones

Adopted gates; general Soundness, Physical Realizability, Resource Safety and v1 remain unmet. Product versions, specification stages and bounded components are independent. [Status](current-status.md) records evidence. VM-22–26 are checked components; VM-27–29 remain open under the [migration](verification-migration-v0.2.md). Rust retains authority.

## v0.3.0 type-system specification and later QLT

Specify types, public migration and corresponding checker/proof updates at v0.3.0. Concrete changes require decisions. QLT waits until v0.4.0 or later. Published finite/shared-QPE results do not complete the [continuation](v0.2.2-plan.md).

<a id="qleisli-soundness-theorem-v050"></a>
## Qleisli Soundness Theorem (v0.5.0)

To prove: verify(p,C,π)=true implies ResourceSafe(p), EffectSound(p,C) and [[p]] ⊨ C for the **actual complete production profile**, including flat/QIRF and enabled hierarchy paths. C is independently requested and fixes entry, encodings, axes, exact phase, full instruments, clean return and arbitrary references. ResourceSafe here is ownership, not quantitative RS. Source/backend preservation, native compilation, approximate execution, algorithm success and hardware remain separate.

| Gate | Required evidence |
| --- | --- |
| S05-C1 | Publish every enabled rule/path, capacities and entry premises; retain positive corpus/algorithm coverage. Reject unsupported paths explicitly; removing support needs versioned migration. An always-rejecting or phase-word-only checker fails. |
| S05-C2 | Compose actual resource/effect, exact arithmetic, contract, hierarchy and instrument proofs for every enabled rule. No required Rust-checker/evidence-producer correctness premise remains. |
| S05-C3 | Bind reviewed theorem to released executable definitions; reproduce builds, declaration/axiom audits and replay. Runtime Mathlib-free; interpretation separate. State compiler/runtime/transport assumptions. |
| S05-C4 | K3 reconstructs evidence against independent requests and binds decisions to executed/emitted artifacts. Differential/adversarial/platform checks pass; kernel/transport failure rejects without Rust fallback. |
| S05-C5 | Publish explanations, coverage/assumptions and reproduction; independent review resolves blockers. Prepare contributor setup, bounded Issues, proof/code review, maintainer, release and security-reporting procedures for community growth. |

<a id="physical-realizability-theorem-v1"></a>
## Physical Realizability Theorem (v1)

Derive complete classical–quantum CPTP semantics, construct isometric dilation and synthesize actual emitted circuits with a substantive Lean backend. Retain outcomes, residual/reference states, pure phase, workspace and environmental discard. Individual outcomes need CP/TNI. Unitarity alone grants neither same-wire synthesis nor inverse/control access.

### Synthesis workspace contract

Clean workspace requires C E0=E0 U for every input/reference including phase; dirty/borrowed workspace needs arbitrary-state preservation. Count preparation, return, routing and peak space. Same-wire Clifford+T+Toffoli determinant obstructions for F8 (det=i, three wires) and c3x (det=-1, four wires) remain in [tests](../tests/static_semantics.rs). Existence is not an implemented backend/cost bound; [#120](https://github.com/MGYamada/Qleisli/issues/120) targets v0.3 specification, [#132](https://github.com/MGYamada/Qleisli/issues/132) bounded v0.4 synthesis.

| Gate | Required evidence |
| --- | --- |
| PR-C1 | Complete-profile CPTP corollary and constructive dilation, with entry/encoding/outcome/reference premises. |
| PR-C2 | Declared target gates/preparation/readout and proved dilation synthesis. Exact/approximate scope explicit; certified reference-sensitive, compositional error metric. Universality is not exact synthesis. |
| PR-C3 | Actual Lean lowering, optimization, layout and emission correspond to accepted IR; bind every input/output. Source translation validation remains separate. |
| PR-C4 | Profile, proofs/coverage/assumptions, reproducible audits and independent review include all three v1 algorithm families. Unsupported targets reject; compiler/runtime/transport/device assumptions explicit. |

<a id="resource-safety-theorem-v1"></a>
## Resource Safety Theorem (v1)

Actual static analysis/checking must issue finite worst-case bounds for every admissible execution **and prefix**, preserved by compilation under declared cost translations. [Resource semantics](resource-semantics.md); budgets, ownership, estimates and QLT tests are insufficient.

| Gate | Required evidence |
| --- | --- |
| RS-C1 | Versioned finite domain/units/order, input/size/target premises and cost/composition for every construct, frames, scratch, repetitions, branches, initialization, routing and measurement. |
| RS-C2 | Actual executable analysis/check proof for every admitted size/input/execution. Unsupported, inconclusive, overflow and limit results issue no evidence. |
| RS-C3 | Prove or independently validate actual lowering/optimization/synthesis/layout/emission bounds; bind artifacts/models and explicit translations. Exceeding the contract requires revised checking or rejection. |
| RS-C4 | Finite termination/prefix/measurement/branch/bounded-retry coverage; distinguish worst/expected and execution/compiler/search/simulator/host costs. State exclusions/device assumptions; no hidden unbounded oracle/retry. |
| RS-C5 | Publish profile, actual-definition proofs, coverage/assumptions, reproducible audits and independent review for three v1 families. Test undercounts, stale evidence, cost-changing passes and model mismatches. |

## v0.1 minimum: semantic contracts

Bounded V01-C1–C6 and B019 are completed historical foundations, not current release gates or general Rust/source proofs. Preserve exact encoding/whole-space equations, phase/entry/reference cleanup, body/dependency binding, unchanged-client substitution and negative evidence. [Contracts](finite-contracts.md).
<a id="v019-maintenance-boundary"></a>

<a id="v1-north-star-textbook-algorithm-structure"></a>
## v1 acceptance target: textbook algorithm structure

Make mathematical thought and real source coincide. Shor/QPE/Grover must each meet every gate below plus PR/RS. Shor reuses QPE, samples and validates periods/factors with bounded retries: r>0 and a^r=1 mod N alone prove no minimal order. Factor extraction needs even r, nontrivial a^(r/2) and GCDs. Exhaustive distributions are not samples. [Algorithm contracts](algorithm-structure-goal.md#release-targets-and-criteria-for-algorithm-structure).

| Gate | Required evidence |
| --- | --- |
| V1-C1 | Compiling/running real source with visible mathematical stages; no pseudocode, monolithic renaming or unimplemented black boxes. |
| V1-C2 | Same definitions across sizes/precision/predicates/operations/inputs; fixed QPE2/3 and N=15 alone fail. |
| V1-C3 | Checked meaning through component/IR boundaries and unchanged-client implementation substitution; access/instrument/accuracy contracts explicit. |
| V1-C4 | Independent phase/reference-sensitive expectations and failure/retry tests; samples alone prove no order, candidates no factors, circuit validity no algorithm correctness. |
| V1-C5 | Stable algorithm source across layouts/decompositions; separate generation/execution/oracle/classical costs and publish bounds/proof status. No precomputed answers or whole-space truth tables replacing general construction. |

<a id="pre-v020-imaginary-v1-code"></a>
## Prerequisite before v0.2.0: imaginary Qleisli 1.0 code

Six [drafts](imaginary-v1/README.md) satisfy the initial design prerequisite only. Preserve their capabilities, meaning, phase, cleanup, accuracy/failure and open questions. They are uncompiled proposals. Work program-first, retain finite contracts, establish symbolic meanings/evidence-bound hierarchy before sizes and synthesize predicates/arithmetic. Every abstraction needs a removed obligation, replacement evidence and independent checker; forms require grammar/types/effects/semantics/IR/limits/migration/validation.
