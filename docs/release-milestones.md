# Qleisli release milestones and north star

Authoritative adopted acceptance gates. The declared finite v0.1 profile is implemented and checked; general Soundness, Physical Realizability, Resource Safety and v1 remain unmet. Specification/stage/ledger/product numbers are independent. [Current status](current-status.md) and immutable fixture evidence record actual results.

## 0.2.0 foundation and 0.2.1 shared-QPE continuation

The published finite foundation and bounded shared-QPE checkpoint are historical results. The broader [continuation](v0.2.2-plan.md) retains hierarchy/source/instrument/execution/R14/H1–H5 obligations; publication did not complete them.

## v0.3.0 type-system specification and later QLT

v0.3.0 specifies the type system and any explicitly adopted public migrations; concrete changes remain to be fixed. Adapt migrated checks/proofs to adopted rules. QLT implementation remains v0.4.0 or later and adds no automatic S05/PR gate.

## 0.2.2–0.2.9 verification implementation targets

[VM-22–29](verification-migration-v0.2.md) cover inventory, exact/finite, pure/observing raw IR, hierarchy and opt-in dual integration. VM-22–26 are checked for their declared profiles; VM-27–29 remain open. Complete implementation/dual checking in 0.2.9 does not transfer Lean-only authority.

## Qleisli Soundness Theorem (v0.5.0)

To prove at v0.5.0 over the actual complete production verification profile, including published flat/QIRF compatibility and enabled hierarchy paths. The independent contract fixes meanings and explicit entry premises. Satisfaction covers exact-phase pure maps or complete observing instruments, admissible inputs and arbitrary references, exact encodings/axes and zero-return separation. ResourceSafe here means ownership validity, not the quantitative RS theorem. Source/backend preservation, native compilation, approximate execution, algorithm success and hardware are separate.

<a id="qleisli-soundness-theorem-v050"></a>

\[
\forall p,C,\pi,\quad
\operatorname{verify}_{0.5}(p,C,\pi)=\mathrm{true}
\;\Longrightarrow\;
\operatorname{ResourceSafe}(p)\;\land\;
\operatorname{EffectSound}(p,C)\;\land\;
\llbracket p\rrbracket\models C.
\]

| Gate | Required v0.5.0 evidence |
| --- | --- |
| **S05-C1: complete declared scope** | Publish the profile, capacities, entry premises and inventory of every enabled IR/evidence rule and production acceptance path. Preserve the required positive corpus and algorithm gates; a rejecting checker or a phase-word-only theorem cannot satisfy this milestone. Unsupported paths must reject explicitly, with versioned migration for any removed support. |
| **S05-C2: actual checker soundness** | Compose resource/effect, exact-arithmetic interpretation, semantic-contract, hierarchy and instrument proofs into the theorem above. Cover every enabled rule. No remaining assumption that a Rust checker or an unproved evidence producer accepts correctly may substitute for a required proof. |
| **S05-C3: reproducible proof and audit** | Bind the theorem and reviewed statement to the released executable definitions; reproducible builds, declaration/axiom audits and proof replay pass. Keep the runtime Mathlib-free and mathematical interpretation proofs separate. Record native compiler/runtime and transport assumptions explicitly. |
| **S05-C4: production binding** | Complete K3: reconstruct serialized evidence against the independent request, bind the accepted IR to the executed/emitted artifact, pass differential/adversarial/platform checks and fail closed on kernel/transport failure. No silent Rust fallback. |
| **S05-C5: public review and contribution readiness** | Publish the theorem explanation, coverage/assumption ledger and reproduction commands; record independent review and resolve blocking findings. Prepare contributor setup, bounded issues, proof/code review rules, maintainer responsibilities and release/security reporting procedures for the v0.5 community expansion. |

## Physical Realizability Theorem (v1)

To prove by v1 with a substantive Lean backend: derive the complete classical–quantum CPTP semantics from Soundness, construct isometric dilation and synthesize the actual emitted target circuit. Retain every outcome, residual/reference state, pure phase, workspace and environmental discard. A single measurement branch need only be CP/TNI. Unitary semantics alone grants no same-wire realization, inverse or controlled provider.

<a id="physical-realizability-theorem-v1"></a>

### Synthesis workspace contract

For clean backend workspace, C E0=E0 U on every input/reference, including phase. Dirty/borrowed workspace needs a separate arbitrary-state preservation contract. Count preparation, return, routing and peak live workspace under the target profile. Same-wire Clifford+T+Toffoli determinant constraints obstruct F8 (det=i on three wires) and reviewed c3x (det=-1 on four wires); [regressions](../tests/static_semantics.rs) preserve them. Exact synthesis existence theorems are not a proved Qleisli backend or practical cost bound. [Issue 120](https://github.com/MGYamada/Qleisli/issues/120) targets v0.3 specification and [Issue 132](https://github.com/MGYamada/Qleisli/issues/132) bounded v0.4 synthesis.

| Gate | Required evidence by v1 |
| --- | --- |
| PR-C1: semantic bridge | Prove the CPTP corollary and constructive dilation for the complete supported profile, with explicit entry/encoding premises, outcomes and references. |
| PR-C2: gate synthesis | Specify the target gates and preparation/readout capabilities, then prove synthesis of the dilation. State which operations are exact; any approximation needs a declared error metric and certified bound that accounts for arbitrary references and composition. A finite gate set's universality alone is not an exact-synthesis proof. |
| PR-C3: actual backend correspondence | Implement the relevant backend transformations in Lean and prove their connection from the accepted IR to the actual emitted target program, covering lowering, optimization, layout and emission. Bind every stage to its checked input/output; source-to-IR translation validation remains a separate prerequisite for source-level claims. |
| PR-C4: release evidence and trust | Publish the supported profile, proof/coverage and assumption ledger, reproducible audits and independent review. Include the three v1 algorithm families; unsupported target capabilities reject explicitly. Record remaining native compiler/runtime, transport and physical-device assumptions. |

## Resource Safety Theorem (v1)

To prove by v1: an executable static analysis/check issues a finite worst-case resource bound for every admissible execution and prefix, and actual compilation preserves it under declared cost translations. [Resource semantics](resource-semantics.md) defines intended space/work distinctions. Budgets, estimates, QLT tests and ownership are not this theorem.

<a id="resource-safety-theorem-v1"></a>

| Gate | Required evidence by v1 |
| --- | --- |
| RS-C1: explicit resource semantics | Specify a versioned finite bound domain, units/order, input/size and target premises, operational cost and composition rules for every supported construct. Cover retained frames, auxiliary space, actual repetitions, branches, initialization, routing and measurements. |
| RS-C2: executable static bound | Implement the analysis/evidence checker and prove that its actual accepted result bounds every admissible execution, with finite bounds for every admitted size instantiation. Inconclusive, unsupported, overflow and limit outcomes cannot issue evidence. |
| RS-C3: compilation preservation | Prove or independently validate resource-contract preservation for actual source lowering, optimization, synthesis, layout and emission. Bind each certificate to input/output artifacts and cost models. Changed representations require explicit bound translation; exceeding the accepted contract requires rechecking under a revised contract or rejection. |
| RS-C4: complete execution boundary | Establish termination for the supported finite execution model and bound all permitted execution prefixes, measurement/classical branches and bounded retry policies. Distinguish worst-case from expected cost and quantum execution from compiler/search/simulator/host work. State excluded costs and physical assumptions. No hidden unbounded retry or oracle may satisfy a finite whole-workflow claim. |
| RS-C5: release evidence | Publish the supported profile, actual-definition proofs, coverage/assumption ledger, reproducible audits and independent review, including the three v1 algorithm families. Test underestimated counts, stale certificates, phase-preserving but cost-changing passes and resource-model mismatches. |

## Project north star

Make the language people use to think about quantum algorithms coincide with the language they use to write programs. Actual source must expose mathematical stages, reusable contracts and composition.

## v0.1 minimum: semantic contracts

Exact pure contracts fix isometric input/output encodings, logical meaning, phase/layout and entry evidence; independently check whole-space validity as well as the encoded equation. The bounded SC/FC path meets the declared V01 gates, without a general Rust correctness proof. Initial inverse/control need their specified unitary/encoding premises; approximate leakage never authorizes pure release.

```text
u : L_in -> L_out                 logical operation
U : P_in -> P_out                 ideal circuit/IR implementation
E_in : L_in -> P_in               input encoding
E_out : L_out -> P_out            output encoding

E_in† E_in = I,   E_out† E_out = I,   U† U = I,
U E_in = E_out u.
```

The completed V01-C1–C6 profile covers explicit finite spaces/encodings/entry/phase;
independent exact identity/sequence/tensor/qualified inverse/control and finite comparison;
actual source/function/final-IR/body/dependency binding through transformations;
phase-oracle/H;H/simultaneous data-auxiliary X with exact arbitrary-reference cleanup;
unchanged-client substitution including control/correlated references/private layout;
and rejection of wrong phase/predicate/layout/encoding/entry/premises/stale evidence/
lost or copied ownership. [SC/FC](finite-contracts.md) remains the full current contract.
[Exact tests](../tests/semantic_contracts.rs), [source](../tests/certified_source.rs),
[function binding](../tests/function_evidence.rs) and [client substitutions](../tests/function_contracts.rs)
retain evidence. This completed bounded foundation is not a general Rust implementation
proof or general encoded-state API; finite approximate regressions remain separate.


<a id="v019-maintenance-boundary"></a>

## v0.1.9 maintenance acceptance boundary

The completed B019 checkpoint is [historical evidence](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/reviews/b019-completion.md). It is not a new release gate or reason to force patch numbering; continuous audit remains required.

<a id="v1-north-star-textbook-algorithm-structure"></a>

## v1 acceptance target: textbook algorithm structure

Real Shor/QPE/Grover source must compile and execute, reuse definitions across supported sizes/operations and carry checked meaning through implementation substitution. Shor reuses QPE and validates GCD/period/factors with explicit sampling/retry behavior; r>0 and a^r mod N=1 do not establish minimal order. Factor extraction needs even r, nontrivial a^(r/2), and nontrivial GCDs. A full simulator distribution cannot replace samples. PR-C1–C4 and RS-C1–C5 are additional v1 gates.

[Algorithm-structure goal](algorithm-structure-goal.md#release-targets-and-criteria-for-algorithm-structure)
fixes the visible Shor/QPE/Grover stages and their size/access/phase/success/ownership/
instrument/retry contracts; all three must satisfy every gate below.


| ID | v1 acceptance condition |
| --- | --- |
| V1-C1 | Deliver real source definitions of all three algorithms that compile and run within a declared supported profile. A reviewer can map their named stages and composition to the table above without reading primitive gate bodies. Pseudocode, comments, a renamed monolithic circuit, or an unimplemented black-box API do not pass. |
| V1-C2 | Reuse the same definitions across multiple supported sizes, precisions, predicates/operations and problem inputs as appropriate. Size and operation parameters replace manually duplicated fixed instances; current 2/3-bit QPE and N=15 examples alone do not pass. |
| V1-C3 | Carry the v0.1 meaning contracts through component boundaries to checked IR. Demonstrate implementation substitution without rewriting algorithm structure. State access capabilities and all additional instrument/accuracy contracts used by the algorithms. |
| V1-C4 | Validate mathematical behavior as well as readability: phase-sensitive and reference-sensitive cases, failure/retry paths, and independently derived expected results. QPE sampling alone is not an order proof, an unverified candidate is not a factor, and a valid circuit alone is not an algorithm-correctness proof. |
| V1-C5 | Keep source structure stable when changing implementation layout or decomposition. Report circuit-generation and execution costs separately, including oracle access and classical work. Precomputed answers or whole-space truth-table enumeration cannot stand in for the delivered general arithmetic/algorithm construction. Publish supported bounds and proof status. |

<a id="pre-v020-imaginary-v1-code"></a>

## Prerequisite before v0.2.0: imaginary Qleisli 1.0 code

The six imaginary QPE/Grover/AE/Shor/walk/QSVT drafts and requirements satisfied the initial-design prerequisite. Keep their source, capabilities, meaning, phase, cleanup, accuracy/failure and open questions explicit. They remain uncompiled proposals, not final syntax, supported algorithms or a general proof.

## Work order and design decisions

Program first; preserve finite contracts; use symbolic meanings/encodings and evidence-bound hierarchy before size generalization; synthesize predicates/arithmetic without whole-space truth tables. Judge abstractions by removed author obligations, replacement evidence and its independent checker. New forms still need grammar/types/effects/semantics/IR/capacity/migration and validation.
