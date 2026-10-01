# Finite core formalization and soundness obligations

Current general Rust acceptance/source/backend adequacy remains unproved. Completed mathematical rule/proof expositions are available in [Git history](https://github.com/MGYamada/Qleisli/tree/7bfcd36916199b05d5ab11851d38d53375ccf71e/docs); executable models, proofs and validation remain in [lean](../lean/README.md), [lean-kernel](../lean-kernel/README.md) and fixtures. The tables distinguish paper derivations, actual-definition component theorems and implementation obligations. [Milestones](release-milestones.md) are authoritative.

## 1. Scope and judgments

Finite basis Unit/Bit/products, distinct tokens/wires, total termination and effects Unitary <= Iso <= Observe. Interpret local operations globally, with ordered axes and arbitrary reference identity. The complete output includes mixed returned values, residual environment and pending/caller frames. Classical outputs of pure operations depend only on classical input. Declared call effects are retained. Current [language](language-spec.md), [types](type-system.md) and [grammar](syntax-v0.md) remain normative.

```text
Gamma ; Delta_in |- P : B ; Delta_out ! epsilon
```

| Form | Resource interface | Effect and additional obligation |
| --- | --- | --- |
| Classical literals and Boolean operations | Change classical records only after evaluating operands once in order; preserve the complete quantum frame. | The Boolean step is `Unitary`; join operand effects. |
| `init0` | Add a fresh `Q<Bit>` slot and logical wire. | `Iso`; prepare zero. |
| Sealed gates | Consume input tokens and return new tokens for the same ordered wires. | `Unitary`; exact sealed matrices. |
| `do/pure` | Consume `Q<A>`, return `Q<B>`, append fresh wires if needed. | Check the total injection; same width is `Unitary`, growing width is `Iso`. |
| `split/join` | Partition or concatenate disjoint ordered wire lists. | `Unitary`; preserve correlations. |
| Static inverse, repetition, `qif` | Check unary `Q<A> -> Q<A>` unitaries; return all input resources. | `Unitary`; keep exact phases, check both branches and zero repetitions. |
| `measure_z` | Consume `Q<Bit>`, return only `CBit`. | `Observe`; no old quantum handle remains. |
| `discard` | Consume `Q<A>`, return `Unit`. | `Observe`, including zero-width ownership. |
| `reset` | End the old `Q<Bit>`, create a fresh logical wire and handle. | `Observe`; discard correlations with the old wire. |
| v0 `with_computed` | Preserve the source interface and close one private auxiliary. | `Unitary`; expanded auxiliary `Z/T` chain or identity only. |
| Certified three-argument `with_computed` | Transfer the source to private data ownership and return both data and auxiliary before certified cleanup; retain the outer frame. | `Unitary`; SC-COMPUTED requires `W Ef=Ef u` for a fixed logical unitary u, including actual output-axis order. |
| `apply_contract` | Consume and return the same exact unary `Q<A>` interface, preserving every frame owner. | `Unitary`; [FC-APPLY](function-contracts-v0.1.md) requires independently checked equality to a fixed specification and retains immutable evidence through transforms. |

```text
Gamma ; Delta0 |- P : B ; Delta1 ! epsilon1
Gamma, b:B ; Delta1 |- F : C ; Delta2 ! epsilon2
-----------------------------------------------------------
Gamma ; Delta0 |- let b=P; F : C ; Delta2 ! max(epsilon1,epsilon2)
```

## 2. Ideal semantics on the entire system

Pure outcome maps are V rho V† with exact operator phase; Iso requires V†V=I and Unitary also VV†=I. Observations use whole-system Kraus maps. Adaptive composition uses probabilistic sums of hidden histories, preserving all outcome labels and residual/reference states. Neither disjoint ownership nor split/join asserts a product state.

```text
E[P]_(gamma,b) : L(H(Delta_in)) -> L(H(Delta_out)).
```

| Constructor | Exact interpretation | Required identity |
| --- | --- | --- |
| Classical constant, `not`, `and`, `xor` | Deterministically extend the classical record; quantum operator `I`. | `I†I=II†=I`; operand maps compose in order. |
| `init0` | `V = ket(0)_q tensor I_R`, with a chosen axis order. | `V†V=I_R` |
| Injective lift | `V_f = sum_a ket(f(a)) bra(a)` | Injectivity gives `V_f†V_f=I_A`. |
| Sealed gate | A fixed exact operator `U`, extended to all other axes. | `U†U=UU†=I` |
| `split/join` | The canonical tensor/axis isomorphism. | Inverse permutations compose to identity. |
| `qif` | `ket(0)bra(0) tensor U0 + ket(1)bra(1) tensor U1` | Orthogonal projectors and unitary `Ui` give unitarity. |
| `measure_z(q)` | `K_b=bra(b)_q tensor I_R`; `E_b(rho)=K_b rho K_b†`. | `sum_b K_b†K_b=I_(qR)` |
| `discard(q)` | `sum_b K_b rho K_b† = tr_q(rho)`; hide the basis outcome. | Kraus completeness; extend to a wider register's full basis. |
| `reset(q)` | `J_b=ket(0)_(q') bra(b)_q tensor I_R`; hide `b`. | `sum_b J_b†J_b=I_(qR)` |

```text
G_d = sum_c F_(d|c) composed with E[P]_(gamma,c).
```

## 3. Evidence for pure auxiliary release

Release is valid only after exact factorization for every input/reference, not from ownership, scope or a numerical zero. Restricted two-argument computed use preserves source/auxiliary labels; certified three-argument use independently checks W E_f=E_f u and actual output order. Arbitrary protected measurement/reset/discard and a detached Release0 are not permitted.

```text
F : H(Delta_in) -> H(R) tensor H(Bit)
F = (I_R tensor ket(0)) V,       V†V=I.
```

```text
W = sum_(x,a) |x,a⟩⟨x,a| tensor V_(x,a),
```

```text
C_f† W C_f |x,0,r⟩ = |x,0⟩ tensor V_(x,f(x)) |r⟩.
```

## 4. Theorem status and proof work

Prioritize independent actual IR acceptance and the evidence kernel, then complete hierarchy/finite/root and instrument binding, then actual source/backend preservation. Rust remains production-authoritative; external schemas stay disabled. VM-24 proves the bounded finite component and VM-25 covers straight-line pure raw checking. [VM-26–29](verification-migration-v0.2.md) and S05/PR/RS gates remain open. Physlib needs the [separate dependency gate](../lean/README.md#future-physlib-bridge). Protocol/algorithm/hardware correctness is separate.

| Result | Current status | What it does not establish |
| --- | --- | --- |
| Resource Safety Theorem, RS-C1–C5 | Adopted v1 target on 2026-09-30; to prove. Resource semantics/analyzer and compilation-bound preservation are not implemented as a complete proof path. | No quantitative bound theorem follows from current ownership checks, work/step ceilings, finite probes or cost reports. |
| Source resource accounting, R1 | Paper proof for the explicit [resource calculus](https://github.com/MGYamada/Qleisli/blob/7bfcd36916199b05d5ab11851d38d53375ccf71e/docs/source-resource-rules.md#7-resource-preservation-theorem-and-proof), plus a declaration-boundary corollary. | General equivalence with Rust execution or the whole source specification. |
| Source types, effects, names and scopes, T1–T3 | [Syntax-complete rule presentation](https://github.com/MGYamada/Qleisli/blob/7bfcd36916199b05d5ab11851d38d53375ccf71e/docs/source-typing-rules.md), local paper proofs of typed total basis evaluation, type/effect determinacy, lexical projection and conservative effects; finite boundary regressions. | Uniqueness of generated IR, full source/Rust adequacy, or general quantum soundness. |
| R1-accounting projection | [Lean-checked](../lean/README.md) typed ownership occurrences, local resource edits, frames, complete renaming/phi, and composition. | Full source R1, lexical/effect/scope/history rules, Rust adequacy, or quantum semantics. |
| Lexical scope projection | [Lean lookup model and Rust extraction](https://github.com/MGYamada/Qleisli/blob/7bfcd36916199b05d5ab11851d38d53375ccf71e/docs/lowering-state-refinement.md): entry-domain/classical restoration, spent non-revival, and exact current quantum-footprint preservation after approval. | Every Rust trace supplies the required snapshots/rebound set, complete pending/caller holder coverage, or full source/Rust adequacy. |
| Phi axis renaming | Local paper lemma for complete position/frame interfaces, including references. | Full source-to-IR branch correctness. |
| Source interface semantics and S1–S4 | [Conditional local paper proofs](https://github.com/MGYamada/Qleisli/blob/7bfcd36916199b05d5ab11851d38d53375ccf71e/docs/source-semantics.md) for evaluated-value substitution, arbitrary correlated frames, classical branch/phi and structural IR composition. | Complete typing/name/scope adequacy, every semantic leaf or Rust implementation path. |
| Finite static transformations, F1–F5 | [Conditional exact-operator paper proofs](https://github.com/MGYamada/Qleisli/blob/7bfcd36916199b05d5ab11851d38d53375ccf71e/docs/static-semantics.md) for axis transport, flattening/output order, restricted computed phases, inverse, repetition, and coherent control; exact finite matrix regressions. | General source-to-IR adequacy, acceptance of all unitary raw IR, or verified Rust algorithms. |
| Mathematical translation, C1–C5 | [Explicit source-to-IR schemas and conditional preservation](https://github.com/MGYamada/Qleisli/blob/7bfcd36916199b05d5ab11851d38d53375ccf71e/docs/source-ir-correspondence.md), including basis encoding, concrete leaves, auxiliary chain extraction, and complete phi construction. | Every Rust path constructs that translation, verifier implementation correctness, or exact numerical execution. |
| Restricted auxiliary zero return | Exact local factorization above and in the resource calculus. | A general release primitive or arbitrary auxiliary-body acceptance. |
| Executable Lean phase-word acceptance | [`normalize_correct` and `verify_sound`](../lean-kernel/QleisliKernel/PhaseWord.lean) prove the actual normalizer/checker against direct cyclic phase execution for every bit and initial phase. | Complex interpretation, wire decoding, full IR/ownership/instrument acceptance, source adequacy or native compilation correctness. |
| Actual bounded finite equations, VM-24 | [Actual finite bridge](../lean/Qleisli/Finite.lean) proves literal reconstructed column traces, full-phase encoded equations, arbitrary-reference action, clean return from required output encodings and both whole-space inverse laws; [native/audit scope](../tests/fixtures/verification_v024/README.md). | RawProgram extraction/ownership/effects, original function/source identity, hierarchy finite discharge, native transport refinement or production authority. |
| Straight-line pure raw checking, VM-25 | [Actual pure acceptance](../lean/Qleisli/RawPure.lean) connects all eleven constructors to independent phase-sensitive complex action and clean-scope obligations. [Bounded denotation](../lean/Qleisli/RawDenotation.lean), [non-dense protected cleanup](../lean/Qleisli/RawProtected.lean) and [fresh retained graph/binding](../lean/Qleisli/RawFunction.lean) cover original bodies, arbitrary references and exact attachments/capacities; [scope](../tests/fixtures/verification_v025/completion/README.md). | VM-26 classical branches/instruments, production hierarchy closure, source/native/execution refinement, complete S05 soundness or production authority. |
| Canonical single-owner reshape metadata | [`encode_leaves`, `compatible_encoding`, `relabel_round_trip`, `relabel_compose`, `check_encoding`, `check_axes_owners`, `check_reference_coefficients`](../lean-kernel/QleisliKernel/Reshape.lean) prove general prefix encoding/coherence and actual bounded helper properties. | Source syntax/production, arbitrary circuit equations, general Mac Lane coherence, production evidence or H1–H5. |
| Hierarchical operator unitarity | [Actual complex operator laws](../lean/Qleisli/HierarchicalUnitary.lean) and [typing bridges](../lean/Qleisli/HierarchicalTyping.lean) prove both inverse laws for phase/permutations and closure under sequence, tensor, inverse, coherent control and powers. [Recursive acceptance](../lean/Qleisli/HierarchicalAcceptance.lean) derives the actual entry's unitarity, including arbitrary finite reference extension, from supported internal checker success without assumed child isometries. | Finite leaves, calls/encodings/computed regions, the remaining full profile, external production verification or sized source. |
| Finite IR ideal soundness | [Conditional paper argument](https://github.com/MGYamada/Qleisli/blob/7bfcd36916199b05d5ab11851d38d53375ccf71e/docs/finite-core-proof.md) for its constructors and verification premises. | Verified Rust implementation, source translation, or numerical exactness. |
| Source rule-system pure-operation and instrument soundness | [Paper Q1–Q3](https://github.com/MGYamada/Qleisli/blob/7bfcd36916199b05d5ab11851d38d53375ccf71e/docs/source-soundness.md): pure determinacy/isometry/unitarity, finite adaptive instruments, CP and total trace preservation with arbitrary references. | Full Rust acceptance/translation correspondence, numerical exactness, protocol, algorithm, or hardware correctness. |
| Local Kraus completeness algebra | [Lean KA-1–KA-5](../lean/Qleisli/Kraus.lean): exact matrix identities for isometries, output transport, and adaptive composition. | Positivity/trace, source derivations, arbitrary-reference extension, or the whole Q1–Q3 proof. |

### Temporary proof markers

Importance and lifetime are independent. Mark eventual retirements temporary (TP-ID), P0/P1/P2, replacement and concrete removal condition in Lean doc comments. Keep every marked declaration built/audited, reusable mathematics and required current registry APIs. Do not mark a result temporary merely because it is long, bounded, conditional or low priority. No declaration is removed by this inventory. Removal requires caller/registry migration, same obligation coverage and public API review; TP-005/006 remain required.

| Importance | Obligation and current examples | Maintenance policy |
| --- | --- | --- |
| P0 — acceptance and binding | Actual executable checker soundness, complete ownership/effect/entry binding, finite-request extraction, actual-body denotations and reference preservation: kernel `Hierarchical` checks, `Reshape`, `HierarchicalEvaluation`, `HierarchicalAcceptance`, `HierarchicalFiniteEvaluation`, `HierarchicalFiniteUnitary`, `HierarchicalRoot`, `HierarchicalInstrument`, and actual gradient/Fourier inspection bridges. | Keep and repair first. These obligations remain necessary when a checker or representation is replaced; a narrower theorem cannot replace them. Current component scope and explicit reader/native premises still apply. |
| P1 — semantic foundations and required components | Reusable operator/matrix, layout, phase, Fourier, Kraus/completeness and reference-extension laws; source resource/scope models; call-lowering laws; current QFT/QPE projection components and semantic regressions. | Preserve reusable results. Extend them for a concrete caller or acceptance obligation. A component may be temporary while its current callers still require it. |
| P2 — migration and compatibility wrappers | Superseded assumed-environment conclusions, projection-only entry packaging, legacy basis-conditioned dispatch and a misleading compatibility name. | Maintain compatibility and validation; direct new development to the replacement. Avoid adding parallel wrapper families without a concrete caller. |

| ID | Importance | Temporary declarations | Replacement and removal condition |
| --- | --- | --- | --- |
| TP-001 | P2 | `HierarchicalSemantics.Interprets` and `ordinary_sound`, `power_sound`, `derives_sound`, `checkAll_sound`, `checkAll_entry_sound`; `HierarchicalOperators.checkAll_operator`, `checkAll_matrix`, `checkAll_reference`, `powerEntry_operators` | Use the [constructed evaluator and denotation theorems](../lean/Qleisli/HierarchicalEvaluation.lean). Migrate remaining wrappers, including the independent coherent-power request conclusion, before removal. Keep `bodies_sound`, interface/entry binding, operator definitions and matrix laws: the constructed proofs use them. |
| TP-002 | P2 | `HierarchicalPower.inspectEntry_equation`, `inspectEntry_reference` | Replace projection-only entry wrappers with the constructed derivation entry, retaining its independent power request. Keep the local `inspect_operators`/`inspect_unitary` component lemmas where used. |
| TP-003 | P2 | `Schema.power_sound` | The shipped registry already selects `Schema.power_coherent_sound`. Retire the old basis-conditioned wrapper; retain lower-level action lemmas still used by QPE. |
| TP-004 | P2 | [`PhaseLayout.check_reference`](../lean-kernel/QleisliKernel/PhaseLayout.lean) | Use `check_reference_value` for the same product-value statement. Retire only the compatibility name after caller migration and public API review. Neither name proves an entangled-reference theorem; keep `check_sound` and the separate complex/reference bridges. |
| TP-005 | P1 — still required | [`QftGraph.check_fourier`, `check_reference`](../lean/Qleisli/QftGraph.lean); [`QftGraph.checked_matrix`, `check_unitary`](../lean/Qleisli/QftUnitary.lean); [`Schema.qft_sound`](../lean/Qleisli/Schema.lean) | Replace the separate internal QFT-graph projection interface with an independently requested Fourier theorem over the actual full hierarchical artifact. Require actual outer reversal, full finite H binding, exact phase, both inverse laws and reference preservation; migrate QPE callers and the exported registry type before retirement. The recursive-body theorem alone does not meet this condition. Keep generic Fourier, normalization, index and matrix lemmas, and the bounded circuit regressions. |
| TP-006 | P1 — still required | [`Qpe.inverse_coefficient`, `checked_branch`, `checked_instrument`, `checked_plan`](../lean/Qleisli/Qpe.lean); [`Qpe.checked_complete`, `checked_plan_complete`, `accepted_plan`](../lean/Qleisli/QpeComplete.lean); [`Schema.qpe_sound`](../lean/Qleisli/Schema.lean) | Replace the separate internal QPE-plan interface with a theorem over actual hierarchical preparation, independently verified provider/control access, inverse QFT and measurement. Require the same exact Kraus branches, retained target/reference state, all-outcome completeness/trace preservation and boundary/freshness obligations. Migrate callers and the exported registry type before retirement. Keep `kraus`, `kraus_complete`, character orthogonality, `complete_withReference`, `complete_trace`, bit encodings and reusable preparation/power laws. |
