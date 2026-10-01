# Finite core formalization and soundness obligations

Status: **Stage 1 in progress** (2026-09-26). The English
[source resource calculus](source-resource-rules.md) now gives explicit rules
for mixed values, pending results, calls, frames, and branch interfaces, together
with a paper proof of its resource invariant (R1). An
[ownership-accounting projection](../lean/README.md) is now machine checked
in Lean; it is supporting evidence for the specification, not the complete R1
derivation system. The [source semantics](source-semantics.md) now defines mixed
value/environment interfaces and gives conditional local proofs for call-by-value
substitution, correlated frames, and classical branch/phi composition. The
[typing supplement](source-typing-rules.md) covers all current syntax cases
and proves local basis, scope, determinacy, and effect lemmas T1–T3.
[Q1–Q3](source-soundness.md) now proves ideal quantum soundness for those
explicit mathematical derivations. A small Lean matrix module checks the
Kraus completeness composition used by that paper proof. Adequacy for the
Rust source checker, source-to-IR meaning preservation, and an implementation
soundness guarantee remain unproved. This English edition replaces the earlier
Japanese formalization notes as the authoritative text of this document.

The later [source-to-IR contract C1–C5](source-ir-correspondence.md) gives
concrete table, primitive, certificate, and phi schemas and a conditional paper
preservation theorem for that mathematical translation. The open claim above
concerns the actual Rust compiler, including its satisfaction of those schemas.

The [adopted release milestones](release-milestones.md) place finite,
compositional semantic contracts and independent evidence checking at the
v0.1 boundary, followed by textbook-structured Shor, QPE, and Grover in v1.
The source/IR boundary relation supplies their foundation. The
[finite semantic-contract supplement](semantic-contracts-v0.1.md) now specifies
exact evidence and the separate three-argument computed rule, with local paper
derivations for composition and zero return. The implemented
[function boundary](function-contracts-v0.1.md) retains checked equality
through final IR transformations; the release ledger records the completed
finite acceptance profile. These results do not complete the open general
proofs. The original R1/T1–T3/Q1–Q3 records do not prove this new
Rust path. Its supplemental cases retain exact type trees, complete ownership,
phase, actual-IR binding, and implementation-adequacy premises; Lean is unchanged.

This work follows the [design principles](design-philosophy.md),
[AI-era goal](ai-era-goal.md), and [finite core v0](language-spec.md).
Specifying a rule, testing its implementation on finite examples, and proving a
general theorem are different milestones. The [frontend](frontend-v0.md) and
finite IR implement constructive checks, but a complete formal connection to
the mathematical judgments below is still an obligation.

## 1. Scope and judgments

The core has finite basis types `Unit`, `Bit`, and finite products, finitely many
logical wires, and total terminating functions. It excludes recursion, dynamic
loops, unreported postselection, implicit failure or discard, and arbitrary
external quantum operations. A `basis fn` denotes a total finite table. Its
coherent basis variables are separate from copyable runtime classical values.

An ownership context `Delta` records basis types, distinct subsystem IDs, and
linear tokens. `split/join` change its grouping, without asserting a product
state. Define `H(Delta)` by a fixed tensor order, and interpret local operations
using the appropriate axis permutations and identities on the remaining axes.
Input density operators may be entangled across all owned registers and with
an arbitrary external reference system.

For whole computations, the semantic judgment has the intended form

```text
Gamma ; Delta_in |- P : B ; Delta_out ! epsilon
```

Here `B` is the classical output type. The source effect order is
`Unitary <= Iso <= Observe`. The word *pure* abbreviates the first two classes;
it is not an additional source effect. `Q<A>` is an ownership type, not an
effect. The operational resource judgment in
[source-resource-rules.md](source-resource-rules.md) further distinguishes named
bindings, opaque pending values, and a slot-to-token/wire store. That distinction
is required for mixed tuples and for a branch inside a later call argument.

This is the whole-computation projection of the source expression judgment,
not a separate type/effect system. For a returned mixed value of type `T`, use
`C(T)` and the ordered quantum leaves `Q(T)` from the
[mixed-value interpretation](source-semantics.md#1-mixed-values-and-ordered-quantum-interfaces).
The complete output includes the returned value, surviving environment and
pending/caller frame; the expression's residual `Delta'` alone is insufficient.
The detailed elaboration judgment is authoritative for binding and scope.

For fixed classical input `gamma`, a pure computation returns a classical
value determined by `gamma` and a linear operator `V_gamma`. `Iso` requires
`V_gamma† V_gamma = I`; `Unitary` also requires `V_gamma V_gamma† = I`.
Classical information itself need not be reversible: a unitary declaration may
ignore a classical argument. A call uses its declared effect, even if its body
has a smaller derived effect.

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

Sequential composition matches the first output ownership interface with the
second input interface and makes the first classical result available to the
second computation. Its effect is the join:

```text
Gamma ; Delta0 |- P : B ; Delta1 ! epsilon1
Gamma, b:B ; Delta1 |- F : C ; Delta2 ! epsilon2
-----------------------------------------------------------
Gamma ; Delta0 |- let b=P; F : C ; Delta2 ! max(epsilon1,epsilon2)
```

This is a schematic whole-computation rule. The detailed source rules also
handle linear or mixed results and their moves; this display is not a
replacement for those rules or a proof of a strict indexed monad structure.

Classical `if` checks its arms exclusively from the same entry context. Their
result type trees and outer consumption sets must match. Result positions and
surviving frame slots determine the phi interface, including resources in a
suspended caller. The resource calculus proves that the interface covers each
live slot once, including `Q<Unit>`, and gives an axis-renaming lemma. General
meaning preservation for every implemented branch transformation remains open.
The [local composition lemma](source-semantics.md#6-s3-classical-branch-and-complete-phi-transport)
now specifies the condition/arm instrument equation and simultaneous classical
substitution, assuming correspondence for immediate subderivations.

## 2. Ideal semantics on the entire system

For classical input `gamma` and classical result `b`, the intended meaning is

```text
E[P]_(gamma,b) : L(H(Delta_in)) -> L(H(Delta_out)).
```

For a pure computation, only its deterministic classical result `b_gamma` has a
nonzero branch: `E[P]_(gamma,b_gamma)(rho)=V_gamma rho V_gamma†`. Keep the
operator's exact phase, rather than quotienting by global phase. Controlled
composition can turn that phase into an observable relative phase.

In the following formulas, `R` denotes the remaining quantum system and `S` an
arbitrary external reference. Displayed operators are extended by `I_S`.

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

The Kraus forms imply complete positivity. Completeness implies that the sum of
outcome maps preserves trace; each individual outcome is trace non-increasing.
No equation assumes that the operated-on subsystem is independent of `R` or
`S`. A partial measurement of a Bell pair therefore conditions the other half,
and discarding a half produces a mixed residual state.

If `P` produces an internal classical result `c` and the continuation selects
`F_(d|c)`, retaining both results gives the branch
`F_(d|c) composed with E[P]_(gamma,c)` indexed by `(c,d)`. Hiding `c` gives

```text
G_d = sum_c F_(d|c) composed with E[P]_(gamma,c).
```

This is a sum of CP maps over classical alternatives. It is not coherent
addition of measurement-branch amplitudes.

## 3. Evidence for pure auxiliary release

A standalone zero release is not an isometry or a trace-preserving primitive on
arbitrary inputs. The formal map
`L(rho)=(I_R tensor bra(0)) rho (I_R tensor ket(0))` sends an auxiliary `ket(1)`
input to trace zero. Replacing it with ordinary discard changes the operation
to `Observe` and can lose correlations; it is not a proof of pure cleanup.

Sufficient evidence is a factorization of the preceding map, **for every
input**:

```text
F : H(Delta_in) -> H(R) tensor H(Bit)
F = (I_R tensor ket(0)) V,       V†V=I.
```

Tensoring the equation with any `I_S` shows that the auxiliary is zero and
separated from the remaining system even with an entangled reference.

For the more general structured raw IR, take a total basis function `f:A->Bit`
and the reversible XOR computation `C_f|x,a⟩=|x,a xor f(x)⟩`. Restrict use to

```text
W = sum_(x,a) |x,a⟩⟨x,a| tensor V_(x,a),
```

where each `V_(x,a)` is a unitary on a work register `R`. This keeps both the
source and auxiliary basis labels. On all `|x,0,r⟩` inputs,

```text
C_f† W C_f |x,0,r⟩ = |x,0⟩ tensor V_(x,f(x)) |r⟩.
```

Linear extension gives the required zero factorization for arbitrary states
and references, with effective unitary
`sum_x |x⟩⟨x| tensor V_(x,f(x))`. Scalar phases are included when `R=Unit`.
Consequently the entire `Init0; C_f; W; C_f†; Release0` structure can be certified
as one constructor. Its final release must not be detached and applied to an
unrelated preceding computation. A future general borrow discipline may prevent
conflicting uses, but a lifetime is not itself the factorization proof. v0 uses
the restricted source scope and protected raw-IR regions described here; it
does not implement general source borrowing.

Source v0 permits only the special case with no work register and an expanded
`Z/T` chain on the auxiliary. The resource calculus states its exact phase
formula and private scope rule. General work registers, preservation-effect
signatures, arbitrary borrowing, and `with0` remain outside source v0 even
though raw IR can describe more structured uses.

The later [three-argument form](semantic-contracts-v0.1.md#4-computed-relation-source-form)
adds a different sufficient certificate: `W Ef=Ef u`. This permits the body
to change data and auxiliary together while preserving their encoded relation.
Its paper factorization `Cf† W Cf E0=E0 u` proves exact cleanup with arbitrary
references. The ordinary two-argument v0 form remains restricted as described
above. This finite extension does not introduce general borrowing or a free
release primitive.

## 4. Theorem status and proof work

The **Qleisli Soundness Theorem** is the adopted **v0.5.0** proof milestone.
Its [statement and S05-C1–C5 gates](release-milestones.md#qleisli-soundness-theorem-v050)
cover the actual production IR checker, exact semantics and all enabled rules,
with no outstanding Rust-checker correctness premise. It remains open; the
local executable phase-word theorem below is a precursor. Source translation
validation and native execution assumptions remain explicitly separate.

The [Physical Realizability Theorem](release-milestones.md#physical-realizability-theorem-v1)
is a further adopted target by v1. Derive CPTP semantics for the complete
instrument as a soundness corollary, then construct and synthesize its isometric
dilation over a declared gate set. K4 must prove the correspondence of the
actual Lean backend through emission; semantic validity alone is insufficient.
The third pillar, adopted on 2026-09-30, is the
[Resource Safety Theorem](release-milestones.md#resource-safety-theorem-v1):
finite, statically computable resource bounds for the supported profile,
preserved through actual compilation. Its [resource semantics](resource-semantics.md)
must compose costs with types, meanings and effects, including frames and all
branches. Ownership/R1 results and implementation work limits do not establish
this quantitative guarantee. All three general theorem pillars remain open.

The [QLT design](https://github.com/MGYamada/Qleisli/issues/50) adds a separate future
test-evaluator adequacy obligation: successful exact evaluation must agree with
this IR denotation, and cost evaluation with its declared structural model.
The first experiment will use Rust; later actual-definition Lean proofs and
instance certificates are independent goals, not new S05, PR or RS release gates.
Resource Safety requires its own actual-analysis and compilation proofs; a QLT
cost evaluator alone does not discharge them.
No QLT evaluator or such theorem is implemented by the design record.

| Result | Current status | What it does not establish |
| --- | --- | --- |
| Resource Safety Theorem, RS-C1–C5 | Adopted v1 target on 2026-09-30; to prove. Resource semantics/analyzer and compilation-bound preservation are not implemented as a complete proof path. | No quantitative bound theorem follows from current ownership checks, work/step ceilings, finite probes or cost reports. |
| Source resource accounting, R1 | Paper proof for the explicit [resource calculus](source-resource-rules.md#7-resource-preservation-theorem-and-proof), plus a declaration-boundary corollary. | General equivalence with Rust execution or the whole source specification. |
| Source types, effects, names and scopes, T1–T3 | [Syntax-complete rule presentation](source-typing-rules.md), local paper proofs of typed total basis evaluation, type/effect determinacy, lexical projection and conservative effects; finite boundary regressions. | Uniqueness of generated IR, full source/Rust adequacy, or general quantum soundness. |
| R1-accounting projection | [Lean-checked](../lean/README.md) typed ownership occurrences, local resource edits, frames, complete renaming/phi, and composition. | Full source R1, lexical/effect/scope/history rules, Rust adequacy, or quantum semantics. |
| Lexical scope projection | [Lean lookup model and Rust extraction](lowering-state-refinement.md): entry-domain/classical restoration, spent non-revival, and exact current quantum-footprint preservation after approval. | Every Rust trace supplies the required snapshots/rebound set, complete pending/caller holder coverage, or full source/Rust adequacy. |
| Phi axis renaming | Local paper lemma for complete position/frame interfaces, including references. | Full source-to-IR branch correctness. |
| Source interface semantics and S1–S4 | [Conditional local paper proofs](source-semantics.md) for evaluated-value substitution, arbitrary correlated frames, classical branch/phi and structural IR composition. | Complete typing/name/scope adequacy, every semantic leaf or Rust implementation path. |
| Finite static transformations, F1–F5 | [Conditional exact-operator paper proofs](static-semantics.md) for axis transport, flattening/output order, restricted computed phases, inverse, repetition, and coherent control; exact finite matrix regressions. | General source-to-IR adequacy, acceptance of all unitary raw IR, or verified Rust algorithms. |
| Mathematical translation, C1–C5 | [Explicit source-to-IR schemas and conditional preservation](source-ir-correspondence.md), including basis encoding, concrete leaves, auxiliary chain extraction, and complete phi construction. | Every Rust path constructs that translation, verifier implementation correctness, or exact numerical execution. |
| Restricted auxiliary zero return | Exact local factorization above and in the resource calculus. | A general release primitive or arbitrary auxiliary-body acceptance. |
| Executable Lean phase-word acceptance | [`normalize_correct` and `verify_sound`](../lean-kernel/QleisliKernel/PhaseWord.lean) prove the actual normalizer/checker against direct cyclic phase execution for every bit and initial phase. | Complex interpretation, wire decoding, full IR/ownership/instrument acceptance, source adequacy or native compilation correctness. |
| Actual bounded finite equations, VM-24 | [Actual finite bridge](../lean/Qleisli/Finite.lean) proves literal reconstructed column traces, full-phase encoded equations, arbitrary-reference action, clean return from required output encodings and both whole-space inverse laws; [native/audit scope](../tests/fixtures/verification_v024/README.md). | RawProgram extraction/ownership/effects, original function/source identity, hierarchy finite discharge, native transport refinement or production authority. |
| Canonical single-owner reshape metadata | [`encode_leaves`, `compatible_encoding`, `relabel_round_trip`, `relabel_compose`, `check_encoding`, `check_axes_owners`, `check_reference_coefficients`](../lean-kernel/QleisliKernel/Reshape.lean) prove general prefix encoding/coherence and actual bounded helper properties. | Source syntax/production, arbitrary circuit equations, general Mac Lane coherence, production evidence or H1–H5. |
| Hierarchical operator unitarity | [Actual complex operator laws](../lean/Qleisli/HierarchicalUnitary.lean) and [typing bridges](../lean/Qleisli/HierarchicalTyping.lean) prove both inverse laws for phase/permutations and closure under sequence, tensor, inverse, coherent control and powers. [Recursive acceptance](../lean/Qleisli/HierarchicalAcceptance.lean) derives the actual entry's unitarity, including arbitrary finite reference extension, from supported internal checker success without assumed child isometries. | Finite leaves, calls/encodings/computed regions, the remaining full profile, external production verification or sized source. |
| Finite IR ideal soundness | [Conditional paper argument](finite-core-proof.md) for its constructors and verification premises. | Verified Rust implementation, source translation, or numerical exactness. |
| Source rule-system pure-operation and instrument soundness | [Paper Q1–Q3](source-soundness.md): pure determinacy/isometry/unitarity, finite adaptive instruments, CP and total trace preservation with arbitrary references. | Full Rust acceptance/translation correspondence, numerical exactness, protocol, algorithm, or hardware correctness. |
| Local Kraus completeness algebra | [Lean KA-1–KA-5](../lean/Qleisli/Kraus.lean): exact matrix identities for isometries, output transport, and adaptive composition. | Positivity/trace, source derivations, arbitrary-reference extension, or the whole Q1–Q3 proof. |

**Pure-operation result and transfer obligation.** For each fixed classical
input, every `Iso` derivation of the explicit source rules denotes an isometry
and every `Unitary` derivation a unitary. Q1's induction uses exact sealed matrices, checked injections,
preparation, structural isomorphisms, phase-preserving static operations,
classical selection, and the auxiliary factorization lemma. Arbitrary release
is not an induction base case. Transferring this paper theorem to every
Rust-accepted source program still requires implementation adequacy.

**Instrument result and transfer obligation.** For every derivation of the
explicit source rules and fixed classical input, each `E[P]_(gamma,b)` is
completely positive and trace non-increasing and their sum is trace preserving.
Q2–Q3 uses Kraus
completeness for observations, pure isometries as single-outcome instruments,
and finite adaptive composition. The proof extends all operations by an
arbitrary reference identity, without excluding entanglement. The relation
between this meaning, actual Rust IR generation, and numerical execution is
not proved by the instrument equations.

**Remaining obligations, in priority order:**

1. Formalize the complete finite raw IR's pure maps and observing instruments,
   including ownership and arbitrary reference systems, from the
   [IR proof obligations](finite-core-proof.md). A future Physlib bridge must
   satisfy the [dependency gate](../lean/README.md#future-physlib-bridge).
2. Prove acceptance soundness of the actual executable checker in the
   [Mathlib-free kernel](../lean-kernel/README.md), covering every enabled rule.
   Follow [VM-22–VM-29](verification-migration-v0.2.md) and the
   [authority-transfer gates](lean-kernel-migration.md). Rust remains production
   authoritative; differential tests and the phase-word theorem do not transfer it.
3. Close the complete hierarchy/request boundary. Supported internal derivations
   have [constructed denotations](../lean/Qleisli/HierarchicalEvaluation.lean)
   and [unitarity proofs](../lean/Qleisli/HierarchicalAcceptance.lean).
   [Finite](../lean/Qleisli/HierarchicalFiniteUnitary.lean),
   [independent-root](../lean/Qleisli/HierarchicalRoot.lean),
   [instrument](../lean/Qleisli/HierarchicalInstrument.lean) and
   [Fourier-host](hierarchical-ir-spec.md#fourier-request-host) extensions retain
   explicit leaf-reader, native/decoder and provider premises. Discharge these
   against the actual immutable artifact and independent request, preserving
   phase, output order, zero return and complete instruments. Remaining rules,
   source integration and R14/H1–H5 are open; all external schemas stay disabled.
   The [rule inventory](rule-inventory.md) records exact component coverage and
   saved validation. Keep pinned registry types and temporary APIs audited until
   their specified compatible migration/removal conditions hold.
4. Establish source/Rust adequacy and actual backend-pass preservation. Cover
   typing, effects, names, snapshots, tombstones, pending/caller frames and the
   open [scope-trace premises](lowering-state-refinement.md), then realize
   [C1–C5](source-ir-correspondence.md) and transfer S1–S4, F1–F5 and Q1–Q3.
   Retain independent IR checks at every [pipeline boundary](lean-kernel-migration.md#pipeline-migration-with-a-stable-ir-verification-boundary).
   Lowering, optimization, synthesis and emission need proofs of their actual
   definitions; external candidate search may remain untrusted when a proved
   [LeafRealizer](lean-kernel-migration.md#external-search-and-the-leafrealizer-checker)
   checks its result. PR-C1–C4 and RS-C1–C5 must bind actual output and resource
   bounds to the checked input and requested meaning.
5. Keep numerical execution, protocol properties, algorithm success and hardware
   realization separate. Preserve Bell, partial measurement/discard, feedback
   and phase-oracle regressions. Finite tests or library imports cannot complete
   a general implementation theorem.

Independent verification precedes general frontend adequacy because it must
check every producer. Source adequacy remains required for source-level claims.
Ownership tracks operation rights without general entanglement detection;
whole-system validity and clean release require their own checked evidence.

### Temporary proof markers

**Importance and lifetime reviewed at the user's request, 2026-09-29.** Use
the following importance levels when choosing proof work. They are maintenance
priorities, not degrees of mathematical validity or permission to skip audits.

| Importance | Obligation and current examples | Maintenance policy |
| --- | --- | --- |
| P0 — acceptance and binding | Actual executable checker soundness, complete ownership/effect/entry binding, finite-request extraction, actual-body denotations and reference preservation: kernel `Hierarchical` checks, `Reshape`, `HierarchicalEvaluation`, `HierarchicalAcceptance`, `HierarchicalFiniteEvaluation`, `HierarchicalFiniteUnitary`, `HierarchicalRoot`, `HierarchicalInstrument`, and actual gradient/Fourier inspection bridges. | Keep and repair first. These obligations remain necessary when a checker or representation is replaced; a narrower theorem cannot replace them. Current component scope and explicit reader/native premises still apply. |
| P1 — semantic foundations and required components | Reusable operator/matrix, layout, phase, Fourier, Kraus/completeness and reference-extension laws; source resource/scope models; call-lowering laws; current QFT/QPE projection components and semantic regressions. | Preserve reusable results. Extend them for a concrete caller or acceptance obligation. A component may be temporary while its current callers still require it. |
| P2 — migration and compatibility wrappers | Superseded assumed-environment conclusions, projection-only entry packaging, legacy basis-conditioned dispatch and a misleading compatibility name. | Maintain compatibility and validation; direct new development to the replacement. Avoid adding parallel wrapper families without a concrete caller. |

Mark proofs intended for eventual removal with `temporary (TP-...)` in their
Lean documentation comment, followed by `importance P0`, `importance P1` or
`importance P2`. Record the replacement and concrete removal
condition. The marker does not weaken their statement, build or axiom-audit
requirements. Keep reusable mathematical lemmas, actual-body definitions and
proofs used by the final checker unmarked. Length, low priority, finite width,
conditional premises or experimental origin alone do not justify retirement.
Labels apply only to the listed declarations, never implicitly to a file,
namespace, its dependencies or its tests. The P0/P1 inventory above is a
preservation policy; unlisted declarations have not been approved for deletion.

The Lean names below are relative to `Qleisli`, except TP-004, which is in
`QleisliKernel`. **No declaration is removed by this classification.**

| ID | Importance | Temporary declarations | Replacement and removal condition |
| --- | --- | --- | --- |
| TP-001 | P2 | `HierarchicalSemantics.Interprets` and `ordinary_sound`, `power_sound`, `derives_sound`, `checkAll_sound`, `checkAll_entry_sound`; `HierarchicalOperators.checkAll_operator`, `checkAll_matrix`, `checkAll_reference`, `powerEntry_operators` | Use the [constructed evaluator and denotation theorems](../lean/Qleisli/HierarchicalEvaluation.lean). Migrate remaining wrappers, including the independent coherent-power request conclusion, before removal. Keep `bodies_sound`, interface/entry binding, operator definitions and matrix laws: the constructed proofs use them. |
| TP-002 | P2 | `HierarchicalPower.inspectEntry_equation`, `inspectEntry_reference` | Replace projection-only entry wrappers with the constructed derivation entry, retaining its independent power request. Keep the local `inspect_operators`/`inspect_unitary` component lemmas where used. |
| TP-003 | P2 | `Schema.power_sound` | The shipped registry already selects `Schema.power_coherent_sound`. Retire the old basis-conditioned wrapper; retain lower-level action lemmas still used by QPE. |
| TP-004 | P2 | [`PhaseLayout.check_reference`](../lean-kernel/QleisliKernel/PhaseLayout.lean) | Use `check_reference_value` for the same product-value statement. Retire only the compatibility name after caller migration and public API review. Neither name proves an entangled-reference theorem; keep `check_sound` and the separate complex/reference bridges. |
| TP-005 | P1 — still required | [`QftGraph.check_fourier`, `check_reference`](../lean/Qleisli/QftGraph.lean); [`QftGraph.checked_matrix`, `check_unitary`](../lean/Qleisli/QftUnitary.lean); [`Schema.qft_sound`](../lean/Qleisli/Schema.lean) | Replace the separate internal QFT-graph projection interface with an independently requested Fourier theorem over the actual full hierarchical artifact. Require actual outer reversal, full finite H binding, exact phase, both inverse laws and reference preservation; migrate QPE callers and the exported registry type before retirement. The recursive-body theorem alone does not meet this condition. Keep generic Fourier, normalization, index and matrix lemmas, and the bounded circuit regressions. |
| TP-006 | P1 — still required | [`Qpe.inverse_coefficient`, `checked_branch`, `checked_instrument`, `checked_plan`](../lean/Qleisli/Qpe.lean); [`Qpe.checked_complete`, `checked_plan_complete`, `accepted_plan`](../lean/Qleisli/QpeComplete.lean); [`Schema.qpe_sound`](../lean/Qleisli/Schema.lean) | Replace the separate internal QPE-plan interface with a theorem over actual hierarchical preparation, independently verified provider/control access, inverse QFT and measurement. Require the same exact Kraus branches, retained target/reference state, all-outcome completeness/trace preservation and boundary/freshness obligations. Migrate callers and the exported registry type before retirement. Keep `kraus`, `kraus_complete`, character orthogonality, `complete_withReference`, `complete_trace`, bit encodings and reusable preparation/power laws. |

TP-005 and TP-006 describe a future interface replacement, not obsolete
mathematics or a completed implementation. `Schema.qft_sound` and
`Schema.qpe_sound` remain the current pinned component theorems. Preserve their
type/source manifest and all three external-disabled entries until the normal
binding and enablement gates pass. Replacing these interfaces is not an extra
v0.2.1 release gate or authorization to remove public APIs in a PATCH release.

Removal must respect the [public Lean API compatibility policy](versioning.md).
These markers identify known retirement paths; they do not promise that all
remaining proofs will be permanent. Review the list as migration changes the
dependency graph. Before deletion, verify every caller and registry entry has
migrated, the replacement covers the same premises/conclusion, and required
semantic regressions and axiom audits still pass. Historical validation records
and first attempts remain intact. This labeling pass leaves declarations,
imports, proof bodies, checker behavior and feature gates unchanged.
