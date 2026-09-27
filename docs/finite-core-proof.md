<a id="現行有限-ir-の量子的健全性-紙上の証明"></a>

# Quantum soundness of the current finite IR: a paper proof

Status: **conditional mathematical proof for the current Rust IR**
(2026-09-26). This document develops the [finite-core formalization](formal-core.md)
for the current constructors and verification conditions. Correspondence
between the mathematical interpretation and the Rust implementation remains
subject to audit; this is not a machine-checked proof. Its subject is finite
IR accepted by the verifier. Meaning preservation by the initial `.qli`
frontend and future external operations are separate proof obligations.

This English edition supersedes the earlier Japanese supplementary paper
proof without changing its premises or conclusions. It is the authoritative
edition of this argument, not a replacement language specification. Consult
the normative [language specification](language-spec.md), the
[formalization overview](formal-core.md), and the separately scoped
[source-soundness argument](source-soundness.md).

The conditional local `CertifiedCompute` case added on 2026-09-27 is specified
by the [English SC rules](semantic-contracts-v0.1.md). Checking concerns the
actual W and explicitly specified u; `W E_f=E_f u` yields
`C_f† W C_f E_0=E_0 u`. The fresh auxiliary entry satisfies E_0, and u is
unitary, so exact zero return, separation, and purity follow. Ownership
consumes source once, returns a fresh token for the same ordered wires, and
requires the auxiliary ID to be globally fresh. These are local premises
added to the structural proof of 2026-09-26 below. They do not mean that
formal verification of exact arithmetic, the Rust checker, or source
translation has been completed.

The same day's `CircuitAction::Contract` follows the
[English FC rules](function-contracts-v0.1.md). It can be added to the
pure-map induction under these premises: immutable function evidence supplies
unitarity of the implementation and its exact meaning `U=u`, and the current
axis placement, disjoint controls, and adjoint flag are independently checked.
Induct over finite construction depth for dependent evidence. Retaining raw
IR and source snapshots does not prove translation correctness. The Rust
correspondence for independent extraction, exact checking, and execution
remains subject to audit.

<a id="1-定理の正確な範囲"></a>

## 1. Exact scope of the theorems

Assume the following.

1. The input is a `RawProgram` accepted by `verify` through the safe Rust API.
   Private fields of `VerifiedProgram` are not forged, and subsequent
   transformations are reverified.
2. Interpret the phases of `Gate`, `Cnot`, `Toffoli`, `ProtectedUse`, and
   `ApplyUnitary` using the **exact complex arithmetic** described below.
   Values produced by the finite-precision reference executor are not evidence
   of an equality.
3. Execution of `RawOp` terminates through finite sequences and finite
   `ClassicalBranch` trees. Add no unreported postselection, failure, external
   quantum operations, or infinite loops.
4. Each constructor's quantum meaning agrees with the equations in this
   document. In particular, branch `QuantumPhi` is positional axis renaming,
   not measurement or duplication of a quantum state.

**Theorem A (resources).** On any classical/measurement path of accepted IR,
live ownership tokens own pairwise disjoint ordered wire lists. Operations
consume only live tokens, once each, and every final surviving token appears
exactly once in `quantum_outputs`. A width-zero `Q<Unit>` is also a linear token.

**Theorem B (purity).** Fix the input classical values γ. Accepted IR with
derived effect `Unitary` or `Iso` denotes a linear isometry V_γ from quantum
input to quantum output, satisfying V_γ†V_γ = I. If the derived effect is
`Unitary`, then V_γV_γ† = I as well. For a declared effect of `Unitary`, the
verifier also requires the derived effect to be `Unitary`, giving the same
conclusion. A weaker declaration of `Iso` or `Observe` does not remove the
property determined by the derived effect.

**Theorem C (observation).** For any accepted IR, classical input γ, and public
classical output b, the ideal meaning E_{γ,b}: L(H_in) → L(H_out) is completely
positive and trace non-increasing, and Σ_b E_{γ,b} is trace preserving. Even
when the public output is empty, the sum is a one-outcome CPTP map. The map
with explicit classical output, ρ ↦ Σ_b |b⟩⟨b| ⊗ E_{γ,b}(ρ), is also CPTP.

These claims do not establish protocol correctness, computational results,
or hardware noise/capability guarantees. Theorem B's V_γ is a map **for each
fixed classical input**. The theorem does not implicitly promote classical
inputs to quantum controls.

<a id="2-文脈軸古典履歴"></a>

## 2. Contexts, axes, and classical histories

A width-n `BasisShape` corresponds to {0,1}^n, with H_n = ℂ^{2^n}.
For n=0, `Unit` is the one-dimensional space H_0=ℂ. Its `Q<Unit>` ownership
token remains even though it has no quantum wires. A register's
`wires=[w₀,…,wₙ₋₁]` is **ordered**: bit i of local label x=Σᵢ xᵢ2ⁱ is
placed on wᵢ. All wires in the currently live registers are pairwise disjoint.

At each verification point, the whole-system space H(Δ) is the tensor product
listing every live wire exactly once. Any choice of whole-system axis order
is related by the corresponding axis permutation P_π. At entry, choose the
order of `quantum_inputs` and the `wires` order inside each port as canonical;
at exit, choose the order of `quantum_outputs` and the order inside each
register. An intermediate operation is expressed by a P_π moving target axes
to the front, a local map, and the inverse axis placement. A difference in
wire IDs alone is not a difference in quantum state. Input density operators
may be arbitrarily entangled across all wires and with an external reference S.

The classical environment γ maps each `ClassicalId` to a bit value.
`ClassicalConst`, `ClassicalNot`, `ClassicalAnd`, and `ClassicalXor` add
deterministic values to it. `MeasureZ` is the only operation that writes a
quantum basis label into γ. For each **history** h, including the hidden Kraus
indices of measurement, `Discard`, and `Reset`, carry a CP map F_h acting on
the unnormalized state and a classical environment γ_h. Define
E_{γ,b}=Σ_{h:out(γ_h)=b}F_h by summing histories whose ordered final
`classical_outputs` have values b. Duplicate classical-output references
merely copy classical values. Hiding unpublished measurement results or
discard indices requires a **sum of CP maps over classical alternatives**,
not addition of amplitudes.

Fix the classical input as γ. Define open semantics allowing entanglement
with an external reference before specializing to an empty quantum input.
`sim::run_closed` numerically approximates only the instances of this general
semantics whose quantum input/output contexts and classical input context
are empty.

<a id="3-原始構成子の意味と局所補題"></a>

## 3. Primitive meanings and local lemmas

Apply identities to unmentioned wires R and the external reference S.
Below, “unitary” means equality over the exact complex numbers.

| Constructor | Local meaning | Isometry or Kraus completeness |
| --- | --- | --- |
| `Init0` | V: \|ψ⟩_R ↦ \|ψ⟩_R\|0⟩_q, with fresh wire q. | V†V=I_R. Not surjective because it adds one wire. |
| `Gate` | Apply H=(1/√2)[[1,1],[1,−1]], X, Z, or T=diag(1,e^{iπ/4}) to the target bit. | Each U†U=UU†=I. Do not quotient out phase. |
| `Cnot`, `Toffoli` | Basis permutations that preserve control bits and XOR-flip the target bit. | Each permutation matrix is its own inverse. |
| `Split`, `Join` | Change ownership tokens and the grouping of ordered registers. | Canonical axis isomorphism H_{m+n}≅H_m⊗H_n. The state undergoes identity or axis permutation. |
| `LiftBasis(table)` | For a total table f:{0,1}^n→{0,1}^m, V_f=Σ_x\|f(x)⟩⟨x\|. Retain the existing n wires in order; the additional m−n wires are fresh. | In-range, pairwise distinct table outputs give V_f†V_f=I. For m=n, an injection between equal finite sets is a bijection and VV†=I. |
| `MeasureZ` | K_b=⟨b\|_q⊗I_R for b∈{0,1}; record b as classical output and end q. | Σ_b K_b†K_b=I_{qR}. Each branch b is CP and trace non-increasing. |
| `Discard` | For a width-k target register, hide z in K_z=⟨z\|_Q⊗I_R, z∈{0,1}^k. | Σ_z K_z†K_z=I and Σ_z K_zρK_z†=tr_Q(ρ). Identity when k=0. |
| `Reset` | End old q and create fresh q′. Hide b in J_b=\|0⟩_{q′}⟨b\|_q⊗I_R. | Σ_b J_b†J_b=I and Σ_b J_bρJ_b†=\|0⟩⟨0\|_{q′}⊗tr_q(ρ). |
| `ClassicalConst`, `ClassicalNot`, `ClassicalAnd`, `ClassicalXor` | Add a new bit to γ using constant, negation, conjunction, or exclusive-or truth tables; apply I to the quantum system. | One-outcome CPTP for each classical input. |

The current IR's `QuantumIf` checks two finite `UnitaryStep` sequences built
from the table's sealed gates at the same target-register width. Each sequence
composes `H/X/Z/T/Cnot/Toffoli` and `ScalarPhase`, with index ranges and
distinct control/target axes checked, and denotes an exact unitary U₀ or U₁.
The outer control wire is distinct from the target, and the operation means

```text
C = |0⟩⟨0|_c ⊗ U₀ + |1⟩⟨1|_c ⊗ U₁.
```

Orthogonality of the projectors gives
`C†C=|0⟩⟨0|⊗U₀†U₀+|1⟩⟨1|⊗U₁†U₁=I`, and similarly `CC†=I`.
Retain `ScalarPhase` as each Uᵢ's exact phase; do not identify operations
modulo a separate global phase in each branch. Even for target `Unit`,
`U₀=I, U₁=−I` acts as Z on the control. This differs from `ClassicalBranch`,
which selects according to a measurement result or other classical value.

For the table lift, injectivity gives isometry by
`V_f†V_f=Σ_{x,y}|x⟩⟨f(x)|f(y)⟩⟨y|=Σ_x|x⟩⟨x|=I`.
The table must have a value for **every input**. For example, the table
`[0,0]` sending both bit values 0 and 1 to 0 has `⟨V_f0|V_f1⟩=1` and
is not isometric.

<a id="applyunitaryの有限列"></a>

### Finite sequences in ApplyUnitary

The added `ApplyUnitary` is a flat `CircuitStep` sequence on an ordered
register. Each action is Hadamard or a finite-axis basis action
`M|x⟩=ζ^k(x)|p(x)⟩`, with `ζ=exp(iπ/4)`. The verifier checks p's totality,
range, and injectivity, `k(x)∈{0,…,7}`, and the distinctness/range of every
action axis. On equal finite carriers, p is bijective. The inner product of
columns is `conj(ζ^k(x)) ζ^k(y) δ_(p(x),p(y))=δ_(x,y)`, so
`M†M=MM†=I`. An action on no axes still retains a one-dimensional phase.

Controls form a projector Π specifying basis values on distinct axes;
overlap with action axes is rejected. For target operator V, the step is
`Π⊗V+(I-Π)⊗I`. Orthogonal projectors and `V†V=VV†=I` make this operator
unitary, and a product of finitely many such steps is unitary. Extend it by
identity on the external reference. Ownership consumes one input token and
returns a fresh token for the same ordered wire list.

This lemma concerns the ideal meaning of verified finite sequences.
Showing that source-body flattening, axis-order normalization, adjoint,
control, and repetition represent the intended original function is an
additional preservation obligation; unitarity alone does not establish it.
Finite tests and [transformation rules](static-operations.md) exist, but a
general machine-checked implementation-correspondence proof remains incomplete.

Each operator of `MeasureZ`, `Discard`, and `Reset` acts on arbitrary R and S
as K⊗I_S or J⊗I_S. This Kraus form gives complete positivity, and completeness
gives trace preservation of the sum. In particular, discarding one half of a
Bell pair leaves the other half in the mixed state given by the partial trace.
Separate ownership of distinct wires does not supply a product-state premise.

<a id="4-構造化した計算使用逆計算"></a>

## 4. Structured compute/use/uncompute

For `ComputeUseUncompute`, source has n bits, internal ancilla has a bits,
and targets is a list of distinct one-bit registers. Its function table
f:{0,1}^n→{0,1}^a must be total and in range, but need not be injective.
`C_f|x,y⟩=|x,y xor f(x)⟩` is unitary even for a noninjective f, and
`C_f†=C_f`.

The verifier permits only these three kinds of `use_ops`:

- `ProtectedGate` is Z or T on one source or ancilla bit. Both preserve the
  protected bit's computational-basis value and retain its phase.
- `ControlledTargetGate` applies H/X/Z/T to a separate target bit according
  to a protected bit's truth value. Its control predicate does not depend
  on the target's value; the action is unitary in every control block.
- `ControlledPhase` applies −1 or e^{iπ/4} according to conditions on protected
  bits. Retain the phase even when there are no targets.

Consequently, the sequence W of `use_ops` has the block-diagonal form
`W=Σ_{x,y}|x,y⟩⟨x,y|⊗V_{x,y}`, preserving the protected labels (x,y).
Each V_{x,y} is unitary on the targets. Protected-bit Z/T and
`ControlledPhase` multiply V_{x,y} by a complex phase; `ControlledTargetGate`
composes a target unitary in the relevant block. The induction holds with
multiple targets as well.

The whole structure consists of initialization, computation, use, and
uncomputation by the same C_f. For any x and target state |t⟩,

```text
|x,t⟩|0⟩ → |x,t⟩|f(x)⟩
         → |x⟩ V_{x,f(x)}|t⟩ |f(x)⟩
         → |x⟩ V_{x,f(x)}|t⟩ |0⟩.
```

By linearity, the final ancilla is exactly |0⟩ and separates from the rest
for arbitrary superpositions and inputs including a reference S. Removing
it leaves the effective map `U_eff=Σ_x|x⟩⟨x|⊗V_{x,f(x)}`, satisfying
`U_eff†U_eff=U_effU_eff†=I`. Extend by I_R on other live wires. If source
is `Unit`, there is only one x; if the ancilla has zero bits, f(x) is the
unique empty label. The same equations hold.

This proof does not rely on a text assertion that the ancilla should
“eventually be zero” or on a lifetime declaration. Making standalone
`Release0` a primitive would, for example, remove |1⟩ with ⟨0| and reduce
its trace to zero, violating both trace preservation and isometry. Rejecting
X/H as `ProtectedGate`, measurement/reset/discard of protected labels, and
uncomputation by a different function supplies the conditions for the
factorization above.

<a id="5-古典分岐と-φ-の補題"></a>

## 5. Classical branches and the phi lemma

The `condition` of `ClassicalBranch` is an existing `ClassicalId`. For a
classical environment γ, exactly **one** of then or else is selected; both
arms are checked from the same quantum input context. An input token can
therefore appear in both arms' syntax without being used twice on one
execution path. If the condition came from measurement, select the branch
separately for each post-measurement classical history.

Each `QuantumPhi` renames the i-th wire of the selected arm's output register
to the i-th wire of the phi output. Every live register maps one-to-one to
phi in each arm; corresponding widths agree, and phi output wires are
globally fresh and disjoint. The maps from arm outputs H(Δ_then), H(Δ_else)
to the shared H(Δ_φ) are positional renamings inside each register, with any
required overall axis permutations P_then, P_else. Each P is unitary: it
neither forces a product state, duplicates amplitudes, nor observes.
`ClassicalPhi` merely copies the selected arm's classical value to a fresh
SSA ID.

If each arm is isometric by induction, fixed γ selects only one V_arm, and
P_arm V_arm is also isometric. If both arms are unitary, the composition is
unitary. For an observation arm, left-multiplying each of its Kraus operators
by P_arm preserves completeness. If classical histories separated by a
measurement later share the same public b, sum their CP maps. **Phi merging
does not add amplitudes between arms**, so trace preservation of the sum
holds even when the condition depends on an earlier measurement result.

<a id="6-合成による証明"></a>

## 6. Proof by composition

**Resource induction.** At entry, `reserve_wire` reserves each port's wires
and `insert_token` inserts each token, excluding duplication. `consume`
checks target tokens for distinctness and liveness before consuming them.
Each ordinary constructor removes old tokens and then inserts disjoint
registers under fresh tokens. `reserve_wire` checks global freshness for
`Init0`, additional `LiftBasis` wires, `Reset`, and the internal ancilla of
`ComputeUseUncompute`. `Split/Join` only partition/concatenate wire lists.
The ancilla of `ComputeUseUncompute` is not an output token; it closes under
the static zero-return evidence above. Check each arm from a copy of the
same input **verification state**, requiring phi coverage of every live
token and fresh outputs. This copies no runtime quantum state. Finally,
check equality of `quantum_outputs` with the live set. Induction on the
finite operation sequence and branch tree gives Theorem A.

**Pure-map induction.** A single `Gate`, `Cnot`, `Toffoli`, same-width
injective `LiftBasis`, `Split/Join`, `QuantumIf`, `ApplyUnitary`,
`ComputeUseUncompute`, or classical operation is unitary for fixed γ.
`Init0` and width-increasing injective `LiftBasis` are isometries. Use the
previous section's lemma for classical branches. Isometries compose because
`(V₂V₁)†(V₂V₁)=V₁†V₂†V₂V₁=I`; unitaries compose to unitaries. Tensoring
local operations with I_R and I_S preserves these equations.

The verifier's derived effect is the join in `Unitary < Iso < Observe`.
`Init0` and **width-increasing** `LiftBasis` raise it to at least `Iso`;
`MeasureZ`, `Reset`, and `Discard` raise it to `Observe`. Branches take the
join of both arms. Thus sequences and all arms with derived effect `Unitary`
contain no nonunitary constructors; among lifts, only square injective
`LiftBasis` remains. A `unitary` declaration additionally checks equality
of input/output bit counts. However, **dimension equality alone** must not
be used to infer unitarity. Rejection of noninjective tables and measurement,
and the induction on effect joins, are necessary. This gives Theorem B.

**Instrument induction.** A pure V gives the one-outcome map E(ρ)=VρV†,
which is CPTP because V†V=I. Observation constructors satisfy the Kraus
completeness equations of Section 3. For a preceding history c with CP map
E_c and a subsequent result d with CP map F_{d|c} selected according to the
resulting classical environment, define `G_d=Σ_c F_{d|c}∘E_c` when only d
is public. Composition and finite sums of CP maps are CP, and

```text
Σ_d G_d = Σ_c (Σ_d F_{d|c})∘E_c
```

has the same trace as the input by completeness at each stage. For a fixed
d, G_d has nonnegative trace on positive inputs; because the total trace is
the input trace, each G_d is trace non-increasing. Use the exclusive-selection
lemma for classical branches. `ClassicalConst`, `ClassicalNot`,
`ClassicalAnd`, `ClassicalXor`, and `ClassicalPhi` only relabel or hide public
outcomes. Induction on finite sequences and branch trees gives Theorem C.
The same induction after tensoring every Kraus operator with I_S includes
entanglement with external references.

<a id="7-検証器から式への対応義務"></a>

## 7. Obligations connecting the verifier to the equations

| Required condition | Current code entry point | Mathematical role and remaining audit |
| --- | --- | --- |
| Linear tokens, distinct live wires, complete exit | `State::consume`, `insert_token`, and the `quantum_outputs` check in `verify` in `verify.rs` | Invariant of Theorem A. Implementation audit including branches, width zero, and state changes on failure is not mechanized. |
| Fresh wires and finite widths | `State::reserve_wire`, input-port checks, width limits, `check_table` | Fix the axes of local actions and total finite tables. The verifier does not bound the total number of live wires; the numerical executor has a separate limit. |
| Sealed gates and phase | `SingleGate`, `ScalarPhase`, `ProtectedUse` in `ir.rs` | Fix and audit correspondence between each enum value and the table's **exact** matrices. `sim.rs` uses `f64` approximation and is not a prover. |
| Coherent branches | `QuantumIf` checks and `UnitaryStep` index checks in `verify.rs` | Check both arms statically; interpret as `P₀⊗U₀+P₁⊗U₁` without measuring control. Retain branch phases. |
| Finite unitary sequences | `ApplyUnitary` / `check_circuit` in `verify.rs` | Check axis nonoverlap, total permutations, and phases 0–7. Corresponds to the orthogonal-column and orthogonal-control-block lemmas above. |
| Injective lifts | `check_table(..., true)` and `LiftBasis` wire-prefix/freshness checks in `verify.rs` | Derive V_f†V_f=I. Check raising the effect to `Iso` on width growth and bijectivity at equal width. |
| Measurement, discard, reset | Width, consumption, freshness, and `Observe` effect checks in `verify.rs` | The respective Kraus forms and completeness. Preserving mixed states in the Rust executor is a separate implementation obligation. |
| Structured auxiliary release | `verify_compute`, `check_table(..., false)`, `check_protected_bit`, `check_controls` in `verify.rs` | Sufficient conditions for W to preserve (x,y) and uncompute with the same C_f. Introduces no arbitrary `Release0`. |
| Branches and positional phi | `verify_branch`, `QuantumPhi`, and `ClassicalPhi` in `verify.rs` | Matching arm inputs, complete output coverage, and each phi's width/freshness. Keep `relabel_branch` in `sim.rs` as axis renaming, not addition of branch amplitudes. |
| Effects and `unitary` declarations | `State::effect`, declaration comparison and input/output bit-count comparison in `verify` | Prevent declaring `Observe` as pure or `Iso` as `Unitary`. Dimension equality is a side condition, not a standalone proof. |
| Public classical outputs | `classical_outputs` existence checks in `verify`, probability aggregation in `sim.rs` | Sum CP maps when hiding internal measurement histories. Read duplicate classical-output IDs as copies. |

Line-by-line equivalence between current code and these equations, an inductive
formal proof covering every implementation path, and verification of the
trusted base including Rust's type system/compiler are **incomplete**.
In particular, the reference executor runs closed programs using `f64` and
handles zero-weight branches and capacity limits; its output is not a proof
of Theorems B or C. The finite source `.qli` subset has type/effect/ownership
checking, translation to `RawProgram`, and static adjoint/control/repetition,
but a general proof of meaning preservation remains incomplete. Do not
automatically include source translation, general borrowing, or external
backend correctness in this IR theorem.

<a id="8-境界を示す反例と拒否"></a>

## 8. Boundary counterexamples and rejections

- `State::consume` rejects IR passing the same token as both `Cnot` control
  and target, or passing an already measured token to `Gate`. These are the
  resource nonduplication and lifetime checks.
- Omitting an `Init0` token from the outputs without an explicit operation
  is rejected by `verify`'s exit check. Disposing of it requires explicit
  `Discard` and effect `Observe`.
- The `LiftBasis` table `[0,0]` is total but noninjective and is rejected.
  In contrast, `[0,3]` can be accepted as the isometry |0⟩↦|00⟩,
  |1⟩↦|11⟩. This does not clone an unknown state as |ψ⟩↦|ψ⟩|ψ⟩.
- Effect comparison rejects declaring a program containing `Init0` as
  `Unitary`, or declaring `MeasureZ`, `Reset`, or `Discard` as `Iso`.
  In particular, equal total input/output bit counts do not permit hidden
  observation.
- `ComputeUseUncompute` rejects use operations that apply X/H to protected
  bits. `RawOp` has no standalone `Release0`. Merely owning one half of a
  Bell pair is not evidence for pure release.
- IR is rejected if one arm omits a quantum owner from phi, corresponding
  arm widths differ, or an output is mapped twice. Valid classical feedback
  using an already measured condition can be accepted together with the
  measurement's `Observe` effect.
