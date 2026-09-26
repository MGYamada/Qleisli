# Source values, calls, and branch semantics

Status: **semantic interfaces and conditional local paper proofs** (2026-09-26).
This English document supplies the semantic layer for the
[source resource rules](source-resource-rules.md) and [finite core v0](language-spec.md).
It introduces no syntax, primitive, acceptance rule, or standard-library API.
The local results below do not alone prove full source soundness or correctness
of the Rust compiler. [Q1–Q3](source-soundness.md) now assembles the ideal
soundness proof for the explicit rule system. S1–S4 are not Lean proofs.

The milestone is to state what a mixed source value denotes and prove how
call-by-value substitution, an arbitrary correlated frame, and classical
branch interfaces compose. Checking that every source rule and every Rust
execution meets these premises remains an explicit obligation.

## 1. Mixed values and ordered quantum interfaces

Use the exact ordinary type trees `T ::= Unit | CBit | Q<A> | (T,T)` and the
basis types of v0. Define a finite classical result set `C(T)` and an ordered
list of quantum basis leaves `Q(T)`:

| T | C(T) | Q(T) |
| --- | --- | --- |
| `Unit` | singleton | empty list |
| `CBit` | `{0,1}` | empty list |
| `Q<A>` | singleton | `[A]` |
| `(T,U)` | `C(T) × C(U)` | `Q(T)` followed by `Q(U)` |

These are semantic projections, not source type coercions. In particular,
`Q<Unit>` has one logical quantum leaf although its Hilbert space is
one-dimensional. `Unit`, `Q<Unit>`, and product trees remain distinct types.
The ordered quantum space `Hq(T)` is the tensor product of the leaf spaces;
an empty product is the scalar space. The basis label convention is
`label(a,b)=label(a)+2^bits(A)*label(b)` for `a:A` and `b:B`.
Tensor identifications send `|a> tensor |b>` to `|label(a,b)>`; no default
array-library or Kronecker ordering is assumed.

Let `R(s)=(A,t,w)` be the slot store of the resource rules, and let `gamma`
assign bits to visible classical SSA IDs. A symbolic value `v:T` determines:

- `class_gamma(v) : C(T)`: replace each classical leaf ID `c` by `gamma(c)`;
  unit and quantum leaves contribute their singleton value.
- `layout_R(v)`: the ordered list of quantum ports, obtained by traversing
  `v` left to right and reading each slot's exact basis and ordered wire list.

Neither projection reads a quantum amplitude. The quantum component of `v`
is an interface to the joint state, not a vector stored in the value. Repeated
classical IDs are permitted and give repeated bits. Repeated quantum slots
are rejected by the resource rules even if their wire lists are empty.

For environments, use lexical **binding identities**, including spent markers,
rather than textual names alone. A live binding contributes its value; a spent
binding contributes no owned port but still participates in name resolution.
The opaque frame `F` contains pending tuple fields, earlier actual arguments,
suspended caller values, and protected resources. Fix an explicit ordering of
live bindings and frame positions. Resource well-formedness makes their
quantum leaves an exact partition of `dom(R)`.

Choose any ordered enumeration `W` of the live physical wire IDs. The state
space is `H(W)`, and the layout supplies a coordinate isomorphism to the
ordered holder-interface space. Rearranging holders or grouping them into
pairs changes this isomorphism, not the physical state. Slot and token names
are ownership metadata; wire positions determine coordinates. A zero-width
leaf contributes no axis but remains in interface coverage checks.

## 2. Classical records and subnormalized joint states

An open semantic state is a finite family `gamma -> rho_gamma`, where each
`rho_gamma` is positive semidefinite on all live axes and an arbitrary finite
external reference space `K`, and `sum_gamma tr(rho_gamma) <= 1`. Different
classical records are classical alternatives. The family is equivalent to a
block-diagonal classical/quantum state; it is not a coherent superposition
of records. Registers in one block may be arbitrarily entangled with each
other or with `K`.

For a fixed classical input `gamma`, an expression derivation has branches

```text
E[e]_(delta | gamma) : L(H_in) -> L(H_out(delta)).
```

`delta` records the visible output classical values and the returned value's
classical projection. Hidden histories may be kept as additional indices and
summed when they are forgotten. A boundary's type fixes the output quantum
interface; individual histories may use different physical IDs. Transport
each history to that interface **before** summing density operators or CP maps.

All maps act on subnormalized states. The trace of a branch carries its
probability; evaluation does not divide by this trace, including at a branch
of probability zero. A fixed public result `b` has meaning

```text
E_public[b] = sum_(histories h with class(result_h)=b)
               Ad(P_h) composed with E_h,
Ad(P)(rho) = P rho P†.
```

Here `P_h` places the complete output in the common interface order. Forgetting
a classical result sums CP maps or density operators, never amplitudes.
Copying or discarding classical data only reindexes these records.

Keep an additional **exact linear operator** `V_gamma` for a pure derivation.
Its classical result is deterministic for fixed `gamma`, and its density map
is `Ad(V_gamma)`. Equality of these density maps does not determine global
phase. Pure-operator correspondence below requires equality of `V`, not just
of `Ad(V)`, because later coherent control may expose a relative phase.

## 3. Compositional interpretation and its premises

The resource calculus fixes successful derivations, evaluation order, accessible
names, exact types, and legal interfaces. The following equations interpret
their semantic structure. They do not provide a new source checker.

| Rule | Semantic action |
| --- | --- |
| Unit, classical copy, quantum move | Reorganize values/environments with identity on the physical joint state. Moving spends the original binding. |
| Pair | Evaluate the left expression; retain its entire result in `F`; evaluate the right expression; pair the resulting value trees. |
| `let` / pattern binding | Evaluate the right-hand expression once, destructure its resulting value, introduce fresh binder identities, then continue. A wildcard can forget only a classical footprint. |
| Block exit | Hide block-local names and unused classical records, restore surviving outer bindings, and propagate spent outer linear bindings. Do not trace out a live quantum resource on scope exit. |
| Normal call | Evaluate actuals once from left to right, bind those **values** to fresh formals in the callee module, and evaluate its body with suspended caller holders in `F`. |
| Classical `if` | Evaluate its condition first, select the arm for its bit, evaluate only that arm, then apply the simultaneous classical and complete quantum phi interface. |

Sequential evaluation uses finite adaptive composition. If the first stage
has maps `E_(delta|gamma)` and the continuation has `F_(eta|delta)`, then

```text
(F ⋆ E)_(eta|gamma) = sum_delta F_(eta|delta) composed with E_(delta|gamma),
```

after matching every intermediate quantum interface, including the frame.
Pending values remain in that interface; they cannot disappear when a later
argument calls a function or measures a different subsystem. Their conditional
state may change through correlations even though the later expression cannot
directly access their handles.

The semantic leaves are the exact sealed matrices and Kraus maps in the
[formal-core overview](formal-core.md#2-ideal-semantics-on-the-entire-system).
A basis lift uses its complete injection table. Static forms use their exact
phase-preserving operators; [F1–F5](static-semantics.md) proves the local
mathematical transformations for the accepted finite subset. A computed scope
uses its checked zero-return factorization. Local `discard` is a partial trace and `reset` discards the old
subsystem and prepares a new zero subsystem; neither is pure cleanup.

For the local proofs, require:

1. Successful resource premises: linear quantum actuals, exact result types,
   legal scope exit, complete result/frame coverage, and fresh generated IDs.
2. Resolved module/function identities and distinct lexical binders; the call
   graph is finite and acyclic. The callee cannot capture caller-local names.
3. Each semantic leaf is local to its accessible inputs, is equivariant under
   fresh renaming, and has the stated exact operator or instrument semantics.
   Static/computed evidence remains a prerequisite, not a consequence of
   ownership accounting.
4. For a **translation** conclusion, the translated immediate subderivations
   already agree with their source maps under the recorded layouts. Pure
   subderivations agree as exact operators. Applying this premise to all Rust
   lowerer paths has not been proved.

## 4. S1: value substitution at function boundaries

Suppose a declaration has formals `x_j:T_j`, return type `T`, and a well-formed
body. Evaluate actual expressions once, obtaining `v_j:T_j` and a joint state.
Let `sigma(x_j)=v_j`. Classical formals receive the actual bit values, allowing
aliasing: `f(b,b)` is valid. Formal quantum leaves correspond one to one to the
owned actual leaves, in parameter order. They cannot alias each other or the
frame. Alpha-rename local binders and generated IDs freshly; preserve resolved
declaration identities and the callee's module.

**Claim S1.** Evaluating the body with these formal bindings and evaluating
its capture-avoiding **value** instantiation have the same classical result
and quantum maps after their interface coordinates are identified. In the
pure case their operators are exactly equal. This is not substitution of
unevaluated actual expressions into each variable occurrence.

**Proof.** At a classical variable, both sides read the same assigned bit;
there is no requirement that different formal classical IDs have different
actual IDs. At a quantum variable, both sides designate the corresponding
single owned port and spend that binder. Unit and pair projections agree by
their definitions. For `let`, the induction hypothesis evaluates the right
side once; fresh lexical identities extend the two environments with matching
result values, and substitutions stop at shadowing binders. Scope exit removes
the same local holders and propagates the same spent outer bindings.

The local-map premise makes each sealed/certified leaf commute with the
interface identification. In a pair or argument sequence, the first induction
hypothesis puts matching pending values in the frame; the next hypothesis
acts on the same joint state. For `if`, both conditions return the same bit
record, so induction selects the same arm, followed by matching interfaces.
For a nested call, its declaration identity is unchanged and the call-graph
induction applies to the smaller dependency. These cases cover the structural
interpretation of §3; semantic leaves are covered by premise 3. The argument
works for each retained outcome map (and compatible refinements of private
histories) and exact pure operator; summing records preserves the equality.
It is conditional on the accepted derivation and leaf semantics,
not a proof of the implementation's snapshot or resolution algorithms.

## 5. S2: extension over a correlated frame

Let a body act on interface `A` and return `B`. For fixed classical inputs,
write an outcome map as `E_d(rho)=sum_k K_(d,k) rho K_(d,k)†`. Let `F` contain
the caller's remaining quantum interfaces, and let `K` be an external reference.
The correctly framed map is

```text
E_d with frame = E_d tensor id_(F tensor K),
K_(d,k) with frame = K_(d,k) tensor I_(F tensor K),
```

conjugated by the input/output layout permutations. **Claim S2:** this is the
meaning of a derivation that cannot access the frame, including when the input
is entangled across `A`, `F`, and `K`.

**Proof.** Semantic leaves have this locality by premise 3. Structural value
operations act as the identity on physical axes. Sequential composition obeys
`(L tensor I)(K tensor I)=(LK) tensor I`; adaptive composition distributes
over the finite outcome sums. Condition/arm selection depends on the available
classical record, not on direct access to framed quantum handles. Phi changes
frame coordinates through the layout isomorphism, retaining their port types.
Induction gives the displayed Kraus operators. Expand an arbitrary joint
operator as `sum_(i,j) |i><j|_A tensor R_(i,j)`; linearity gives the equation
without a product-state assumption. The same proof applies to exact pure
operators. Complete positivity is preserved, and Kraus completeness is
preserved whenever the original outcome family is complete.

This does **not** assert that a frame's normalized conditional state is
unchanged. Measuring one half of a Bell pair steers the other half to the
selected basis state. Only after summing a trace-preserving outcome family is
the frame marginal unchanged. Scope and ownership preservation alone cannot
justify a stronger statement or a pure release of an entangled auxiliary.

## 6. S3: classical branch and complete phi transport

Let the condition instrument be `C_(d|gamma)`, where `d` contains its returned
bit `b(d)` and retained classical record. In v0, bit 1 selects the then arm and
bit 0 the else arm. Let `A^i_(h|d)` be the selected arm's CP outcome maps, indexed
by retained arm-output classical records `h`, including the result projection.
First transport private histories to the fixed arm-output interface and sum
them within each such record. The source and IR need not have the same private
Kraus decompositions. No condition is re-evaluated.

Use the resource rules' correspondence `J` over **all** result quantum leaves
and residual frame slots. It is a bijection to the live slots in either arm;
matched leaves have equal basis trees and wire positions. The induced map
`P_i` transports the selected arm's complete output axes to the common
interface. It is unitary and extends by `I_K`. Zero-width slots participate
in `J` even though they contribute no axes to `P`.

Define `mu_i` on the selected arm's **frozen pre-merge** classical valuation:
all phi outputs read their chosen inputs from that valuation, simultaneously.
Retain parent-visible records, hide arm-local IDs, and export the result tree.
A shared classical ID may bypass a phi only if it was already parent-visible.
Duplicated classical results remain legal; a phi output cannot feed a sibling
phi in this same merge.

**Claim S3.** For public output `o`, the branch meaning is

```text
E_if[o | gamma] =
  sum_(d,h : mu_b(d)(d,h) exports o)
    Ad(P_b(d)) composed with A^b(d)_(h|d) composed with C_(d|gamma).
```

**Proof.** The condition first produces subnormalized records `d`. Runtime
selection uses exactly one arm for each record. Arm evaluation gives the
subnormalized retained records `h`. Complete position-wise phi coverage
transports each record by `P` without copying, tracing out, or preparing quantum
state. The frozen classical substitution gives exactly `mu`; grouping retained
records by `o` sums their CP maps, with private histories already summed. This
proves the equation. Under premise 4, source and IR agree for each retained
outcome map and therefore after the finite sum. Unitary
conjugation preserves trace and CP; adaptive composition of complete condition
and arm instruments proves completeness of the sum over `o`.

If the condition and arms are pure, fixed classical input gives a single
reachable record and selected arm. The exact operator is
`P_i V_arm V_condition`, with intermediate layout identifications understood.
Equality of density maps alone would be insufficient for that stronger claim.
The theorem neither coherently adds the two arms nor replaces classical `if`
with `qif`. Different arm wire IDs, new allocations, reset, and returned
permutations are allowed only when the full resource/phi premises hold.

## 7. S4: local source-to-IR composition

Let `J_in` and `J_out` be the source-to-IR coordinate isomorphisms at a checked
boundary, and let classical SSA decoding agree with the source projections.
The desired correspondence for each output record is

```text
E_IR composed with Ad(J_in) = Ad(J_out) composed with E_source,
V_IR J_in = J_out V_source                         (pure operators).
```

**Claim S4:** assuming premise 4 for immediate subderivations and the resource
interfaces, the following structural translations preserve these equations:
pair/argument sequencing, pattern binding and block exit, normal call inlining,
and classical `if` with complete simultaneous phis.

**Proof.** Structural moves/bindings add no physical instruction. Intermediate
coordinate isomorphisms cancel in a sequence, and finite sums distribute over
composition. S1 identifies parameter binding with value instantiation; S2
extends the body equality over every suspended caller or pending-value axis.
S3 identifies selected-arm maps, output coordinate transport, and classical
decoding. Thus each structural case commutes, including arbitrary references.
Pure cases use exact operator equations throughout, so no phase is quotiented
away. This proves the local compositional rule. It does not discharge every
semantic leaf, static compiler transformation, or Rust data-structure invariant;
using it as an unconditional theorem about all compiled programs would omit
those premises.

## 8. Implementation audit and evidence

| Semantic obligation | Current implementation | Evidence and boundary |
| --- | --- | --- |
| Actuals are values, evaluated once in order | `expr_inner` and `call_user_inner` in [lower.rs](../src/frontend/compile/lower.rs) | Argument values are collected before parameter binding. Classical aliasing is permitted; quantum values move. |
| Callee module and lexical isolation | `call_user_inner`, `block`, `bind` | A fresh parameter environment and callee module are used. Block snapshots and the `rebound` set implement scope bookkeeping; their general adequacy remains open. |
| Pending/caller frame | Shared `Lowerer::registers`, `branch` | Registers outside the callee environment still participate in complete branch merging. The compiler does not infer a product state. |
| Ordered mixed outputs and complete phi | `merge_results`, `merge_register`, `branch` | Result trees are traversed before residual slots, including zero-width slots. [verify.rs](../src/verify.rs) independently checks full coverage. |
| Simultaneous classical substitution | `verify_branch` in `verify.rs` | All inputs are checked before any output is registered. Sequential assignments in [sim.rs](../src/sim.rs) are equivalent because verified outputs are globally fresh and cannot be inputs to this merge. |
| Axis order and history sum | `relabel_branch` and final probability aggregation in `sim.rs` | Selected wire IDs are relabeled; hidden classical histories contribute probabilities. Numerical execution is finite-precision evidence, not an exact operator proof. |

Regression evidence is in [tests/source_semantics.rs](../tests/source_semantics.rs),
alongside the seven `resource_rules_` tests in [tests/compile.rs](../tests/compile.rs)
and the independent malformed-IR tests:

| New regression | Observable contract |
| --- | --- |
| `measured_actual_is_evaluated_once_before_classical_substitution` | One X-basis measurement of a Bell half is passed as two aliased classical actuals; all three returned bits agree, each outcome having probability 1/2. |
| `call_substitution_respects_callee_scope_and_restores_shadowed_classical_names` | Four fixed input combinations distinguish callee declaration resolution from a caller-local name and preserve the outer classical binder after an arm-local shadow. |
| `nested_call_preserves_conditional_phase_against_an_entangled_caller_frame` | Nested mixed calls select T or ZT on a Bell half. Recombination tests the analytic joint weights `(2 ± sqrt(2))/8`, detecting lost relative phase or correlations. |
| `simultaneous_phi_order_preserves_mixed_results_zero_width_and_bell_coherence` | Reversing the three classical and three quantum phi entries, then independently reverifying, preserves the expected mixed output and interference, including a zero-width result and caller frame. |

The first three compare wrapped and expanded source arrangements against
independently expected distributions; the fourth checks both original and
reordered verified IR. Numerical comparisons use tolerance `1e-12`. They do
not establish equality on arbitrary input operators, and source edits were
not needed to make these regressions pass.

Local validation on 2026-09-26: all four new regressions passed; all 119 Rust
tests, formatting, and Clippy with warnings denied passed. Documentation checks
found no missing local link targets. The translated normative specification
retains its title and 11 legacy section anchors. These checks are implementation
and documentation evidence, not machine checking of S1–S4. Lean is unchanged.

## 9. Remaining specification work

| Result | Status after this milestone |
| --- | --- |
| Mixed values, environments, ordered interfaces, subnormalized classical records | Defined here for successful resource derivations |
| S1 value substitution, S2 correlated frame, S3 branch/phi, S4 structural IR composition | Conditional local paper proofs above |
| Finite flattening, output order, inverse/control/repetition, restricted computed phase | [F1–F5](static-semantics.md) supplies conditional local paper proofs and exact finite matrix regressions |
| Type/effect/name and scope rules for all syntax cases | [Explicit supplement and local T1–T3 proofs](source-typing-rules.md); full source/Rust adequacy of binder identities, scopes, snapshots and effects remains open |
| Every source/IR semantic leaf and static lowering meets the correspondence equation | Open; assemble the local proofs and establish all source typing/layout premises and Rust implementation adequacy |
| Ideal soundness of the explicit source rule system | [Paper Q1–Q3](source-soundness.md), using complete holder interfaces, exact leaves and finite adaptive Kraus composition |
| General correspondence to Rust acceptance and correctness of lowering/verifier paths | Open; not inferred from the paper theorem or finite tests |

The next task is to discharge the remaining leaf-translation premises and
establish implementation adequacy for the explicit derivations and Q1–Q3.
Lean supports the resource model and a small Kraus algebra component; it does
not yet check these source semantic proofs. Algorithm
correctness, backend behavior, and physical noise remain separate topics.
