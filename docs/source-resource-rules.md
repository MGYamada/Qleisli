# Source resource rules for finite core v0

Status: **SPEC-3 resource formalization, with a paper proof for the rules below**
(2026-09-26). This English document is the authoritative statement of this
resource calculus. The [formal-core overview](formal-core.md) provides
motivation and the remaining quantum soundness obligations. This formalization
draft is intended to account for the accepted forms of [v0](language-spec.md);
it adds no syntax, primitive, public API, or new acceptance rule. Acceptance
remains governed by v0; any discovered mismatch must be recorded and resolved,
rather than silently changing the language through this calculus.

The result proved here is preservation of ownership accounting by successful
derivations of this calculus. The complete calculus below has not been machine
checked. A separate [Lean development](lean-resource-proof.md) checks its
ownership-accounting projection, with explicit scope limits. Neither result
proves that every Rust execution implements these rules or establishes
source-to-IR quantum meaning preservation. The [source semantics](source-semantics.md)
adds value/environment interfaces and conditional local call/frame/phi
preservation lemmas. The correspondence table below is an implementation
audit supported by finite regression tests. SPEC-3 and SPEC-4 remain open.

The [type/effect/name supplement](source-typing-rules.md) now states all current
syntax cases and declaration/scope premises, with local paper lemmas T1–T3.
Together these documents present the finite rule system; completeness by
syntax cases does not prove its adequacy for every accepted Rust execution.

## 1. Types, values, and ownership occurrences

Use exact type trees, without implicit associativity or unit isomorphisms:

```text
A ::= Unit | Bit | (A,A)                 basis types
T ::= Unit | CBit | Q<A> | (T,T)         ordinary types
C ::= Unit | CBit | (C,C)                classical types
effects: Unitary <= Iso <= Observe
```

`bits(Unit)=0`, `bits(Bit)=1`, and `bits((A,B))=bits(A)+bits(B)`.
`lin(T)` holds exactly when the tree contains `Q`. A symbolic ordinary value is

```text
v ::= () | c | q(s,A) | (v,v)
```

Here `c` is a classical SSA identifier, and `s` is a register **slot**, not an
amplitude, a wire, or an SSA ownership token. Its type is `Q<A>`. Slots allow a
pending source value to survive a branch that renames its IR token and wires.
The store `R(s)=(A,t,w)` gives its current basis type, token `t`, and ordered wire
list `w`, with `length(w)=bits(A)`.

Define the multiset of ownership occurrences:

```text
own(()) = own(c) = empty
own(q(s,A)) = [s]
own((v1,v2)) = own(v1) + own(v2)
```

The use of a multiset is essential: `[s,s]` is invalid even if `R(s)` has zero
wires. A mixed value such as `(c,q(s,A))` moves as a whole. After destructuring,
its classical component can be copied independently.

An environment `E` maps each visible local name to a binding with a unique
lexical identity, type, and either a live value or a **spent marker**. Spent
bindings still hide top-level functions. A new `let` has a new lexical identity
even when its spelling and register slot are unchanged. The classical live
bindings are the usual `Gamma`; live bindings of linear type are `Delta`.
Keeping them in one environment also accounts for mixed values and shadowing.

`F` is a list of opaque, pending values: earlier tuple fields, earlier call
arguments, the suspended caller's live bindings, and protected resources.
Source names cannot access `F`. Classical components in it are harmless;
quantum occurrences must be accounted for. `own(E)` counts only live values.

The assertion `WF(E,F,R)` means:

1. `own(E)+own(F)` contains each slot in `dom(R)` exactly once and no other slot.
2. Every quantum occurrence agrees with its store basis type; value and binding
   type trees agree. Every classical leaf is visible in its current SSA scope.
3. Store tokens are distinct; each wire list has the required length, has no
   repeated wire, and is disjoint from every other live wire list.

This is an ownership assertion. It imposes **no factorization** on the quantum
state. Distinct slots, tokens, or wires may describe entangled subsystems.

A history `H` records issued tokens, wires, slots, and classical IDs. A fresh
allocation uses an identifier outside the corresponding history. History is
shared across both checked arms of a branch. Classical IDs additionally have
lexical IR scopes: a child arm's IDs cannot be read in its sibling or parent
except through the merge specified below. Mathematical IDs are unbounded;
Rust capacity limits are a separate rejection policy.

## 2. Judgments and evaluation order

With a resolved, acyclic declaration environment `D`, write

```text
D ; E ; F ; R ; H |- e => v : T ! eps ; E' ; R' ; H'
```

for a successful checked elaboration. Its output ownership assertion is
`WF(E', F ++ [v], R')`. This assertion is a theorem of the rules, rather than a
permission to silently remove an unmatched resource. The rules construct the
output and reject missing or duplicate ownership. The frame values `F` keep
their slots and type trees; store metadata for them may be renamed by a branch.

An elaboration also emits a finite IR fragment. Write `I1;I2` for concatenation.
No IR is emitted by a name move, classical copy, pattern binding, or tuple
construction. Resource transitions below specify which IR constructors are
emitted. Effects join by maximum, starting at `Unitary` for an empty sequence.
Declarations are checked in dependency order; all declarations and both arms
are checked, including targets of zero repetitions.

### Values and tuples

`UNIT` returns `()` and leaves all contexts unchanged, with effect `Unitary`.
`COPY` returns a live classical binding's value without modifying `E`.
`MOVE` returns a live linear binding's entire value and replaces that binding
by its spent marker. A missing or spent value name is rejected.

The tuple rule explicitly retains its first result during the second premise:

```text
E0 ; F        ; R0 |- e1 => v1:T1 ! eps1 ; E1 ; R1
E1 ; F ++ [v1]; R1 |- e2 => v2:T2 ! eps2 ; E2 ; R2
---------------------------------------------------------------- PAIR
E0 ; F        ; R0 |- (e1,e2) => (v1,v2):(T1,T2)
                                      ! max(eps1,eps2) ; E2 ; R2
```

`D` and sequentially threaded histories are suppressed in inference displays
only. The same left-to-right rule evaluates an argument list, adding all prior
results to `F` while evaluating the next argument. This includes quantum
temporaries that no longer have a live name in the caller.

### Patterns, statements, and scope exit

`BIND(p,v,E)` is the following partial operation. It moves `v` out of the pending
results and into the bindings introduced by `p`.

- A name installs the value with a fresh lexical identity. It may replace a
  classical binding or a spent marker, but not a live linear binding.
- `_` is defined only when `own(v)` is empty.
- `(p1,p2)` requires `v=(v1,v2)` and applies the operation recursively, from
  left to right. Names in the **whole** pattern must be distinct.

Thus `let q=h(q);` first spends the old binding, then installs the new one.
`let q=init0();` cannot shadow an unconsumed `q`.

For `let p=e; rest`, elaborate `e`, apply `BIND`, then elaborate `rest` in the
new environment. For `e; rest`, require `own(v)=empty` before continuing. The
effects are joined in both cases. Every block must have a final expression.

At block entry, save the visible binding identities. At exit:

1. Every live linear binding installed within the block must have been moved
   into the final result or explicitly consumed. A leftover local is rejected.
2. Each original linear binding remains live only if that same lexical binding
   survived unspent. Otherwise propagate a spent marker to the outer scope.
3. Remove local bindings and restore outer classical bindings. Do not restore
   a consumed outer quantum value when a shadowing local goes out of scope.

These rules describe scope exit even when a local has the same name, type, and
slot as the original binding. Returning a local is permitted; leaving it behind
is not. The result and the surviving outer bindings are separate holders.

## 3. Basis judgments and primitive transitions

Basis expressions use only `Xi |-basis b : A`. Variables in `Xi` are copyable
basis labels, never ordinary quantum handles or `CBit` values. The rules for
`()` and `0/1` give `Unit` and `Bit`; pairing gives the exact product tree;
`not` requires one `Bit`; `and/xor` require two `Bit` operands and return `Bit`.
A basis call requires matching parameter trees and returns its declared basis
type. Its name must resolve to a basis declaration and must not be a local
basis variable. All bodies are checked. Induction over the finite acyclic call
graph and expression trees makes these functions total on their finite domains.

A coherent lift first elaborates its ordinary input `q(s,A)`. It checks the
basis expression in the **isolated** environment `Xi={x:A}`, obtaining `B` and
a total table `f:A->B`. It requires distinct table outputs. No surrounding
ordinary binding can be captured. The label convention is
`label(a,b)=label(a)+2^bits(A)*label(b)`.

After argument elaboration, a primitive checks its full source type and arity.
Each listed input slot occurs once in its pending argument values, and different
arguments cannot alias. All unused store entries remain in the frame. In this
table `t'`, new slots, and new wires are fresh; consumed IR tokens are not reused.

| Rule / sealed name | Store and value transition | Effect / emitted IR |
| --- | --- | --- |
| `INIT / init0()` | Add `s:(Bit,t',[w'])`; return `q(s,Bit)`. | `Iso / Init0` |
| `GATE / h,x,z,t` | Require `q(s,Bit)`; replace its token and keep its wire and slot. | `Unitary / Gate` |
| `CNOT / cnot` | Two `Q<Bit>` inputs; refresh both tokens; return `(control,target)`. | `Unitary / Cnot` |
| `TOFFOLI / toffoli` | Three `Q<Bit>` inputs; refresh all tokens; return `((a,b),target)`. | `Unitary / Toffoli` |
| `SPLIT / split` | Remove `s:Q<(A,B)>`; add fresh slots/tokens for the prefix of length `bits(A)` and the remaining suffix; return their pair. | `Unitary / Split` |
| `JOIN / join` | Remove two distinct slots of types `Q<A>,Q<B>`; add one slot/token with type `Q<(A,B)>` and concatenated ordered wires. | `Unitary / Join` |
| `LIFT / do/pure` | At the input slot change `A` to `B`, refresh its token, and append `bits(B)-bits(A)` fresh wires. Return `q(s,B)`. Require the checked injection above; shrinking is impossible for such finite bases. | Same width: `Unitary`; growing: `Iso / LiftBasis` |
| `MEASURE / measure_z` | Remove the `Q<Bit>` slot; return a fresh visible classical ID. No quantum result. | `Observe / MeasureZ` |
| `RESET / reset` | Remove the `Q<Bit>` slot; return a fresh slot/token with a new logical wire of type `Bit`. | `Observe / Reset` |
| `DISCARD / discard` | Remove a `Q<A>` slot; return `()`, including when `A=Unit`. | `Observe / Discard` |

Input expression effects are joined with the indicated effect. Slots removed
by `SPLIT/JOIN` are consumed handles, not dropped wires. `MEASURE`, `RESET`, and
`DISCARD` explicitly end logical wires. No rule silently weakens a quantum value.

## 4. Function boundaries and frames

A normal declaration has signature `(T1,...,Tn) -> T ! eps_decl`. Its parameters
have distinct names and ordinary types. Start its independent check with fresh
symbolic inputs of those types, an empty frame, and exactly their quantum slots
in `R`. Elaborate its block and require:

- The returned tree has exactly type `T`.
- No parameter or local linear binding remains live.
- The body's effect is at most `eps_decl`.

For `CALL`, resolve a function name that is not hidden by any local binding,
including a spent one. Evaluate actual arguments left to right and check the
declared arity and exact types. Move the actual values into the callee parameter
bindings; do not clone linear arguments. The callee can access these parameters
and its module's declarations, not the caller's names. Its opaque frame is

```text
F_callee = F_caller ++ values of the caller's remaining live bindings
```

The pending actual arguments are removed from that frame when installed as
parameters. After checking the body, return its result to the caller and restore
the caller environment. Store metadata for framed slots follows any branch
merges performed by the callee. The call's effect is `eps_decl`, joined with
argument effects, even when the body's derived effect is smaller.

**Frame statement.** Elaborating a body cannot operate on an opaque frame slot,
spend its holder, or change its basis type. It can rename its token and wire IDs
at a classical merge. Such renaming is propagated through `R`, so suspended
values still designate the same subsystem. This includes earlier actual
arguments, earlier tuple fields, and a caller's resources entangled with callee
inputs. It does not assert that their joint state is a product.

## 5. Classical branches and simultaneous phi interfaces

`IF` first elaborates the condition and requires `CBit`. Let its resulting
contexts be `(E,F,R,H)`. Check each arm as a block from the same `E,F,R`.
Accumulate freshness history across the checks, so IDs created in one arm
cannot be allocated by the other. Cloning checking contexts is not copying a
runtime quantum state.

For arm `i` let the outputs be `vi:Ti`, `Ei`, and `Ri`. Require:

1. `Tthen=Telse` as type trees.
2. The set of original linear **binding identities** marked spent is equal in
   both arms. Block scope exit has removed locals and checked their ownership.
3. Traverse result trees left to right and pair quantum leaves by tree position
   and basis type. Each pair gets a fresh result slot, fresh token, and fresh
   ordered wires of the common width. Remove the paired slots from each `Ri`.
4. All remaining slots must be the same entry slots in both arms, with the same
   basis types. Match each such frame slot to itself. Keep its slot identity,
   but assign it a fresh token and fresh ordered wires.
5. Every arm's live slot must occur exactly once in these correspondences.
   No leftover branch-local slot and no repeated result leaf is permitted.

Let `J` index these correspondences. For each selected arm `i`, the maps

```text
j -> input slot s_i(j)      : J bijects onto dom(Ri)
j -> output slot s_out(j)   : J bijects onto dom(Rout)
(j,k) -> k-th wire of R_i(s_i(j))
```

induce a bijection of the live wire axes to the corresponding output axes.
An element of `J` with width zero still gets a token and participates in slot
coverage, although it contributes no axes. Pairing only by wire sets would lose
this linear obligation.

For classical result leaves, a shared ID already visible before the branch may
be reused. Otherwise allocate a fresh classical phi result, with its input
from each arm's visible scope. Validate **all inputs before installing any
outputs**; one phi cannot read a sibling phi's output. Parent classical IDs
remain visible and arm-local IDs become hidden. Classical duplication in a
result is allowed. A quantum result and its frame cannot share a slot.

The output environment is the common residual outer environment. Emit one
`ClassicalBranch` with both fragments and these quantum/classical phis. The
effect is the maximum of the condition and both arms, whether or not a runtime
condition happens to be constant. Result slots may pair different original
wires: `if c {(a,b)} else {(b,a)}` is valid for matching types. In contrast,
`if c {a} else {b}` spends different outer bindings and is rejected.

### Axis meaning of the merge

For a selected arm, let `pi_i` be the wire-axis bijection above and `P_i` its
permutation matrix in the fixed input/output tensor order. Then
`P_i† P_i = I` and `P_i P_i† = I`. The merge acts as

```text
rho_i -> P_i rho_i P_i†
```

on that arm's complete live system. For an external reference `S`, replace
`P_i` by `P_i tensor I_S`. No product-state premise is used. Different classical
histories that give the same public output contribute a sum of CP maps, never
a sum of their state-vector amplitudes. This establishes the axis-renaming
lemma for this interface, not general correctness of `sim::relabel_branch`.

## 6. Static operations and the computed scope

`STATIC` requires a statically resolved `unitary` declaration with exactly one
`Q<A>` parameter and the same result, or a sealed `h/x/z/t` on `Q<Bit>`.
The body and its resource boundary are checked even for repetition zero.
`adjoint` and `repeat_static` take and return one input slot of the same type,
refreshing its IR token. Their checked finite circuit has no allocation,
measurement, reset, or discard. `qif` evaluates its control before its target,
retains the first as a pending value, requires `Q<Bit>` and `Q<A>` on disjoint
slots/wires, and checks both static branches. It returns their ordered pair.
The implementation uses `Join; ApplyUnitary; Split`, so result slots can be new
while the logical wire axes are retained. All three forms have `Unitary` effect
in addition to input effects. Circuit axes, controls, total permutations, and
phase exponents must pass independent IR verification. Operator equality with
the source function is a separate SPEC-4 obligation.

`COMPUTED` first elaborates `q(s,A)`, resolves a basis function `f:A->Bit`, and
checks its total table. Multiple basis parameters are packaged as a left
associated product; zero parameters give `Unit`. Local names, even spent ones,
hide candidate predicate names. No injectivity of `f` is required here.

For checking the body, put the source and all surrounding quantum values into
an opaque frame. Copy only classical outer bindings into its visible
environment; preserve other outer names as unavailable markers. Introduce a
fresh auxiliary slot `a:Q<Bit>` with a private initial token and wire. The body
must have effect at most `Unitary`, leave no local ownership, return that exact
auxiliary slot, and emit only a connected `Z/T` token chain on it (possibly
empty) after ordinary call expansion. Branches, other gates, static transforms,
and access to outer quantum values fail this certificate.

Checking this private body does not expose a free-standing auxiliary release.
Replace the entire private construction by one `ComputeUseUncompute`, refresh
the source token, and return its original slot. Its internal zero return is
justified by the following **exact** lemma. With `z` Z gates, `t` T gates,
`k=(4z+t) mod 8`, and `C_f|x,b>=|x,b xor f(x)>`,

```text
C_f† W C_f |x,0> = exp(i*pi*k*f(x)/4) |x,0>.
```

The equation holds for every basis input, extends linearly and under any
reference identity, and factors out `|0>` on the auxiliary. Thus this atomic
certificate can close its private slot. Lifetime alone is not evidence.
The more general protected target operations of raw IR are outside this source
rule. This local lemma does not prove the entire source quantum semantics.

## 7. Resource preservation theorem and proof

**R1 (ownership accounting).** Suppose `D` is finite and acyclic, primitive
transitions and the atomic computed certificate are exactly those above, and
`WF(E,F,R)` holds. For any successful finite expression derivation with result
`v:T`, residual environment `E'`, and store `R'`:

1. `WF(E',F ++ [v],R')` holds, and the opaque frame keeps its holders and types.
2. Every emitted transition consumes only distinct live input tokens; every
   newly issued token is fresh. Every live wire belongs to exactly one register.
3. Each slot ends only by an explicit transition, by structural regrouping, or
   by a complete branch renaming. Each private auxiliary ends only inside its
   checked atomic certificate. There is no implicit loss or duplicate holder,
   including for `Q<Unit>`.

Freshness and well-scoped classical visibility are included in this theorem.
The statement concerns successful derivations; it makes no claim that an
arbitrary rejected Rust computation leaves an inspectable partial store.

**Proof.** Use induction on dependency order for function bodies, and mutual
structural induction on expression, argument-list, pattern, and block
derivations within a body. The induction order is well founded: every call
uses a strictly earlier declaration, and all other premises use smaller syntax
or a finite sequence. Static body checks use that same declaration order.

- `UNIT` adds no occurrence. `COPY` adds no quantum occurrence because its
  type is classical. `MOVE` removes the complete multiset of occurrences from
  one binding and places exactly that multiset in the result. It cannot read a
  spent marker. Store metadata does not change in any of these cases.
- For `PAIR`, the first induction hypothesis partitions `R1` among `E1`, `F`,
  and `v1`. Hence the second premise begins well formed with `v1` in its opaque
  frame. Its induction hypothesis partitions `R2` among `E2`, `F`, `v1`, and
  `v2`. Pair construction only groups the last two holders; it cannot repeat a
  slot. Induction on list length proves the same fact for arguments.
- Pattern induction partitions a pair's occurrences between its components.
  The distinct-name check prevents overwrite within a pattern; the live-linear
  shadowing check prevents overwrite of prior ownership. `_` removes no quantum
  occurrence. Thus binding redistributes occurrences exactly. Expression
  statements remove only empty occurrence multisets. Block induction composes
  these steps. Its exit check forbids leaving a local quantum holder behind;
  restoring classical bindings adds no ownership, and spent outer bindings
  remain spent. The final result therefore completes the residual partition.
- For a primitive, the induction hypothesis for the argument list gives
  distinct live slots disjoint from the rest of the store. `GATE/CNOT/TOFFOLI`
  refresh tokens on the same disjoint wire lists. `SPLIT` partitions a list
  and `JOIN` concatenates disjoint lists, each exactly once. `INIT` introduces
  fresh ownership and wires. `LIFT` retains its list and appends fresh wires;
  its updated value has the new basis type. `MEASURE/DISCARD` remove precisely
  the explicit input; `RESET` replaces precisely that input by fresh ownership.
  Token freshness and the stated type checks give all three conclusions. These
  arguments use slot multiplicity even when the wire list is empty.
- At a call boundary, moving actual values into parameters preserves the
  partition, while the caller's remaining bindings move into the opaque frame.
  The declaration induction hypothesis applies to the body. Its exit condition
  leaves only its result and that frame. Restoring the caller's holders is the
  inverse redistribution. Frames may have new metadata, but preserve slots
  and types, so no caller value becomes stale. Argument effects and the declared
  call effect cannot hide a stronger body effect.
- For `IF`, each arm's induction hypothesis supplies a partition of its own
  store. Equal consumption sets give one residual outer environment. Result
  traversal covers each returned quantum occurrence once. Removing those
  occurrences leaves exactly the surviving environment and opaque frame.
  Matching those entry slots covers every remaining occurrence. Thus the
  bijections indexed by `J` consume each live arm token once and construct each
  output slot once. Fresh tokens and disjoint fresh wires yield the output
  partition, including zero-width entries. History is shared, so identities
  allocated in separate arms cannot collide. Classical inputs are checked
  before outputs, and arm scopes are hidden after the merge; visibility and
  freshness therefore hold. At runtime only one arm is selected, so alternative
  syntactic uses of an input never become two uses along a single path.
- Static forms consume the checked inputs and return exactly their wire
  interface with new tokens. Each independently checked circuit step has
  disjoint action/control axes and does not allocate or destroy wires. The
  enclosing `Join/Split` for `qif` has the structural case already proved.
  Repetition is finite; zero repetitions still return ownership once.
- The computed body's induction hypothesis accounts for its auxiliary and
  inaccessible outer frame. Its final-slot and gate-chain checks restrict
  all token updates to the single auxiliary. The exact zero-return equation
  licenses closing that private slot as part of the atomic constructor; the
  output source and every framed holder survive. No standalone release rule
  is available to this induction.

These cases exhaust the v0 expression and statement forms. Sequential history
extension preserves freshness; only the branch case changes frame metadata,
and it keeps frame slots and types. This proves R1. The circuit and auxiliary
premises are explicit local certificate requirements, not inferred from mere
ownership or floating-point examples.

**Boundary corollary.** A successfully checked declaration returns every live
quantum slot exactly once in its result: apply R1 with an empty initial frame
and the declaration exit check. A closed `observe fn main()->C` with classical
`C` therefore leaves no live quantum slot. This proves resource closure of the
rule system, not normalization of the numerical execution's probabilities.

## 8. Implementation audit and regression evidence

The implementation uses `Option<Value>` tombstones and block snapshots plus a
`rebound` set instead of explicit lexical binding IDs. Its slots are `u32` keys
in `Lowerer::registers`; IR tokens/wires live only in the register metadata.
The pending frame is implicit: registers not held by the current environment
or expression result remain in that map. These representations are central to
the following audit; their general equivalence to R1 is still unproved.

| Rule or obligation | Implementation | Evidence / remaining boundary |
| --- | --- | --- |
| Exact types, occurrence distinction | [compile/mod.rs](../src/frontend/compile/mod.rs) `Ty`; [lower.rs](../src/frontend/compile/lower.rs) `Value::owns_quantum`, `quantum` | Existing mixed-value and `Q<Unit>` rejection cases. Wire width does not replace source type equality. |
| MOVE/COPY, pattern and block exit | `expr_inner`, `bind`, `block`, `no_owned_bindings` | `resource_rules_reject_lost_or_differently_consumed_bindings`; explicit `rebound` detects same-name/same-slot rebinding. |
| Pending argument / tuple frame | `expr_inner`, `call_user_inner`, `branch` | `resource_rules_pending_mixed_argument_survives_nested_call`, `resource_rules_pending_tuple_field_survives_branch`; Bell correlations tested after recombination. |
| Mixed branch result positions | `branch`, `merge_results` | `resource_rules_mixed_branch_results_follow_positions`; both choices, classical duplication, and output permutation checked. |
| Empty-wire ownership in phis | `merge_results`, `merge_register`; [verify.rs](../src/verify.rs) `verify_branch` | `resource_rules_zero_width_result_and_frame_are_both_merged` checks a zero-wire result plus a live caller frame. |
| Old vs branch-created wires | `branch`, `merge_register`; [sim.rs](../src/sim.rs) `relabel_branch` | `resource_rules_reset_branch_keeps_reference_and_classical_history` checks the correlated frame when one arm ends a logical wire. |
| Classical scope and simultaneous phi inputs | `merge_results`; `Global`, `verify_branch` in `verify.rs` | `resource_rules_nested_classical_results_keep_their_scopes`, existing `classical_phis_cannot_read_outputs_of_the_same_merge` and `nested_classical_phi_is_visible_in_its_parent_arm`. |
| Actual parameters, conservative effects | `call_user_inner`, `lower_function` | Existing argument-location, effect, and unused-body tests; no substitution proof for the Rust implementation yet. |
| Basis isolation and atomic auxiliary | [basis.rs](../src/frontend/compile/basis.rs) `eval_basis`; `lift`, `computed` in `lower.rs` | Existing `finite_v0_basis_lifts_are_injective_and_closed` and `finite_v0_computed_blocks_require_the_structural_certificate`. |
| Static certificate boundary | `static_steps`; [circuit.rs](../src/frontend/compile/circuit.rs) `flatten`, `invert`; `check_circuit` in `verify.rs` | [Static judgments](static-operations.md#static-target-judgment), [local exact-operator proofs F1–F5](static-semantics.md), phase/rejection tests, and exact finite matrix regressions. Full source/Rust meaning preservation remains SPEC-4. |

The `resource_rules_` tests are in [tests/compile.rs](../tests/compile.rs).
Numerical examples use tolerance `1e-12` and cannot prove R1 or equality of
arbitrary quantum operators. Existing independent raw-IR rejection tests remain
necessary: the source occurrence checks do not replace `verify`.

## 9. Open obligations

1. Establish adequacy in both directions between the
   [syntax-complete typing/name/effect rules](source-typing-rules.md), v0, and
   the implementation's module/name resolution, snapshots and implicit frames.
   The explicit rules and T1–T3 do not prove that relation or capacity diagnostics.
2. Complete elaboration semantics and general source-to-IR meaning preservation,
   using the [source value/environment interfaces and local S1–S4 proofs](source-semantics.md).
   The [finite static transformation proofs](static-semantics.md) discharge
   further local mathematical obligations. Their source/Rust correspondence
   premises and full typing/scope adequacy remain open.
3. Transfer the [paper ideal-soundness theorems Q1–Q3](source-soundness.md)
   for the explicit rules to all source-checker paths, with exact phases,
   adaptive composition, and arbitrary external references.
4. Extend the [Lean accounting model](lean-resource-proof.md) to the complete
   source rules when it helps resolve a specification obligation, and verify
   the Rust correspondence. Lexical/effect/scope/history rules and quantum
   semantics remain outside that ownership model. A separate small Kraus
   matrix module checks local completeness algebra; further mechanization
   remains targeted at specification and IR correspondence obligations.

The resource-rule paper result R1, its declaration-boundary corollary, and
the stated local lemmas are completed here. Q1–Q3 supplies ideal soundness
for the explicit mathematical rules separately. Its implementation transfer,
algorithm correctness, and backend behavior remain separate obligations.
