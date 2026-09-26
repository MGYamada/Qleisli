# Source-to-IR translation contract for finite core v0

Status: **explicit translation schemas and a conditional paper preservation
theorem** (2026-09-27). This English supplement connects the semantic leaves
and interfaces of [S1–S4](source-semantics.md) to the static transformations
[F1–F5](static-semantics.md). It interprets the existing
[typing rules](source-typing-rules.md) and [v0 specification](language-spec.md);
it adds no language form or public API. None of the results below is a Lean
proof or a proof about every execution of the Rust compiler or verifier.

The later three-argument computed extension adds the [SC-IR obligation](semantic-contracts-v0.1.md)
alongside the baseline schemas below: retain W, the explicit u and the
predicate, preserve their ordered body interface, and independently establish
`C_f† W C_f E_0=E_0 u`. This is an additional conditional leaf, not a claim
that the original C1–C5 proof verified the new Rust paths. The later
[FC function-contract rules](function-contracts-v0.1.md) add a retained evidence
action through final static transformations, with the conditional schema below.
General correctness of its independent extraction, source snapshots/cache,
and compiler implementation remains an obligation; no Lean theorem is added.

The distinction is between a **mathematical translation satisfying the schemas
below**, its ideal raw-IR meaning, and the actual Rust algorithms. For the
first two, the semantic leaf obligations can be discharged and the structural
proofs assembled. Establishing that every successful Rust execution constructs
such a translation remains open. Numerical simulator agreement is finite
evidence for that obligation, not the definition of either meaning.

## 1. Boundary relation and the preservation statement

At each successful expression boundary record `(E,F,R,v)`: lexical bindings
with spent markers, opaque pending/caller holders, the slot store, and the
returned symbolic value when present. Use the exact type trees and classical
and quantum projections of [S1](source-semantics.md#1-mixed-values-and-ordered-quantum-interfaces).
The translation boundary relation **BC** requires:

1. Live source slots and live IR tokens are in bijection, with the same ordered
   wire list and width `bits(A)` at each pair; there are no extra IR tokens,
   including zero-width tokens. Source basis trees remain in the relation:
   raw IR widths alone do not distinguish `Bit`, `(Bit,Unit)`, and `(Unit,Bit)`.
2. Returned, environmental, and frame holders partition all live slots, and
   their wire lists partition the live physical axes. Slot/token coverage
   includes every `Q<Unit>` even though it contributes no axis.
3. Decoding visible classical SSA IDs gives the source classical values.
   Aliased classical inputs and repeated classical outputs are permitted.
   Arm-local IDs are not visible after a branch except through exported phis.
4. Each generated token, wire, and classical ID is fresh in its respective
   issued-ID history, including IDs issued in either alternative arm. Existing
   wires may be transferred to a fresh token. A consumed binding stays spent;
   allocating a new token does not restore its lexical name.
5. Resolved declarations, the defining module, exact argument/result types,
   and declared effects agree with the checked source derivation. The finite
   dependency graph includes ordinary, basis, and static references in all
   bodies and has no cycle. Capacity failures are outside successful translation.

Fix an order for the complete source holder interface and for live IR wires.
Let `J_in` and `J_out` map **source interface coordinates to IR coordinates**.
They are the basis permutations determined by BC, including tensor grouping;
an empty list gives the identity of the scalar space. Neither changes the
physical state. At an intermediate boundary, `o` is the **complete decoded
classical record accessible to the continuation** in `(E',F,v)`, not just the
returned value's classical part. Only private Kraus histories and inaccessible
records may be summed at that point; a later `if` must retain correlations
with every bit it can read. At the closed final boundary, group these records
by the public return value. For each such boundary record `o`, preservation is

```text
E_IR[o] composed with Ad(J_in) = Ad(J_out) composed with E_source[o],
V_IR J_in = J_out V_source                              (pure case),
Ad(J)(rho) = J rho J†.
```

For a history-dependent raw layout, transport each raw result back to the
common source interface using `J_out,h†` before grouping histories:

```text
sum_(h exporting o) Ad(J_out,h†) composed with E_IR,h composed with Ad(J_in)
  = E_source[o].
```

Alternatively choose one common IR output coordinate map `J_bar` and first
transport each history by `J_bar J_out,h†`; the first displayed equation then
uses `J_out=J_bar`. Both sides hide private measurement histories by summing
CP maps, never amplitudes. All equations extend by the identity on an arbitrary
finite reference space. Pure correspondence retains the exact operator,
including scalar phase; equality of density maps is insufficient for a target
that may later occur under `qif`.

## 2. C1: basis encoding, evaluation, and table rows

For `A ::= Unit | Bit | (A,A)`, define `w(A)=bits(A)` and structured values
`Val_Unit={()}`, `Val_Bit={0,1}`, `Val_(A,B)=Val_A × Val_B`. Retain the typing
rules' integer carrier `L_A={0,...,2^w(A)-1}`. Define the bijection
`enc_A : Val_A -> L_A` by

```text
enc_Unit(()) = 0,               w(Unit) = 0,
enc_Bit(b) = b,                 w(Bit) = 1,
enc_(A,B)(a,b) = enc_A(a) + 2^w(A) enc_B(b).
```

The inverse `dec_(A,B)(i)` decodes `i mod 2^w(A)` as `A` and
`floor(i/2^w(A))` as `B`. **C1a:** `enc` and `dec` are inverse on these domains.
Proof is by type induction: the Unit and Bit cases are immediate, and quotient
and remainder uniquely recover the two bounded components of a product. This
also works for `w(A)=0`, where the remainder is zero and division is by one.
Unit contributes one label, not an empty domain. The bijection does not make
different source type trees interchangeable.

For formals `A_1,...,A_k`, let `Pack([])=Unit`, `Pack([A])=A`, and use a
left-associated product for longer lists. Set `s_j=sum_(l<j) w(A_l)`. Then

```text
enc_Pack(a_1,...,a_k) = sum_j 2^s_j enc_(A_j)(a_j),
i_j = floor(i / 2^s_j) mod 2^w(A_j).
```

**C1b:** the packed formula equals the recursively defined product encoding.
Induct on the number of parameters; appending a factor shifts it by the sum
of all preceding widths. Zero parameters have the unique index zero. Thus
the first formal occupies the low bits, independent of the number of Unit
factors. An ordinary basis call still requires `k` separate arguments; this
packing is an internal table convention, not implicit source uncurrying.

**C1c (evaluation and rows).** In an environment that represents each typed
basis label by its `enc`, evaluation by the following mathematical algorithms
returns `enc_B(b)` for the result `b:B` of the basis rules:

- Variables read that encoded value; literals and Unit use their displayed
  encodings. A pair adds the first label to the shifted second label.
- `not`, `and`, and `xor` require Bit operands and use the Boolean truth table.
- A basis call resolves the checked callee in the module containing that
  expression, evaluates separate arguments in formal order, packs them by
  C1b, and reads the row of the selected callee's table. That table was
  compiled from the callee's body in its own defining module.
- A typed lift pattern decodes a product by C1a, recursively binds its distinct
  names, and omits wildcard labels from the environment. It never removes an
  input row from enumeration.

Proof: induct on acyclic basis-declaration dependency rank and then expression
or pattern structure. The variable/literal/Boolean cases preserve their stated
encodings. C1a supplies the pattern induction; C1b supplies pair construction
and argument packing. The lower-rank callee row equation gives the call case.
T1 guarantees totality and the fixed result type. Enumerating all input indices
then constructs exactly

```text
table_f[i] = enc_B(f(dec_A(i))).
```

For declared basis functions, `A=Pack(params)`. For `do p <- q; pure b`, use
the original input type `A` and the pattern valuation of `dec_A(i)` to evaluate
`b`. The table's identity is now a syntactic evaluation obligation, not the
semantic assumption that the resulting quantum operators already agree.

## 3. C2: lifts and the sealed/classical leaves

Given the C1 row equation, an injective `f:Val_A->Val_B` lowers to `LiftBasis` with
that table, old wires as the ordered prefix, and fresh appended wires if needed.
Its ideal action is

```text
V_table |i⟩ = |table_f[i]⟩,
V_table enc_A = enc_B V_f,
V_f = sum_(a in Val_A) |f(a)⟩⟨a|.
```

Here `enc_A` also denotes the induced basis-coordinate isomorphism. **C2a**
follows on every basis vector from C1 and extends linearly. Injection gives
orthonormal output columns. Therefore `w(B)>=w(A)`; equal widths give a
permutation and effect `Unitary`, larger widths an isometry and effect `Iso`.
Appending fresh zero axes is the storage realization of this map, not an
assumption that the input register was unentangled. A wildcard over a Bit is
safe only if the *whole* output function remains injective; erasing a Unit
factor can give a bijection with unchanged physical width.

For other leaves, evaluate actual expressions first, once and in source order.
The schemas below describe only the ensuing primitive step. Its operands have
the exact source types, distinct owned ports when required, and the ordered
axes supplied by BC. All fresh output IDs satisfy BC.

| Source step | Required raw constructor | Ideal local action, with first component in low bits |
| --- | --- | --- |
| `init0()` | `Init0` on a fresh wire | `\|()⟩ -> \|0⟩` |
| `h(q)` | `Gate(H)` | `\|b⟩ -> (\|0⟩+(-1)^b\|1⟩)/sqrt(2)` |
| `x(q)` | `Gate(X)` | `\|b⟩ -> \|1-b⟩` |
| `z(q)` | `Gate(Z)` | `\|b⟩ -> (-1)^b\|b⟩` |
| `t(q)` | `Gate(T)` | `\|b⟩ -> zeta^b\|b⟩`, `zeta=exp(i*pi/4)` |
| `cnot(c,t)` | `Cnot` in that operand order | `\|c,t⟩ -> \|c,t xor c⟩`, result `(c,t)` |
| `toffoli(a,b,t)` | `Toffoli` in that operand order | `\|a,b,t⟩ -> \|a,b,t xor (a and b)⟩`, result `((a,b),t)` |
| `split(q:Q<(A,B)>)` | `Split(left_bits=w(A))` | Prefix/suffix regrouping, identity on physical axes |
| `join(a,b)` | `Join(left=a,right=b)` | Ordered wire concatenation, identity on physical axes |
| `measure_z(q)` | `MeasureZ` with fresh classical result | Outcome `b` has `K_b=⟨b\|`; consume the input port |
| `discard(q:Q<A>)` | `Discard` | Private Kraus family `K_a=⟨a\|`; consume the port and hide `a` |
| `reset(q)` | `Reset` with a fresh logical wire/port | Private family `K_b=\|0⟩_fresh⟨b\|_old`; hide `b` |
| `true`, `false` | `ClassicalConst` with the matching bit | Extend the record by that constant; quantum identity |
| `not`, `and`, `xor` on CBit values | `ClassicalNot`, `ClassicalAnd`, `ClassicalXor` | Extend the record by the matching truth function; quantum identity |

**C2b:** each row satisfies the boundary correspondence equation. Gate and
controlled-gate cases agree on basis vectors, including the listed phases.
Split/join agree by C1a and the specified ordered axes, even when one side has
zero width. Initialization tensors in the same fresh zero factor.

For observation, expand any joint input operator in local matrix units as
`rho=sum_(i,j) |i⟩⟨j| tensor R_ij`, where `R_ij` acts on the remaining holders
and an arbitrary reference. `measure_z` produces `R_bb` in outcome `b`;
`discard` produces `sum_i R_ii`; reset produces
`|0⟩⟨0| tensor sum_i R_ii`, in the new output layout. These are exactly the
source instruments. No normalization or separability hypothesis is used.
For `Q<Unit>`, discard has one Kraus operator, physically the identity, while
still consuming its distinct ownership and having source effect `Observe`.

For a classical truth function `g` and fresh ID `c`, both sides send the input
record `gamma` to `gamma[c↦g(gamma)]` with quantum identity. This remains true
when two inputs are the same classical ID. Hidden records are grouped by
summing their quantum blocks. Operand computations still compose before the
truth step, so `false and measure_z(q)` consumes and measures `q`.

This proof establishes locality and fresh-name equivariance for the leaves
required by S1/S2: tensor each displayed operator with the identity on every
inaccessible axis and conjugate by BC's coordinate permutations. Quantum
ownership isolation is not used as a product-state assumption.

## 4. C3: the computed certificate and static target dependency

For `with_computed`, evaluate its source expression once and retain that owned
result while checking the private body. Its emitted source-expression prefix
and effects remain in the enclosing computation. C1 gives the predicate table
on exactly `Pack(params)`,
which must equal the source register's basis tree, with result Bit. The
predicate need not be injective. Zero parameters mean `Unit`; they do not
mean an absent quantum source port.

The translation schema checks the body in the prescribed private environment,
retaining every masked outer owner in the frame. It must return the same
auxiliary slot with effect `Unitary`. The **entire** emitted body must be a
linked chain of Z/T gates on that auxiliary, or empty: each gate consumes the
preceding output token, and the final token is the returned one. Merely having
the same width, a diagonal mathematical effect, or a correct sampled state is
not this certificate. Unselected branches and dead-looking classical
instructions do not disappear from this structural check.

Let `r=4*(number of Z)+number of T (mod 8)`. Given body correspondence for
this smaller subderivation, the certified chain has exact operator
`diag(1,zeta^r)`. Replace its emitted instructions and private auxiliary by
one `ComputeUseUncompute` with that predicate and protected auxiliary gates.
On each `|a,0⟩`, its ideal compute/use/uncompute action is

```text
|a,0⟩ -> |a,f(a)⟩ -> zeta^(r f(a))|a,f(a)⟩
        -> zeta^(r f(a))|a,0⟩.
```

**C3:** the replacement preserves the exact source operator
`D_f|a⟩=zeta^(r f(a))|a⟩` and restores a separated zero auxiliary for every
input and reference. For `sum_a |a⟩ tensor |v_a⟩`, apply the equation termwise;
the auxiliary factors out even for arbitrary, nonorthogonal `v_a`. This is
the source-specialized instance of F3, now tied to the C1 table and the emitted
token chain. If `A=Unit`, `D_f` may be a nontrivial scalar that must survive
later control.

For `adjoint`, `repeat_static`, and `qif`, resolve checked lower-rank targets
with exact signature `Q<A> -> Q<A>` and declared effect `Unitary`. Translate
the complete target body, including its return layout, in a fresh environment;
require the verified finite subset of F2. The target's source-to-IR equality
is obtained by dependency induction, **not** inferred from IR validity.
Apply these syntactic emission schemas to the complete step lists produced
by the F2 flattening algorithm:

| Form | Emitted operations |
| --- | --- |
| `adjoint(f,q)` | Reverse the flattened list and invert each step by F4 (including reindexed inverse phases); emit one `ApplyUnitary` on the evaluated input. |
| `repeat_static(n,f,q)` | Concatenate that complete list `n` times and emit one `ApplyUnitary`; the list is empty at zero, after all target checks. |
| `qif(c,q) { 0 => f0, 1 => f1 }` | Evaluate control then target once; `Join(control,target)`. Shift every target action/control index by one and add `(axis 0 = b)` to every step of arm `b`. Concatenate the zero-arm and one-arm lists into `ApplyUnitary`, then `Split(left_bits=1)`. |

The source `qif` path therefore does not emit the separate raw `QuantumIf`
constructor. F1–F5 give these sequences respectively `U†`, `U^n`, and
`|0⟩⟨0| tensor U0 + |1⟩⟨1| tensor U1`. The final output permutation and all
scalar phases belong to `U`. Target validation still applies at `n=0`, and
input expressions are evaluated once before the static operator.

### FC attachment through function calls and static transformations

For `apply_contract(i,s,e)`, translate e once and use its resulting owned
register. Resolve both ordinary unary-unitary definitions after that input,
preserving exact source trees and the defining-module/dependency identity in
BC. Independently validate their actual raw bodies and extract the complete
ordered pure circuits. The [FC-CHECK boundary](function-contracts-v0.1.md#3-independent-whole-function-evidence)
must establish `U_i=U_s`, including phase, and retain those bodies, source
snapshots, signature, and checked dependencies in immutable evidence.

Emit one `ApplyUnitary` containing a `CircuitAction::Contract` on the input's
ordered axes, initially with `adjoint=false` and no new control. Consume the
input token and produce a fresh token for exactly the same public register.
Its semantics is `U_i=U_s`, extended by identity on the complete caller frame.
This preserves BC without copying the input into two runtime invocations.
The source expression's effect and all pending holders remain present.

Static flattening retains this action. F1 remaps its indices and controls;
F4 toggles its adjoint flag when reversing; F5 adds coherent controls;
repetition retains its evidence on every occurrence. The
[FC-STATIC identities](function-contracts-v0.1.md#5-conditional-mathematical-soundness)
justify each resulting operator. Final IR verification checks axes,
ownership, and the opaque checked evidence boundary. A different unbound
circuit cannot inherit this evidence merely by keeping a function name.

For the mathematical translation, add this as a conditional leaf to C5:
assuming correct ordered extraction and actual-function evidence, the emitted
operator equals the fixed specification, and S1–S4 composes it with input and
frame translations. This argument supplies the local obligation; it does not
prove that every Rust path supplies those premises, or turn source bytes into
a proof of compiler correctness. Current bounds and validation results remain
separate from the general preservation theorem.

## 5. C4: constructing the complete branch interface

Translate the condition first. Both arms start with its same residual holder
environment and register store, but generated-ID histories continue across
both arm translations. Require equal result type trees and equal consumption
of outer bindings. Construct the interface as follows:

1. Traverse the two returned value trees in corresponding positions. Unit
   yields Unit. A pair recursively pairs its components. Classical leaves
   either share a parent-visible ID or receive a fresh phi result. Quantum
   leaves are removed from their arm's live store and paired by result
   position, with the same basis tree.
2. Pair every remaining live register by its original entry-slot identity.
   The two residual key sets must match and each key must have existed at
   entry. Match basis trees. This includes suspended callers and pending
   values that do not appear in the current lexical environment.
3. Give each quantum pair a fresh common token and ordered wire list; create
   a phi from each arm's entire ordered input list to that common list.
   Export classical phis using the frozen pre-merge valuation, simultaneously.

**C4a (coverage):** under BC and these checks, the pairing is a bijection from
each arm's live slots to the common result/frame slots. Result slots occur
once by linearity and are removed before frame pairing. Every residual slot
is paired exactly once by equal key sets; no branch-local unreturned owner
can enter the frame. Their disjoint wire lists therefore give a bijection of
all live axes. Empty quantum lists are paired as owners as well. Fresh output
names preserve disjointness. These facts supply S3's `CompletePhi` premise.

**C4b (classical export):** a result ID shared by the two arms is parent-visible
because arm-local generated IDs are globally fresh across alternatives and
successful operands only read visible IDs. Otherwise each new phi output
reads the selected old value. Fresh output IDs cannot be sibling inputs, so
sequential writes to fresh destinations implement the simultaneous
substitution regardless of phi list order. Unexported arm-local IDs stay
out of scope. Multiple phi outputs may copy the same classical input.

Let `P_i` identify the selected arm's result/frame layout with the common
interface, and `mu_i` be this simultaneous classical export. Condition maps
`C_d` and selected-arm maps `A^i_h` then compose to

```text
sum_(d,h exporting o via mu_b(d)) Ad(P_b(d)) composed with A^b(d)_h composed with C_d,
```

where `b(d)=1` selects then and `0` selects else. **C4c:** this is the same
source and IR instrument by S3 and the condition/arm induction hypotheses.
For a pure derivation with fixed classical input it is the exact selected
product `P_i V_arm V_condition`. Phi renaming prepares no state and loses no
correlations. This also covers branches with fresh allocation or reset whose
physical output IDs differ. It does not combine arm amplitudes coherently.

## 6. C5: assembly for the mathematical translation

Define `D translates-to (ops,v,R')` by the **syntactic schemas** above and
S4's structural schemas: evaluated-value binding, left-to-right sequencing,
scope projection, and call expansion. Require successful source typing and
resource premises, BC at inputs, fresh allocations, C1 table construction,
C3's certificate/static subset, and C4's complete interface construction.
The later certified-computed and function-contract cases additionally require
their independently checked finite IR equations. No rule may assume the
desired source-to-IR semantic equality itself as a premise.

**Theorem C5 (conditional preservation).** For every finite derivation in
this translation relation, the output satisfies BC and the equations in §1
hold for every classical input, decoded output, and finite external reference.
Pure derivations satisfy exact operator equality. The raw effect is at most
the source derived effect, which is at most the checked declaration's effect.

**Proof.** Use well-founded induction on the resolved dependency rank of the
current declaration, and structural induction inside that declaration.
Basis tables use C1's own dependency/expression induction. Ordinary and static
references go to lower-rank declarations; the finite AST's operands, blocks,
arms, and computed body are strictly smaller structural subderivations.
This handles both normal inlining and fresh compilation of static targets
without assuming the compiler's result already agrees with its source.

- Unit, copy/move, and pattern binding only change the holder interface.
  The resource premises and BC forbid quantum duplication or loss; S4 gives
  the coordinate equality. Block exit hides classical records and binder
  identities without tracing out a surviving quantum holder.
- Pairs, actual argument lists, and `let` use the hypotheses in source order,
  retaining each pending result in the complete frame. Intermediate `J`
  maps cancel. Finite adaptive sums distribute over composition. Normal calls
  use S1's substitution of already evaluated values and the lower-rank body
  hypothesis; C2's locality and S2 extend it over the suspended caller.
- Boolean forms apply the operand hypotheses eagerly, then C2b. A coherent
  lift applies the input hypothesis followed by C1 and C2a. Sealed calls apply
  argument hypotheses followed by the corresponding C2b row.
- A classical branch uses the condition/arm hypotheses and C4. Returned and
  residual slots cover the complete output, so its coordinate isomorphism is
  defined on the entire state, including zero-width holders and frames.
- A computed scope first uses the source-expression hypothesis, then its body
  hypothesis and structural certificate to invoke C3. Its entire map is the
  operand instrument followed by `Ad(D_f)`; its effect retains that operand's
  effect. Static operations use lower-rank target equality and F1–F5,
  preceded by their input-expression hypotheses. No phase quotient occurs.
- The later certified-computed case uses its input hypothesis, the
  independently checked `W E_f=E_f u` relation, and the explicit fresh-auxiliary
  construction to apply SC-COMPUTED. Its public map is `Ad(u)` with the
  complete original frame; relating u and W to their source definitions still
  uses the corresponding translation hypotheses.
- FC-APPLY uses the input-expression hypothesis once. The independently
  checked actual raw implementation equals the fixed raw specification;
  the lower-rank specification hypothesis relates that operator to its source
  meaning. FC-IR and FC-STATIC retain this equality under ordered placement,
  control, inverse, and repetition. Dependency metadata binds the artifact
  but is not itself a premise of source semantic correctness.

These include all current expression, pattern, statement, and declaration cases,
with the semantic-contract additions understood as the conditional supplements
above, in
the [constructor coverage table](source-typing-rules.md#9-constructor-coverage-and-implementation-audit).
Each schema preserves BC's live coverage, ordering, classical decoding, and
freshness; observations explicitly remove or replace the indicated owner.
All local operator/instrument equations extend over references, and finite
history grouping preserves equality. Effects follow row by row: only
initialization and widening lift require `Iso`, observation requires
`Observe`, and other leaf steps require `Unitary`. Composition and both arms
take joins. Expanding a normal call can lower its raw effect, while its source
judgment retains the declared effect. This instantiates T3b's leaf premise.

The theorem applies to this specified mathematical translation. Proving that
Rust's snapshots, maps, counters, enumeration, graph traversal, and all return
paths construct it is a separate implementation-adequacy theorem. Calling the
raw verifier at the end does not discharge that theorem.

## 7. Implementation and independent-verifier obligations

| Contract | Frontend implementation to audit | Independent raw-IR check and its boundary |
| --- | --- | --- |
| Exact type trees, declaration identity, acyclic references | [`ty`](../src/frontend/compile/mod.rs), [`resolve`](../src/frontend/compile/mod.rs), [`order`](../src/frontend/compile/mod.rs) | Raw IR does not contain source names, basis trees, or a call graph. |
| C1 encoded evaluation and correct full rows | [`compile_basis`](../src/frontend/compile/basis.rs), [`eval_basis`](../src/frontend/compile/basis.rs), [`bind_basis_pattern`](../src/frontend/compile/basis.rs), [`lift`](../src/frontend/compile/lower/mod.rs) | [`check_table`](../src/verify.rs) checks length, range, and required injection; it cannot check equality with a missing source expression. |
| C2 operand identity/order and primitive kind | [`sealed`](../src/frontend/compile/lower/primitives.rs), [`expr_inner`](../src/frontend/compile/lower/mod.rs) | [`verify_op`](../src/verify.rs) checks widths, ownership, freshness, classical visibility, and effects. It does not choose the source-intended gate. |
| Ordered port transfer and complete owners | [`input`](../src/frontend/compile/lower/mod.rs), [`outputs`](../src/frontend/compile/lower/mod.rs), [`register`](../src/frontend/compile/lower/mod.rs) | [`insert_token`](../src/verify.rs), [`consume`](../src/verify.rs), [`verify`](../src/verify.rs) enforce disjoint wires, fresh tokens and final coverage, including empty tokens. |
| Value substitution, lexical projection, pending/caller frame | [`call_user_inner`](../src/frontend/compile/lower/mod.rs), [`block`](../src/frontend/compile/lower/mod.rs), [`close_scope`](../src/frontend/compile/lower/scope.rs), [`bind`](../src/frontend/compile/lower/mod.rs) | Raw validation checks emitted operations; it does not reconstruct spent source names or suspended caller holders. The [scope model](lowering-state-refinement.md) checks a local projection, with trace/coverage premises still open. |
| C3 correct predicate and entire auxiliary chain | [`computed`](../src/frontend/compile/lower/mod.rs) | [`verify_compute`](../src/verify.rs) checks total predicate, fresh auxiliary wires and protected-use restrictions. Source v0 permits a narrower body than raw IR. |
| Static exact operators and final output layout | [`static_steps`](../src/frontend/compile/lower/mod.rs), [`flatten`](../src/frontend/compile/circuit.rs), [`remap`](../src/frontend/compile/circuit.rs), [`invert`](../src/frontend/compile/circuit.rs) | [`check_circuit`](../src/verify.rs) checks permutation/phase tables and disjoint axes/controls. Validity alone cannot identify the intended target operator. |
| C4 source result positions and original frame slots | [`branch`](../src/frontend/compile/lower/branch.rs), [`merge_results`](../src/frontend/compile/lower/branch.rs), [`merge_register`](../src/frontend/compile/lower/branch.rs) | [`verify_branch`](../src/verify.rs) checks selected inputs, total quantum coverage, compatible widths and fresh outputs, plus frozen classical phi inputs. It does not retain source result positions. |
| Public result order and history grouping | [`lower_function`](../src/frontend/compile/lower/mod.rs), [`process_project`](../src/frontend/compile/mod.rs) | [`verify`](../src/verify.rs) checks result availability. [`run_closed`](../src/sim.rs) numerically groups returned classical bits, while [`relabel_branch`](../src/sim.rs) transports branch wire names. |

For example, replacing an injective identity table with an injective NOT table
can preserve raw validity and change source meaning. Replacing T by Z or
exchanging equal-width phi inputs can do the same. Thus three distinct claims
must stay separate: the source derivation is accepted; its emitted IR is
valid; its emitted IR denotes the source operation. C1–C5 and the boundary
relation specify the missing correspondence obligations rather than treating
the independent verifier as a source-equivalence checker.

## 8. Evidence and remaining work

[Source-to-IR regressions](../tests/source_ir_correspondence.rs) exercise the
table, observation/reference, computed-phase, and branch interfaces against
independently derived expectations. The existing
[exact static matrix regressions](../tests/static_semantics.rs) check phase
and output-axis direction, including controlled scalar phases. The
[source semantic regressions](../tests/source_semantics.rs) retain
call-by-value and simultaneous-phi cases, and
[malformed-IR tests](../tests/verify.rs) retain independent rejection evidence.
Run results and the precise finite coverage are recorded in the
[conformance ledger](specification-status.md).

The remaining proof obligations are concrete:

1. Derive BC and these translation schemas from every successful Rust path,
   including source typing, resolution timing, tombstones, masked captures,
   branch snapshots, work limits, and generated-ID histories. The
   [scope-refinement step](lowering-state-refinement.md) extracts the closing
   algorithm and proves its lookup model, but not all paths supplying its
   snapshots or complete holder/frame coverage.
2. Prove that each Rust table/axis/circuit algorithm implements its mathematical
   schema; C1–C5 and F1–F5 are paper proofs of the specified algorithms, not a
   semantics of Rust execution or a machine-checked compiler proof.
3. Establish the independent verifier's implementation correctness against the
   raw validity conditions. Its independence is valuable but is not a proof
   of its own code or of source correspondence.
4. Relate reference execution to the exact raw denotation with explicit
   numerical error and capacity conditions. Closed finite probability tests
   do not establish exact equality of all open instruments or pure phases.

Subject to these implementation connections, C5 would transfer Q1–Q3's ideal
source guarantees to compilation. Those connections, full compiler soundness,
individual algorithm correctness, and hardware behavior are not claimed here.
