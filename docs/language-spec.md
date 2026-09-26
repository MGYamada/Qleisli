<a id="qleisli-有限コア言語仕様-v0"></a>

# Qleisli finite core language specification v0

Status: **Normative finite core specification fixed** (2026-09-26). This version covers finite types and static operations before sized types and operation parameters. This document, the [surface grammar](syntax-v0.md), and the [module and sealed API specification](standard-library.md) are normative for v0. Following the [design principles](design-philosophy.md), fixing a specification, implementing it, checking finite examples, and proving general theorems are distinct milestones. The [conformance and proof ledger](specification-status.md) records their correspondence. **Proofs of source-to-IR meaning preservation and implementation soundness remain incomplete.** This English edition is the authoritative text of this document and replaces its earlier Japanese edition without changing v0's rules.

<a id="1-範囲と規範の扱い"></a>

## 1. Scope and normative interpretation

v0 is a nonrecursive language with basis types `Unit`, `Bit`, and finite products. It includes injective lifts represented by finite tables, sealed gates, static inverse/control/repetition, restricted auxiliary computation, observation, and classical branching. Finite quantum algorithm examples remain applications of this specification and regression checks.

`Q<A>` is an **ownership type** for quantum resources. It is neither a computation effect nor a value type that permits arbitrary quantum states to be copied. Arbitrary `bind` on the free vector space `H(A)=ℂ^A` is not an executable API. The design principle of Kleisli-style composition with classical values, resources, and effects is distinct from a proof of a strict monad structure.

In this document, *accepted* means satisfying the typing, ownership, and effect rules. Diagnostics for an implementation's explicit capacity limits are a separate matter. Read code fragments in an environment that explicitly imports the sealed names they use. Complete executable examples are in `examples/bell`, `examples/phase_oracle`, and `examples/feedback`.

v0 excludes size variables, arrays, general integers, arbitrary angles, precision types, first-class operation values, higher-order quantum functions, recursion, dynamic loops, general borrowing, `with0`, unconditional `release0`, nondestructive measurement, external quantum operations, and host I/O. `Iso<A,B>`, `Unitary<A,B>`, and `lift(f)` are explanatory metanotation, not source types or APIs.

<a id="2-型と文脈"></a>

## 2. Types and contexts

```text
Basis types A,B   ::= Unit | Bit | (A,B)
Ordinary types T  ::= Unit | CBit | Q<A> | (T,T)
Classical types C ::= Unit | CBit | (C,C)
```

- `Bit` is a coherent basis label and cannot appear as a bare parameter or return type of an ordinary function. `CBit` is a copyable classical value. There is no implicit conversion between them.
- Type equality is equality of syntax trees. Product associativity, `(Unit,T)=T`, and `Q<(A,B)>=(Q<A>,Q<B>)` are not applied implicitly.
- `bits(Unit)=0`, `bits(Bit)=1`, and `bits((A,B))=bits(A)+bits(B)`. `Q<Unit>` still carries linear ownership. Zero wire count does not permit copying or implicit discard.
- An ordinary value containing any `Q<A>` is linear. Referring to a mixed tuple `(CBit,Q<A>)` by name **moves the entire value**. To copy only its classical part, destructure it with a pattern first.
- Types do not assert a state, eigenstate, product state, absence of entanglement, or algorithmic success. Separately owned resources may be entangled.

Write the judgment for an ordinary expression as `Γ ; Δ ⊢ e : T ⊣ Δ' ! ε`. `Γ` contains classical bindings that may be copied or discarded; `Δ` contains linear bindings and their quantum tokens and subsystem IDs; `Δ'` contains bindings remaining in the environment after evaluation. Ownership in the returned value is disjoint from `Δ'`. Mixed values are managed as linear bindings. The basis-expression judgment `Ξ ⊢basis e : A` uses a separate static context and cannot capture runtime `Γ` or `Δ`.

The [type, effect, name, and scope supplement](source-typing-rules.md) expands
these judgments for every current syntax case, together with the resource
calculus's pending frames, binding identities, and complete branch interfaces.
Its local paper lemmas do not establish general compiler correctness.

<a id="3-束縛合成宣言"></a>

## 3. Binding, composition, and declarations

| Construct | Typing and ownership rule | Effect and evaluation order |
| --- | --- | --- |
| Name | Copy a classical value; take a linear value from the environment once. A consumed name cannot be reused. | `Unitary` |
| `()`, `(e1,e2)` | `Unit` and a strict binary product. Check `e2` in the environment left by `e1`. | Left to right; join the effects. |
| `let p=e; body` | Rebind the result of `e` using pattern `p`. Names cannot repeat within one pattern. `_` discards only classical values. A live linear binding cannot be shadowed. | Evaluate the right-hand side before binding. `let q=h(q);` is permitted. |
| `e; body` | The discarded expression `e` must have a classical type. | Sequential composition; join the effects. |
| Block | A final expression is required. Return local quantum ownership in the final result or consume it explicitly. | Statements in source order, followed by the result expression. |
| `f(e1,…,en)` | Argument count and types must match the declaration. Quantum arguments move into the call; ownership is received through its result. | Arguments from left to right. Use the function's **declared classification** as the call effect. |

Every function explicitly declares its parameter types, result type, and effect classification; local `let` types are inferred. An ordinary function is declared `unitary fn`, `iso fn`, or `observe fn`. Its body must consume or return every quantum parameter and local resource, and its result must match the declared type. The same rules apply to bundled ordinary `.qli` definitions.

Check every declaration. Name, type, effect, and ownership checks also apply to unused functions, unselected branches, and the target of zero repetitions. The call graph must be acyclic, including edges from function references in static operations. Functions may be referenced regardless of declaration order. A local value shadows a function of the same name, and the value is not callable. A moved local binding continues to shadow the function throughout its scope. The [grammar](syntax-v0.md#名前とスコープ) specifies name resolution and modules in detail.

<a id="4-効果と意味論"></a>

## 4. Effects and semantics

The effect order is `Unitary ≤ Iso ≤ Observe`. Sequential composition, tuples, and classical branches take the join of their effects. The body effect must be no greater than its declaration's classification. A `basis fn` is a static total function outside this effect order.

| Operation | Effect |
| --- | --- |
| Classical value construction/copying, ownership moves, sealed gates, `split/join`, equal-width injective lifts, static operations, restricted `with_computed` | `Unitary` |
| `init0`, width-increasing injective lifts | `Iso` |
| `measure_z`, `reset`, `discard` | `Observe` |
| Ordinary function call | Use its declared classification without lowering it based on its body. |

For example, `iso fn id(q:Q<Bit>)->Q<Bit>{q}` is valid, but calling this `id` from a `unitary fn` is rejected. Changing its declaration to `unitary` makes the call acceptable. `unitary fn forget(b:CBit)->Unit{()}` is accepted. The reversibility required by `Unitary` concerns the **quantum operator for each fixed classical input**, not reversibility of classical information.

Fix a classical input `γ`, and let the quantum input and output spaces be `H_in` and `H_out`. A pure operation has a classical output `c(γ)` and an operator `V_γ:H_in→H_out`. The `Iso` contract is `V_γ†V_γ=I_in`; `Unitary` additionally requires `V_γV_γ†=I_out`. Proving in general that source checking establishes these contracts is a [formalization obligation](formal-core.md).

The ideal meaning of `Observe` is a completely positive map `E_{γ,c}:L(H_in)→L(H_out)` for each classical output `c`, with a trace-preserving sum for each `γ`. Its outcome probability is `tr(E_{γ,c}(ρ))`. To hide a classical result, sum the corresponding maps. Do not add amplitudes of measurement branches.

Interpret a local operation by extending it with the identity on the remaining system and any external reference system. Separate ownership does not imply a separated state. Preserve the operator's global phase. Since `U` and `exp(iθ)U` give different relative phases under control, inputs to static operations are not equivalence classes modulo phase.

<a id="5-基底計算と単射リフト"></a>

## 5. Basis computation and injective lifting

Basis expressions consist of `Unit`, bit literals, variables, binary products, `not/xor/and`, and calls to total basis functions. `not : Bit→Bit` and `xor/and : (Bit,Bit)→Bit` follow the usual truth tables. Precedence is `not > and > xor`; binary operators associate to the left. Basis variables may be copied or discarded. Basis expressions exclude observations, ordinary functions, capture of runtime classical values, and recursion.

The body of `basis fn f(a1:A1,…,an:An)->B` must be type-checkable and evaluable on every input. Its semantic domain is `Unit` for zero parameters, `A1` for one, and the left-associated product `((A1,A2),…)` for two or more. Label order is `label(a,b)=label(a)+2^bits(A)label(b)`.

`do x <- q; pure e` is a **language form**. First evaluate and consume `q:Q<A>`, then check `e:B` using only `Ξ={x:A}`. If the total function `f:A→B` defined by `e` is injective, return `Q<B>`. Its meaning is `V_f=Σ_a |f(a)⟩⟨a|`. Equal width gives `Unitary`; greater output width gives `Iso`. Equal-width lifts between different type trees are permitted. The IR is `LiftBasis` with a finite table whose injectivity is independently rechecked. Every table output has phase 1.

| Input and continuation | Decision | Meaning |
| --- | --- | --- |
| `q:Q<Bit>`, `pure (x,x)` | Accepted, `Iso` | `α\|0⟩+β\|1⟩ → α\|00⟩+β\|11⟩`. This does not clone an unknown state. |
| `q:Q<Bit>`, `pure not x` | Accepted, `Unitary` | A basis permutation. |
| `q:Q<Unit>`, `pure 0` | Accepted, `Iso` | Prepare `\|0⟩` from a singleton domain. |
| `q:Q<Bit>`, `pure 0` | Rejected | Not injective. |
| `pure outer` | Rejected | An outer classical or quantum binding `outer` cannot be captured. |
| `(q,q)` | Rejected | Duplicates ownership, not basis labels. |

A basis predicate `f` itself need not be injective. Injectivity is required when lifting `f` alone onto a quantum register.

<a id="6-封印された組み込み操作"></a>

## 6. Sealed built-in operations

The following names require explicit imports. `A,B` are metavariables in this table, not user-defined type-parameter syntax. Consume each input `Q` once and return ownership through output `Q` values. Quantum operations with multiple arguments require distinct ownership and disjoint wire sets.

| Module and name | Type | Effect and meaning | IR |
| --- | --- | --- | --- |
| `std::quantum::init0` | `()→Q<Bit>` | `Iso`; prepare `\|0⟩` on a fresh logical wire. | `Init0` |
| `h`, `x`, `z`, `t` in `std::quantum` | `Q<Bit>→Q<Bit>` | `Unitary`; matrices below. | `Gate` |
| `cnot` in `std::quantum` | `(Q<Bit>,Q<Bit>)→(Q<Bit>,Q<Bit>)` (two arguments) | `Unitary`; `\|c,t⟩→\|c,t xor c⟩`. | `Cnot` |
| `toffoli` in `std::quantum` | Three `Q<Bit>` arguments → `((Q<Bit>,Q<Bit>),Q<Bit>)` | `Unitary`; `\|a,b,t⟩→\|a,b,t xor (a and b)⟩`. | `Toffoli` |
| `split` in `std::quantum` | `Q<(A,B)>→(Q<A>,Q<B>)` | `Unitary`; split ownership while preserving state correlations. | `Split` |
| `join` in `std::quantum` | Arguments `Q<A>,Q<B>` → `Q<(A,B)>` | `Unitary`; group ownership in the specified order. | `Join` |
| `std::observe::measure_z` | `Q<Bit>→CBit` | `Observe`; consume the target and return no quantum handle. | `MeasureZ` |
| `reset` in `std::observe` | `Q<Bit>→Q<Bit>` | `Observe`; discard the old state and prepare `\|0⟩` with a fresh logical ID. | `Reset` |
| `discard` in `std::observe` | `Q<A>→Unit` | `Observe`; partial trace over the target. This classification also applies to `Q<Unit>`. | `Discard` |

In basis order `|0⟩,|1⟩`, `H=(1/√2)[[1,1],[1,-1]]`, `X=[[0,1],[1,0]]`, `Z=diag(1,-1)`, and `T=diag(1,exp(iπ/4))`. Gates preserve the target logical wires and refresh ownership tokens. Regrouping through `split/join` does not itself add physical gates, but a change in axis order between a function's input and output is interpreted as an operator permutation.

For target `q` and remaining system `R`, observation has Kraus operators `K_b=⟨b|_q⊗I_R`. `measure_z` denotes `E_b(ρ)=K_bρK_b†`; `discard` denotes `Σ_b E_b(ρ)=tr_qρ`. `reset` denotes `Σ_b J_bρJ_b†` with `J_b=|0⟩_{q'}⟨b|_q⊗I_R`. These meanings include correlated inputs.

Using `h(q)` after `measure_z(q)`, `cnot(q,q)`, and `join(q,q)` is rejected. `let b=measure_z(q); let fresh=init0(); if b {x(fresh)} else {fresh}` is accepted. The newly prepared logical wire is not the measured handle. Reuse of a physical device is the backend's responsibility.

<a id="7-古典分岐の合流"></a>

## 7. Merging classical branches

`if c { e0 } else { e1 }` is a language form. Evaluate the condition first and require `CBit`; select the then arm if true and the else arm if false. Both arms receive the same environment after condition evaluation **exclusively**. Statically check both arms and require all of the following:

1. Both results have the same ordinary type `T`, including the binary-product tree.
2. Both arms consume the same set of outer linear bindings. A `let` inside an arm does not update an outer binding.
3. No local quantum ownership remains in either arm. Explicitly consume temporary resources that are not returned in its result.
4. Match quantum result leaves by tuple position and basis type. Match surviving outer resources (the frame) by their original positions. The frame also includes caller resources absent from the function's local environment.
5. Result and frame matches cover all live ownership in each arm exactly once. Assign a fresh merge token and logical ID to each match; merge classical results by position as well.

The IR uses `ClassicalBranch` with quantum and classical phi mappings. A phi names the selected arm's result at the merged interface; it does not initialize a quantum state. Each classical phi references a value from its arm or from before the branch, never another phi output in the same merge. The effect is the join of the condition and both arms.

`if c {(a,b)} else {(b,a)}` is accepted when `a,b` have the same type. Matching by result position does not require the original wire IDs to agree. Both arms may return quantum results freshly prepared by `init0()` in an `Iso` or higher context. `if c {discard(q)} else {()}` is rejected because the consumed sets differ. An arm containing `let q=h(q); ()` is also rejected because it does not return its quantum result.

<a id="8-静的な逆反復量子制御"></a>

## 8. Static inverse, repetition, and quantum control

The following three constructs are **language forms**. `u` is a statically resolved function name, declared `unitary`, with exactly one argument of type `Q<A>` and a result of the same type `Q<A>`. Sealed `h/x/z/t` are also eligible. Classical arguments, first-class operation values, and `iso` declarations are not permitted.

| Form | Input/output and ownership | Effect and meaning |
| --- | --- | --- |
| `adjoint(u,q)` | `Q<A>→Q<A>`; consume once and return ownership. | `Unitary`; `U†`. |
| `repeat_static(n,u,q)` | `Q<A>→Q<A>`; consume once and return ownership. | `Unitary`; `U^n`. `n` is a decimal static natural-number literal. |
| `qif(c,q){0=>u0,1=>u1}` | Arguments `Q<Bit>,Q<A>` → `(Q<Bit>,Q<A>)`. Control and target wires must be disjoint. | `Unitary`; `\|0⟩⟨0\|⊗U0+\|1⟩⟨1\|⊗U1`. |

Include the effects of the input expressions in the overall effect. `qif` evaluates the control expression before the target expression. It preserves the control's basis label. Even for `n=0`, check the target declaration and body, and return an identity operation that passes ownership through. Preserve scalar phases on `Q<Unit>` under control as well.

The IR is `ApplyUnitary`: translate the checked body into a finite sequence of Hadamards and basis permutations carrying eighth-root phases. Inversion reverses the order, permutations, and phases; repetition expands finitely; control is constructed by basis control of the two arms. Account for the function's output axis order. The verifier rechecks axis bounds and distinctness, disjointness from controls, table totality and bijectivity, and phases.

`adjoint(t,q)` and `repeat_static(0,h,q)` are accepted. `repeat_static(0,missing,q)`, `adjoint(init0,q)`, static transformation of a `choose` with classical arguments, and `qif(q,q){…}` are rejected. See the [static-operation judgments, examples, and verification record](static-operations.md) and [conditional exact-operator proofs](static-semantics.md). These local proofs do not establish full source soundness or Rust compiler correctness.

<a id="9-限定された補助計算"></a>

## 9. Restricted auxiliary computation

`with_computed(q,f){|a| body}` is a **language form**. v0 accepts only the following constructive evidence:

- Evaluate and consume `q:Q<A>`, and require the name of a total basis function `f:A→Bit`. `f` need not be injective.
- Only classical values are available from outside `body`. It cannot capture outer quantum values, including the computation source `q`. The local name `a:Q<Bit>` owns a fresh auxiliary bit.
- The body has effect `Unitary`, returns `Q<Bit>` for the same auxiliary slot, and leaves no additional quantum resources.
- **After ordinary function expansion, quantum instructions must be only a `Z/T` sequence on that auxiliary, or the empty sequence.** Each gate passes the immediately preceding ownership onward.
- The whole expression returns updated ownership of the original `Q<A>`. Excluding its input expression, the construct's effect is `Unitary`.

Accepted bodies include `with_computed(q,f){|a| z(a)}`, the identity `a`, and `t(z(a))` wrapped in ordinary functions. Rejected bodies include `h(a)`, `h(h(a))`, measurement, classical branching, and capture of another quantum value. Although `adjoint(t,a)` and `repeat_static(2,z,a)` are diagonal, they produce `ApplyUnitary` and are rejected by this v0 evidence format. There is no extensional acceptance rule based on matrix equivalence.

To define the meaning, let `C_f|x,b⟩=|x,b xor f(x)⟩` and let `W` be the phase sequence above. With `k=(4·number_of_Z_gates+number_of_T_gates) mod 8`, for every `x`,

```text
C_f† W C_f |x,0⟩ = exp(iπ k f(x)/4) |x,0⟩
V = Σ_x exp(iπ k f(x)/4) |x⟩⟨x|
```

Linear extension of this equation shows that, for arbitrary inputs and reference systems, the auxiliary returns to `|0⟩` and separates from the remaining system. `V†V=VV†=I_A`. This **structural evidence for all inputs** closes the internal auxiliary. A lifetime alone, measurement of sample inputs, or numerical comparison of states is not evidence of this property.

The IR is atomic `ComputeUseUncompute`. Verify the entire structure corresponding to `Init0; C_f; W; C_f†; Release0`; no standalone `Release0` is exposed. Current handwritten IR also supports protected control over work registers, but accepted v0 source bodies are restricted as above. General borrowing, preservation-effect signatures, and `with0` belong to later specifications.

<a id="10-コンパイルと実行の境界"></a>

## 10. Compilation and execution boundaries

1. Resolve modules and check every declaration: names, types, effects, linear ownership, finite tables, and auxiliary evidence.
2. Expand ordinary functions and lower language forms and sealed names to their corresponding IR. Verify the input/output boundary of each ordinary function.
3. An independent IR verifier rechecks IR from every producer using the same rules. Unverified IR cannot enter the execution API.
4. Execute a closed entry point: a parameterless `observe fn main()->C` in the root `main.qli`, where `C` is a classical type and no quantum ownership remains at termination. Library checking does not require an entry point.

A quantum IR instruction consumes its input ownership tokens and creates fresh tokens for any quantum outputs. Name moves and identity functions do not themselves add physical operations. Gates and structural operations carry logical wires forward; `init0`, width-increasing lifts, and `reset` allocate fresh IDs as needed. Branch merge IDs rename the selected arm's axes. IDs alone do not establish the presence or absence of correlations.

Report type, ownership, and effect violations, noninjective lifts, unsupported auxiliary evidence, unknown names, recursion, and capacity overflow with source locations. With multiple violations, diagnostic ordering and exact wording are not normative. Implementation error codes and numerical/capacity limits are given in the [implementation profile](frontend-v0.md#診断と上限). Capacity overflow must not be handled by changing meaning, such as truncating repetitions or implicitly discarding resources.

The reference executor numerically approximates the finite ideal semantics. Hardware compilation and device-capability checks are separate responsibilities; unsupported mid-circuit measurement, feedback, or other features cannot be treated as implemented. Rust memory safety, agreement on finite tests, and the existence of independent IR checks do not replace a proof of source soundness.

<a id="11-変更方針と次の工程"></a>

## 11. Change policy and next work

The scope and acceptance/rejection rules of this edition are fixed as the v0 baseline. A future change to syntax, types, effects, ownership, semantics, or sealed APIs must update the specification, grammar, conformance checks, and IR correspondence together and record its compatibility impact. Adding experimental ordinary library definitions does not by itself add language forms or sealed operations.

The [inference-rule supplement](source-typing-rules.md) and resource calculus cover all current syntax cases. [Ideal soundness Q1–Q3](source-soundness.md) proves pure-operation and instrument properties for these explicit mathematical derivations. The next priority is to prove their adequacy for all Rust source-checker paths, source-to-IR meaning preservation, and correspondence with the verifier implementation. [Source semantics and conditional IR correspondence](source-semantics.md) develops source values and environments, function-boundary substitution, frame extension, and phi composition; soundness of every Rust-accepted program and compiler correctness remain open. The [Stage 1 completion criteria](../ROADMAP.md#1-言語仕様) remain in force. Sized types, operation parameters, algorithm skeletons, and extensions to the standard vocabulary belong to subsequent specifications.
