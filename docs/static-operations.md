<a id="a2-有限の静的操作変換"></a>

# A2: Finite static operation transformations

Status: **Finite subset implemented and checked on finite examples**
(2026-09-26). Function names are resolved at compile time; operations are not
first-class values. All three constructs below are language forms, not ordinary
higher-order functions or additional sealed gates. This English edition is the
authoritative contract and reference for this document, replacing its earlier
Japanese edition. The review revision additionally supports closed classical
computations and deterministic branch selection within a static target. The
[finite core specification](language-spec.md) supplies the surrounding rules.
The [static semantics](static-semantics.md) gives local phase-preserving proofs;
general source-to-IR meaning preservation and Rust implementation correctness
remain open.

The 0.1.8 [M1 supplement](next-minor-spec.md) additionally permits static
parameter names in these three forms, requiring Adjoint, Apply, and Controlled
access respectively. Its six-bit operation profile is separate from the
existing twelve-bit closed named-function profile below. `apply_contract` and
both computed forms keep their original closed name operands. Static operation
constructors use bracket arguments; they are not runtime closures.

<a id="表層の契約"></a>

## Surface contracts

A target `u` is a known `unitary fn u(q: Q<A>) -> Q<A>` or one of the sealed
single-qubit gates `h/x/z/t`. The initial subset requires one register, identical
input/output basis type trees, and no classical parameters. Expand and check
the ordinary body for types, effects, and ownership, independently verify its
IR, and only then transform it.

| Form | Type, ownership, and effect | Acceptance, rejection, and meaning |
| --- | --- | --- |
| `adjoint(u, q)` | `Q<A> -> Q<A>`, `Unitary`; consume and return the input ownership. | `U†` for the known body. Reject `Iso`, observation, classical parameters, or different input/output types. |
| `repeat_static(n, u, q)` | The same interface. `n` is a decimal static natural-number literal. | `U^n`; zero repetitions give identity but still check the target name, type, and body. Reject a dynamic count or capacity-budget overflow. |
| `qif(c, q) { 0 => u0, 1 => u1 }` | Arguments `Q<Bit>,Q<A>` return `(Q<Bit>,Q<A>)`, `Unitary`; consume and return both ownerships. | `\|0⟩⟨0\|⊗U0 + \|1⟩⟨1\|⊗U1`. Require distinct ownership and preserve both arms' phases. |

The table gives each form's own effect. Join it with the effects of its input
expressions; applying a static unitary does not erase an input's `Iso` or
`Observe` effect. Quantum arguments are evaluated from left to right. The same
ownership cannot be supplied twice. Distinctness concerns logical ownership
slots as well as disjoint physical wire sets: `Q<Unit>` remains linear even
though its wire list is empty. Different ownerships may be entangled.

Resolve names through explicit imports and the current module. A local binding,
including a spent binding, hides a same-named function. Recursion is rejected,
including call-graph edges from static target references. Function names cannot
be returned as values or passed as ordinary arguments.

The implementation limits `n` to 4,096 and disallows leading zeroes except for
`0` itself. Basis literals elsewhere remain only `0/1`. The existing total work
budget and depth limit also apply to static expansion, including nested
repetitions.

### Static target judgment

Use the environments, opaque pending-value frame `F`, and register store `R`
from the [source resource rules](source-resource-rules.md). `E` retains spent
bindings as unavailable entries. Write

```text
D ; E |- StaticTarget(u,A) => S
```

when declaration context `D` and the current residual environment `E` resolve
`u` to a checked finite circuit `S` on `bits(A)` axes. This is metanotation,
not a new source type or API. The premises are:

1. `u` is absent from `dom(E)`, including spent entries; resolve it using the
   current module and its explicit imports.
2. Either it names a declaration whose **declared** classification is
   `unitary`, with exactly the signature `(Q<A>) -> Q<A>`, or it names sealed
   `std::quantum::h/x/z/t` and `A=Bit`. Exact type-tree equality is required;
   equal wire width alone is insufficient. An `iso` identity is ineligible.
3. Check the whole body from one fresh symbolic input in a separate register
   store. Enforce normal calls, types, ownership closure, effect bounds, and
   the acyclic dependency rule. It must return one `Q<A>` and no leftover
   ownership. A static target cannot access caller values.
4. Independently verify the resulting unary IR with declared effect `Unitary`;
   flatten only supported finite constructors into `S`, including the final
   output-axis permutation. All width, expansion, and work limits must hold.

Closed internal `CBit` constants, Boolean operators, and classical branches
are supported. With no classical ports or observations, their values are
statically determined. After both arms pass source and IR verification,
flattening selects the arm, transfers its complete simultaneous phi interface,
and retains output order and phase. This does not enable classical parameters
or measurement-dependent static targets. See [F2](static-semantics.md#3-f2-flattening-and-final-output-order).

Thus a signature alone is insufficient. These premises are required even for
zero repetitions and both arms of a `qif`. The emitted enclosing IR is also
independently verified; static-body verification does not replace that check.

### Expression rules and evaluation order

Abbreviate a successful resource judgment as
`D ; E ; F ; R |- e => v:T ! eps ; E' ; R'`. Freshness history is implicit
here and must satisfy the full resource rules. For a circuit `S`, `Inv(S)`
inverts it and `Repeat(n,S)` concatenates `n` copies, with an empty sequence
for `n=0`.

```text
D ; E ; F ; R |- e => q(s,A):Q<A> ! eps ; E1 ; R1
D ; E1 |- StaticTarget(u,A) => S
---------------------------------------------------------------------- ADJOINT
D ; E ; F ; R |- adjoint(u,e) => q(s,A):Q<A> ! max(eps,Unitary) ; E1 ; R2

D ; E ; F ; R |- e => q(s,A):Q<A> ! eps ; E1 ; R1
D ; E1 |- StaticTarget(u,A) => S       n is a permitted static literal
---------------------------------------------------------------------- REPEAT
D ; E ; F ; R |- repeat_static(n,u,e)
    => q(s,A):Q<A> ! max(eps,Unitary) ; E1 ; R2
```

`R2` is `R1` with a fresh token for slot `s` and the same ordered wires and
basis type. Emit `ApplyUnitary` with `Inv(S)` or `Repeat(n,S)`. These rules
resolve the target **after** evaluating `e`, using `E1`. Zero repetitions
still evaluate `e`, check `StaticTarget`, and pass its ownership through once.

```text
D ; E  ; F        ; R  |- ec => c:Q<Bit> ! eps_c ; E1 ; R1
D ; E1 ; F ++ [c] ; R1 |- eq => q:Q<A>   ! eps_q ; E2 ; R2
own(c) and own(q) are disjoint; their live wire sets are disjoint
D ; E2 |- StaticTarget(u0,A) => S0
D ; E2 |- StaticTarget(u1,A) => S1
---------------------------------------------------------------------- QIF
D ; E ; F ; R |- qif(ec,eq){0=>u0,1=>u1}
    => (c',q'):(Q<Bit>,Q<A>) ! max(eps_c,eps_q,Unitary) ; E2 ; R3
```

First evaluate and check the control as `Q<Bit>`, then evaluate the target
with the control held in the opaque pending frame. If the target expression
contains a classical branch, its complete phi interface must include that
control; its register metadata can change while the pending holder survives.
Resolve and check `u0`, then `u1`, in the same residual environment `E2`.
Neither target becomes unchecked because of a known control state. Only after
both checks, emit `Join; ApplyUnitary; Split`, returning the control and target
in that order. The joins/splits create new slots/tokens while preserving the
logical wire interface. Remap each target axis `j` to joined axis `j+1` and
add a control at axis `0`, false for `S0` and true for `S1`.

Accepted examples are `adjoint(t,q)` and `repeat_static(0,h,q)` on a live
`Q<Bit>`. Rejected examples include `repeat_static(0,missing,q)`,
`adjoint(init0,q)`, static transformation of a function with a classical
parameter, and `qif(q,q){0=>h,1=>h}`. In
`unitary fn bad(u:Q<Bit>)->Q<Bit>{adjoint(u,u)}`, evaluating the input spends
local `u`; its tombstone still hides any same-named function, so the static
target is rejected. Invalid function bodies and invalid second `qif` targets
are rejected even when a run would not use their operation.

<a id="位相を保持する有限ir"></a>

## Phase-preserving finite IR

The target representation is `ApplyUnitary` with a flat sequence of
`CircuitStep`s. Each step has distinct basis controls and either a Hadamard or
a finite monomial operator. On its specified ordered axes, a monomial means

```text
M|x⟩ = exp(iπ phase[x]/4) |permutation[x]⟩.
```

The verifier checks a total permutation table, phase exponents in `0..7`,
axis bounds and uniqueness, and disjoint control/action axes. The empty-axis
table `[0]` can also carry a phase, so scalar phases on `Q<Unit>` survive.
This representation does not accept arbitrary matrices.

Inversion reverses step order, leaves Hadamards unchanged, and uses
`p⁻¹[p[x]]=x` and `phase_inv[p[x]]=-phase[x] mod 8`. Control adds the
corresponding basis control to every step. Output-axis reordering caused by
`split/join` is part of the operator and is normalized before inversion or
control. The [static semantics](static-semantics.md) states the exact operator
lemmas for flattening, adjoint, control, finite repetition, and computed phases,
including their premises and limits.

Existing injective lifts can be transformed only at equal width, when their
tables are permutations. Two-argument `with_computed` must pass its existing
structural certificate before conversion to a finite phase action. The
[three-argument semantic extension](semantic-contracts-v0.1.md) first passes
independent checking of its retained W and logical u, then contributes u's
steps on the source axes. Adjoint/control/repetition act on that checked
logical circuit, including output order and scalar phase. This substitution
uses `C_f† W C_f E_0=E_0 u`; finite regression evidence does not prove every
Rust transformation correct. No unconditional
auxiliary-release instruction is introduced. Existing `QuantumIf` IR remains
available; the new surface forms use `ApplyUnitary` to represent finite bodies.

An explicit [function-contract call](function-contracts-v0.1.md) remains a
`CircuitAction::Contract` referencing the same checked evidence. Flattening
remaps its ordered interface, reversal toggles its adjoint flag, and coherent
control appends disjoint predicates. Repetition reuses the evidence. Its exact
meaning and retained implementation therefore remain inspectable in final IR.
An ordinary contract invocation reuses its receipt; transforming a circuit is
subject to the comparison below.

Each statically transformed register is limited to 12 bits; `qif` counts the
control and target together. This is separate from the program's live-wire
limit. Duplicated step tables and controls count against the work budget. Raw
IR is rechecked regardless of its origin. General machine-checked meaning
preservation for the transformation remains an open obligation.

**0.2.0 finite comparison:** for a concrete `adjoint` or `repeat_static` interface
of at most six bits, and `qif` including its control of at most six bits, extract
the original phase-fixed matrix from independently verified raw IR using the
contract extractor, separately from frontend flattening. Compare the emitted
steps with the adjoint, integer matrix power, or control-block matrix
respectively. Cache the original closed function meaning by resolved function
identity within one compilation; a static parameter uses its checked receipt.
Abstract generic checking has no concrete matrix, so the comparison occurs at
instantiation. Interfaces above six bits retain structural checking; no larger
dense matrix is built. No function name grants acceptance.

The original function must satisfy the finite extractor's 1,024-operation/step
and dependency-depth bounds. Emitted flat repetitions can be checked in chunks
of 1,024 steps, without changing their order. All comparisons spend the shared
10,000,000-unit compilation budget; overflow/capacity exhaustion rejects, and
unequal phase, axes or control blocks report a contract error. These additional
finite capacities are part of the 0.2.0 MINOR migration. Inversion uses the
existing audited contract routine. This reuses an existing equation checker;
it adds neither a semantic acceptance rule nor a general frontend proof.

<a id="最初の利用対象"></a>

## Initial applications

Fixed-width QFT and two-/three-bit QPE are implemented as ordinary `.qli`
definitions. Angles are exact symbolic multiples of `π/4`, using integer
repetitions of the existing `T`. Arbitrary angles, sized types, and general
operation parameters are deferred. QPE measures and consumes its phase
register and returns the target ownership after measurement.

<a id="通常定義と公開契約"></a>

### Ordinary definitions and public contracts

| Classification and name | Type, ownership, and effect | Meaning, acceptance, rejection, and IR |
| --- | --- | --- |
| Ordinary definition `std::transforms::qft2` | `Q<(Bit,Bit)> -> Q<(Bit,Bit)>`, `Unitary`; consume and return the input. | `F_4`. Accept the two-bit type; reject other types and reused ownership. Expand to H, controlled T, and Split/Join. |
| Ordinary definition `std::transforms::qft3` | `Q<((Bit,Bit),Bit)> -> Q<((Bit,Bit),Bit)>`, `Unitary`; the same ownership rule. | `F_8`. Accept the three-bit type; reject other types and reused ownership. Expand ordinary calls and ApplyUnitary. |
| Example ordinary definition `evolution::evolve` | `Q<Bit> -> Q<Bit>`, `Unitary`. | The initial body is T. Replace its body to specify the QPE target statically. Reject a body containing observation. |
| Example ordinary definition `estimation::phase2` | `Q<Bit> -> ((CBit,CBit),Q<Bit>)`, `Observe`. | Two-bit QPE. Measure and consume only the phase register, returning the target. Accepted as an instrument without an eigenstate premise. Reject a call in a Unitary context or implicit discard of the returned target. |
| Example ordinary definition `estimation::phase3` | `Q<Bit> -> (((CBit,CBit),CBit),Q<Bit>)`, `Observe`. | Three-bit QPE with the same type, resource, and effect conditions. Expand to controlled powers, `adjoint(qft3,...)`, and MeasureZ. |

The QFT convention is
`F_M|x⟩=Σ_y exp(2πixy/M)|y⟩/√M`. Bits have weights `1,2,4` from left to
right. Apply `U^(2^j)` controlled by phase bit `j`, then the inverse QFT.
For `U|u⟩=exp(2πiφ)|u⟩`, the probability of result `y` is
`|Σ_(r=0)^(M-1) exp(2πir(φ-y/M))/M|²`. The
[planned QPE contract](stdlib-roadmap.md#42-phase_estimate-位相に関するインストルメント)
specifies the post-measurement action on general inputs and reference systems.
See the [primary phase-estimation reference, §5](https://arxiv.org/abs/quant-ph/9708016).

Private helpers in `transforms` are the ordinary unitaries
`identity:Q<Bit>->Q<Bit>` and `phase_quarter:Q<Bit>->Q<Bit>`, applying identity
and two T gates respectively. The QPE example's private helpers are an identity
of the same type and `square`/`fourth`, which apply `evolve` two/four times.
All receive the same checks.

QPE is a finite example with replaceable static source dependencies, not yet a
general standard-library skeleton. It supplies no size parameters, arbitrary
angles, eigenstate proofs, or automatic choice of precision and failure rate.

<a id="確認した結果"></a>

### Verification record

```sh
cargo run --bin qleisli -- run examples/phase_estimation
cargo test --test static_operations
```

The published example uses T's eigenstate `|1⟩` and returns `1001` with
probability one. Its first `100` encodes integer 1 and phase `1/8`; the final
`1` is a Z measurement of the returned target. This display is not conventional
most-significant-bit-first binary notation.

The [12 static-operation tests](../tests/static_operations.rs) cover all eight
phases, the distribution of a non-grid phase with two-bit QPE, correlations
with an external reference, coherence within degenerate phase subspaces,
inversion of output-axis reordering, positive/negative reflections under
control, empty-register phases, repetition counts `0/1/4,096`, and rejection
of type, effect, resource, and dependency-cycle errors. They also check static
expansion depth and work limits on a 2 MiB stack. Raw IR with incomplete or
noninjective tables, out-of-range phases, duplicated or out-of-range axes, or
control/action overlap is rejected.

These numerical comparisons use tolerance `1e-12`. Success on one input does
not establish general machine-checked meaning preservation or arbitrary-
precision QPE. The additional [exact finite matrix checks](../tests/static_semantics.rs)
exercise the static-translation correspondence described in
[static-semantics.md](static-semantics.md). They preserve exact phases on their
finite cases; they do not prove correctness for arbitrary source programs.

**Historical A2 validation (2026-09-26):** `cargo test --all-targets` passed
all 92 tests (algorithms 7, compiler 17, parser 8, project 8, reference execution
13, static operations 12, IR verification 27). `cargo fmt --check`,
`cargo clippy --all-targets -- -D warnings`, and `git diff --check` also passed.
Documentation links, column counts of new tables, and the nine public bundled
definitions present at that milestone were checked. These are the A2 milestone
counts, not the current repository totals; see the
[conformance record](specification-status.md) for subsequent validation.
