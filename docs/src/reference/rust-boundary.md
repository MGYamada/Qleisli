# Rust familiarity and quantum meaning

A **false friend** is a Rust spelling or habit whose Rust reading would
misdescribe a quantum operation in Qleisli. This chapter states, for each
false friend, the Rust reading, the Qleisli rule, and the diagnostic or the
correction.

Qleisli reuses familiar syntax for familiar semantics. It uses distinct syntax
where the familiar intuition would misdescribe a quantum operation. A familiar
spelling is not evidence of a physical operation, an ownership transition or a
checked mathematical law. The
[inference and discovery boundary](architecture.md#inference-and-explicit-discovery)
connects predictable classical mistakes to diagnostics and explicit quantum
contracts.

The chapter specifies this boundary for edition 2026 under the
[authority hierarchy](authority.md). It uses the [type model](type-model.md)
and the [functional boundary](functional-boundary.md). It distinguishes
implemented rules from grammar that is absent.

The chapter uses these terms:

- A **quantum owner** is a value of type `Q<A>`. A value is
  **quantum-containing** when its type contains a quantum owner at any depth.
- A quantum owner is **live** from its creation until an operation consumes
  it.
- A construct is **absent** when neither the source grammar nor the builtin
  catalog contains it. A parser refusal or a name refusal for an absent
  construct does not implement its future ownership law or adopt a pending
  design. It does not forbid a valid user-defined identifier with the same
  spelling.
- The **source checker** is the common checker of both
  [routes](diagnostics.md#routes). The **native checker** is the independent
  Lean checker.
- A **profile** is a bounded implementation of checking or lowering, with its
  own limits. The finite project profile lowers source on the project route.
  The selected Raw profile and the selected hierarchy profile lower source on
  the selected-entry route.

A rule names the diagnostic code of a program that breaks it. The two routes
report some failures with different codes. A rule then gives the
project-route code first, as in `unknown_name` or `name`.
[Codes](diagnostics.md#codes) lists both vocabularies.

## Ordinary data may be ignored

Rust's ordinary owned values are affine: a program uses each at most once and
may leave it unused. Qleisli's ordinary `Bit`, `Unit` and products that
contain only ordinary data are unrestricted. An unused ordinary value needs no
physical operation.

Rules:

- A program may reuse ordinary data, leave it unused, or match it with `_`.
- A program need not insert a physical `discard` for an unused classical
  `Bit`.
- Ignoring an ordinary measurement result does not destroy another live
  quantum owner. The earlier measurement contributes Observe to the principal
  effect of the body.
- This rule introduces none of Rust's `Drop`, `Clone`, `Copy` or trait
  machinery.
- The source has no built-in `drop`, `forget`, `clone`, `copy` or `default`
  function. These identifiers are ordinary names. They resolve by the same
  declaration, import and lexical rules as other identifiers.
- A call of an unresolved `drop`, as in `drop(0)`, is a name error about an
  absent builtin (`unknown_name` or `name`). It is not a quantum ownership
  error.
- A user definition named `drop` is valid. Its name grants no special
  permission.

The checker accepts these two functions. They use ordinary binding, tuple
construction and wildcard matching:

```qli
fn duplicate(b: Bit) -> (Bit, Bit) { (b, b) }

fn ignore(b: Bit) -> Unit {
    let _ = b;
    ()
}
```

The checker accepts this observing function. Its body explicitly means
measurement:

```qli
observe fn drop(q: Q<Bit>) -> Bit {
    measure_z(q)
}
```

The function consumes its quantum input through its checked body. It is not a
quantum destructor or an escape from effect inference.

## Explicit construction instead of Default

In Rust, `T::default()` returns the default value of a type that implements
`Default`. Qleisli has no such abstraction for a quantum-containing type.
Preparation is an explicit operation, and each preparation has its own
contract.

| Preparation | Result and action |
| --- | --- |
| `init0()` | A fresh zero qubit, with Isometry action |
| `unit(())` | One fresh zero-axis `Q<Unit>` owner with exact coefficient `+1` and Unitary action. It allocates no physical wire. |
| `empty()` | The separately typed `Q<Bits<0>>` owner |

Rules:

- A Rust-like `Default` abstraction is unavailable for every runtime type that
  contains a live quantum owner. This includes `Q<T>`, `Q<Unit>`,
  `Q<Bits<0>>` and ordinary products that contain any such field.
- Ordinary and static basis data are not quantum resources. `0`, `()` and
  explicit ordinary constructors are ordinary data, without preparation and
  without a quantum owner.
- The checker inserts no default conversion between these types.
- The language has no general trait or impl, no associated `Default` call and
  no generic `Default` bound.
- The checker applies the same complete source checks to a generic Basis body
  as to any other body. This includes a declaration that the selected entry
  does not call.
- Neither zero physical width nor an ordinary `Unit` argument makes the
  returned owner unrestricted.
- Explicit `finish` preserves the preceding scalar phase. Checked scoped
  cleanup keeps its all-input fixed-state contract.
- Default construction provides no hidden clean workspace and no cleanup. The
  source provides checked workspace only through the scoped forms `clean`,
  `dirty` and `with_computed`.
- A source effect is not a resource bound. Quantitative resource certification
  is a separate obligation.
- A program may name an ordinary function `default`. Its caller keeps the
  effect of its body, and the checker rejects a false Unitary assertion
  (`effect`).
- A function named `default` that returns ordinary data gains no quantum
  action from its spelling.
- A name, a return-type annotation or a generic parameter cannot grant
  allocation, duplicate a quantum result, or excuse an abandoned owner.
- A call of an unresolved `default` is a name error (`unknown_name` or
  `name`).

The checker accepts this function. It has explicit preparation, and its
principal effect is Isometry:

```qli
use std::state::init0;

fn default() -> Q<Bit> { init0() }
```

## Ordinary relations and live quantum owners

In Rust, `==`, `<` and hashing act on values through the `PartialEq`, `Eq`,
`PartialOrd`, `Ord` and `Hash` traits. A live `Q<T>` has no such relation.

Rules:

- A live `Q<T>` has no ordinary value equality, ordering or hashing inherited
  from `T`. This includes `Q<Unit>`, `Q<Bits<0>>` and products that contain a
  quantum owner.
- Owner and provenance IDs that the compiler uses internally, physical wire
  IDs and logical wire IDs are distinct bookkeeping data. A comparison of them
  does not compare quantum states, and it implements no source operation on
  `Q<T>`.
- Runtime expression syntax has no `==`, `!=`, `<`, `<=`, `>` or `>=`
  operator, even on ordinary values (`parse`). These tokens are available in
  their specified static Nat predicates.
- A program may compare ordinary `Bit` values with the Boolean operations.
  Such a comparison acts on ordinary values, including explicit measurement
  results. It does not read a quantum owner without observation.
- Coherent basis comparison must be an explicit reversible operation with its
  own ordered input and output, effect and phase contract.
- State comparison, tomography and testing have separate procedures and
  statistical or operational contracts. No comparison operator selects one.
- There is no built-in `hash`, no general trait mechanism and no `Eq`, `Ord`
  or `Hash` instance for live owners. A call of an unresolved `hash` is a name
  error (`unknown_name` or `name`).
- A user-defined or imported function named `hash` is an ordinary checked
  function. Its name grants no special semantics.
- Static descriptions, evidence IDs and ordinary values keep the comparisons
  that their types and APIs support. This section invents no missing ordinary
  operator. It does not turn a comparison of internal IDs into quantum-state
  equality.
- A comparison diagnostic explains the distinction conditionally, because
  parsing does not establish the operand types. The explanation for an
  unresolved `hash` does not infer its argument type, and it does not
  intercept a resolved ordinary declaration.
- Neither diagnostic inserts a measurement, copies an owner or exposes an ID.

The checker accepts this comparison of ordinary values:

```qli
classical fn equal(a: Bit, b: Bit) -> Bit { not(a xor b) }
```

The basis language can express the coherent comparison
`|a,b,t> -> |a,b,t xor [a=b]>`. That operation keeps both input values and
accepts either initial target value. It is not a test that two arbitrary
quantum states are equal.

## Quantum owners require an explicit transition

Rust drops a value that is live at the end of its scope. Qleisli has no such
implicit end for a quantum-containing value. `Q<A>` is linear: a program must
consume each quantum owner once, through the result or through an explicit
transition.

The first table lists the Rust habits that lose or duplicate a value.

| Rust habit | Rust reading | Qleisli rule | Diagnostic |
| --- | --- | --- | --- |
| Leaving a value unused | Rust drops the value at scope exit. | A quantum-containing value must not be live at function exit or at local scope exit. | `ownership` |
| `let _ = q;` | `_` binds nothing, and the value stays in `q`. | `_` must not match a quantum-containing value. | `ownership` |
| `q;` | The statement moves the value and drops it. | An expression statement must not abandon a quantum-containing value. | `ownership` |
| `let q = e;` over a live `q` | The earlier binding stays alive until scope exit. | A binding must not shadow a live quantum-containing binding. | `ownership` |
| A second use of a value | Rust rejects a use after a move unless the type is `Copy`. | A program must not copy a quantum-containing value. | `ownership` |

The second table lists the explicit operations that end or replace an owner.
Its signatures are interface descriptions, not first-class arrow syntax.

| Explicit operation | Interface and effect | Meaning |
| --- | --- | --- |
| `measure_z(q)` | `Q<Bit> -> Bit`; Observe | It consumes the original logical owner and returns the Z outcome. It does not return a quantum owner or silently select one outcome. |
| `discard(q)` | One `Q<A> -> Unit`; Observe | It explicitly loses the quantum information of that subsystem by the specified partial trace. It is not proof of clean return. |
| `std::state::reset(q)` | `Q<Bit> -> Q<Bit>`; Observe | It ends the original logical owner and returns a fresh owner prepared in zero. The result is linear, and the program must return it or consume it explicitly. |
| `with_computed(...) { ... }` | A checked scoped construction with its own exact cleanup premises | It returns the data owner. It discharges its private auxiliary only through the admitted compute/use/uncompute rule. |
| `adjoint(U)(q)` | It consumes its input and returns an owner | It reverses the specified operation only with the required checked access (`capability` or `access`). Uncomputation alone does not discharge the returned owner or prove it clean. |
| Scope exit | A lexical boundary | It requires complete owner accounting. It performs none of the physical operations above. |

Recognition by the source checker and support in a requested profile are
distinct. The [primitive inventory](primitive-boundary.md) and
[Status and limits](#status-and-limits) state the support of each profile.

Rules:

- `Q<A>` is linear, including `Q<Unit>` and `Q<Bits<0>>`. A product that
  contains any quantum owner is also linear, even when that owner is nested
  among ordinary fields.
- Zero physical width removes neither the ownership obligation nor the
  scalar-phase obligation.
- The [disposal diagnostics](#conditional-teaching-diagnostics) explain the
  obligation at the original binder or use that triggered the rejection.
- Ordinary `let` means binding. `let q = h(q);` is valid: the right-hand side
  consumes the preceding owner and returns the replacement before the binder
  is introduced. `let q = init0();` must not shadow a preceding live `q`.
- This distinction introduces no assignment to places, no temporary reference
  and no automatic quantum destruction.
- Separate owner names do not imply separate physical states. Observation or
  disposal of one subsystem must keep its specified action on an arbitrary
  joint state. That state includes correlations with every retained owner and
  external reference.
- A name, a lifetime, a sampled result or an assertion of unitarity cannot
  establish cleanliness.
- There is no supported standalone `release(q)` and no free-standing
  `Release0` IR constructor. A diagnostic must not recommend that invented
  call.
- Explicit `finish` for `Q<Unit>` and `consume_empty` for `Q<Bits<0>>` keep
  their exact structural contracts. Neither is a general clean-release or
  discard API. Preceding scalar work stays in the composed meaning.
- A change of spelling to `drop(q)` cannot justify any of these different
  operations.

The checker accepts this finite observing body. It chooses reset and then
explicitly consumes the fresh result:

```qli
use std::state::reset;

observe fn reset_then_measure(q: Q<Bit>) -> Bit {
    let fresh = reset(q);
    measure_z(fresh)
}
```

The checker rejects the statement `reset(q);` (`ownership`). The statement
abandons the fresh quantum result.

## Signal registers remain in the interface

A **signal register** is an ordinary linear quantum owner in the semantic
interface of an operation. Scratch workspace differs: it has a declared
restoration contract. The word *ancilla* does not determine a cleanup
obligation.

For ordered signal and system spaces `S` and `D`, an exact block-encoding
contract can state

```text
(<0|_S tensor I_D) U (|0>_S tensor I_D) = A / alpha.
```

The projection in this mathematical equation performs no measurement. It
postselects no successful branch, and it does not release `S`.

Rules:

- Clean workspace must return exactly to its specified fixed state.
- Dirty workspace must restore its arbitrary input state and its reference
  correlations.
- A signal register need not return to zero unless the interface separately
  requires it.
- The caller owns the full output of `U`, including the signal register.
  Dropping the signal register changes the channel on the other owners and
  requires explicit Observe semantics.
- A signal register counts throughout its live interval. The count includes
  its width, gates, depth, measurement, and the target and layout costs under
  the stated resource model.
- Renaming a signal register to *ancilla*, or excluding it from a cleanup
  contract, cannot remove those costs.
- A quantitative resource bound is checked separately. The block equation and
  the ordinary ownership rules alone do not prove it.
- This section defines no `signal` primitive, no further ownership kind, no
  general `BlockEncoding` API and no automatic block-encoding checker. A later
  block-encoding, LCU or QSVT contract can specify signal subspaces and
  normalization with these ordinary owners.
- Source workspace, extra backend synthesis workspace and an exposed library
  signal interface are separate roles with their own obligations.
- EXACT-2026-01 applies. An approximation error certificate cannot replace an
  applicable exact equation or an exact clean-return obligation.

For example, apply H to a one-bit signal and then CNOT from signal to system.
The signal-zero block is exactly `I / sqrt(2)`, but the input `|0,0>` produces
`(|0,0> + |1,1>) / sqrt(2)`. The signal is not clean scratch. Returning both
owners is a valid Unitary interface.

## Explicit clean and dirty scopes

```text
WorkspaceScope ::= "clean" "(" Expr "," Name ")" ScopeBody
                 | "dirty" "(" Expr "," Expr "," Name ")" ScopeBody
ScopeBody      ::= "{" "|" Ident "," Ident "|" BlockContents "}"
```

A **workspace scope** gives its body one scratch `Q<Bit>` beside one data
owner. It has two forms:

- `clean(data, logical) { |data, scratch| body }` supplies a fresh `Q<Bit>` in
  `|0⟩` and returns the data owner.
- `dirty(data, scratch, logical) { |data, scratch| body }` takes an existing
  `Q<Bit>` and returns the ordered pair of owners.

`logical` names the closed Unitary action on `Q<A>`.

`clean` and `dirty` are contextual words. Each begins a workspace scope only
before a parenthesized argument list that a `{` follows. Elsewhere each is an
ordinary identifier.

Rules:

- The data argument must be one `Q<A>` owner, and the scratch argument of
  `dirty` must be a `Q<Bit>` owner (`type_mismatch` or `type`).
- `logical` must name a Unitary operation on `Q<A>` (`effect`).
- The two binders must be distinct (`parse`).
- The body must return `(Q<A>, Q<Bit>)` in data/scratch order and must have
  Unitary effect (`effect`).
- The body must return the data owner and the scratch owner that the scope
  binds. The checker rejects a body that leaves either owner live
  (`ownership`). The [disposal diagnostics](#conditional-teaching-diagnostics)
  identify that owner and explain the return contract of the scope.
- Clean release requires the exact logical action on the zero-initialized
  subspace, with the same zero scratch at exit.
- Dirty return requires identity on the entire scratch interface, including
  phase and correlations with an external reference.
- The native checker checks the original body and the logical action against
  the Raw interval of the scope. When it rejects the equation (`contract`),
  the diagnostic of either route reports which restoration contract failed.
- Access authority, restoration and resource accounting are separate
  obligations.
- Inside a workspace body, `unit(())` creates a logical `Q<Unit>` owner and
  `finish` consumes the exact owner. Both actions have coefficient +1 and use
  zero physical axes. The source checker records their owner history and
  checks the ordered returned owners.
- A target resource certificate also needs the routing schedule and the costs
  under the gate set of that target.

> **Implementation note.** The finite checker records the whole live Raw frame
> at scope entry and the peak that includes fresh scratch. It records
> preparation, clean release, the two predicate passes in the clean packet,
> and the literal body steps. Dirty scratch is already live at entry. The
> checker counts circuit references through their checked physical
> implementations, including nested predicate passes. For a circuit-backed
> `with_computed`, the expanded body counts include the literal forward
> circuit, the protected uses and the inverse circuit.

The checker accepts this program. Two controlled flips restore the scratch to
zero and act as the identity on the data:

```qli
use std::gate::cnot;
unitary fn logical(q: Q<Bit>) -> Q<Bit> { q }
pub unitary fn main(q: Q<Bit>) -> Q<Bit> {
    clean(q, logical) { |data, scratch|
        let (data, scratch) = cnot(data, scratch);
        cnot(data, scratch)
    }
}
```

The checker rejects this program (`ownership`). The body returns a fresh owner
of the required type and leaves the original `scratch` live:

```qli
use std::state::init0;
pub unitary fn client(q: Q<Bit>) -> Q<Bit> {
    clean(q, h) { |a, scratch| (h(a), init0()) }
}
```

## Checked cleanup is a separate contract

```text
ComputedScope ::= "with_computed" "(" Expr "," Name StaticArgs? ")"
                    "{" "|" Ident "|" BlockContents "}"
                | "with_computed" "(" Expr "," Name StaticArgs? "," Name ")"
                    "{" "|" Ident "," Ident "|" BlockContents "}"
```

A **computed scope** computes a predicate of its source data into one private
auxiliary `Q<Bit>`, runs its body, and uncomputes the auxiliary. The
two-argument `with_computed(source, predicate)` exposes the auxiliary to the
body and protects the source data. The three-argument form also supplies a
logical operation, and it exposes a data binder and an auxiliary binder.

Rules:

- The source must be one `Q<A>` owner (`type_mismatch` or `type`).
- The predicate must be a total `classical fn` with one ordinary argument of
  the exact basis tree of the data and with result `Bit`. Another parameter
  count is `arity`. Another type is `type_mismatch` or `type`.
- The scope returns the data owner.
- The three-argument form checks the bounded exact **computed-relation
  contract**. Let `E_f` embed each data basis value as `|x,f(x)>`. The use
  circuit `W` must satisfy `W E_f = E_f V` for the specified logical action
  `V`, with exact coefficients, phase and ordered axes.
- The surrounding compute/uncompute construction then justifies the return of
  the auxiliary to zero.
- A Unitary annotation or the names of the binders do not supply this
  equation.

> **Implementation note.** A body that is already a canonical empty, Z or T
> body keeps its complete original token chain and the protected native
> check. For another supported auxiliary body, a fresh native unitary leaf
> check reconstructs the complete original one-Bit fragment and its
> dependencies against the exact eighth-root diagonal matrix. A second native
> leaf checks a canonical witness that is built from the exact scalar, Z and T
> actions emitted in the protected scope. Both checks keep both diagonal
> entries and the full phase.
>
> Chunking only constructs an untrusted matrix proposal. The native equation
> never substitutes checked chunks for the original body.
>
> The retained `SourceUnitaryEquation` associates the two native leaves, the
> names and the source snapshot for local inspection only. It is not execution
> input, an authority flag, a whole-source preservation proof or a target or
> resource certificate. Retained provenance contains the complete original
> module bytes for the relevant declaration, the bound-provider dependencies
> and the evidence dependencies. Closures share module records. This sharing
> selects receipt metadata. Project loading and checking cover all loaded
> modules, as
> [the production boundary](production-boundary.md#root-loading-and-compatibility-during-generic-migration)
> specifies.

### Finite automatic-uncomputation rule

The two `with_computed` forms admit the bounded rule of this table. The rule
adds no way to declare a parameter, a type or a binding as clean or dirty
workspace. It synthesizes no inverse for an arbitrary Unitary body.

| Premise | Required evidence or refusal |
| --- | --- |
| Computed value | One owned `Q<A>` and a total predicate `A -> Bit`, with the complete ordered basis tree retained. |
| Scoped dependencies | The two-argument body receives only its private `Q<Bit>` quantum owner. The checker rejects a capture of an outer quantum owner (`ownership`). Available classical locals are subject to the closed-fragment and effect checks. Callable dependencies keep their original source and ordinary checking. |
| Body effects and owners | The body must be Unitary (`effect`). The two-argument body must return the auxiliary owner. The three-argument body must return the data owner and the auxiliary owner in that order. A body that leaves one of them live is `ownership`. Measurement, reset, discard, lost owners and an incorrectly ordered returned frame cannot supply cleanup evidence. |
| Two-argument action | The complete auxiliary action must be exactly `diag(zeta_8^a, zeta_8^b)` in the supported profile, where `zeta_8` is the eighth root of unity `exp(i*pi/4)`. Non-diagonal factors are permitted when their complete composition satisfies this equation. The check covers both entries, including their common phase. Another action is `unsupported`. |
| General supported use | The three-argument form supplies an independent logical operation and checks the computed-relation contract for the use circuit. Merely adding a logical argument cannot make a failed cleanup equation valid. |
| Generated cleanup | The ordinary structured Raw representation must retain compute, use and inverse. The independent checker validates the rule and the dependencies. The producer cannot assert successful restoration. |
| Capacity | The checker rejects missing evidence and exhaustion of a source, dependency or exact-work limit. No reset, discard, heuristic equality or alternate acceptance path repairs the failure. |

Rules:

- The diagnostic for an unsupported two-argument action reports the missing
  diagonal contract. It points to the three-argument form, including its
  required returned owners and its cleanup equation.
- A capture diagnostic identifies the captured binding and explains how to
  pass the data through the three-argument form.
- These conditions concern restoration and provenance. They do not claim that
  `ctrl` means an unchanged state: coherent controls keep their basis sectors,
  while phase kickback may change their correlations.
- Dirty restoration requires identity on arbitrary, possibly
  reference-entangled input. This clean rule does not infer it.
- The clean obligation is exact return to the declared fixed pure state for
  every permitted data input. Under the adopted all-input channel premises,
  this is equivalent to factorization with that same fixed pure state for
  every retained external reference.
- Separation alone is insufficient. An auxiliary in a different pure state is
  separable, but it has not returned to its declared state.
- One known-input test, an approximate zero probability or an unchanged
  unknown marginal is insufficient.
- Dirty workspace instead needs restoration of its arbitrary state and its
  reference correlations. The explicit
  [clean and dirty scopes](#explicit-clean-and-dirty-scopes) state that
  contract.

> **Implementation note.** The checked Raw interval accounts for the full
> caller frame and one private auxiliary wire, including its preparation and
> its release. The resource model counts a forward predicate pass and its
> inverse, plus the emitted body steps. The certified checker uses this same
> compute/body/inverse word for the cleanup equation, and it checks the
> logical witness separately. Physical target decompositions and routing have
> their own costs.

The checker accepts both of these auxiliary bodies when the predicate is the
identity on `Bit`. They have different exact live actions:

```qli
h(x(h(a)))  // H X H = Z: diag(1, -1).
x(z(x(a)))  // X Z X = -Z: diag(-1, 1).
```

Their standalone readout probabilities can agree. Their common sign matters
under coherent control: replacing either specified operator by the other fails
its exact request (`contract`).

The checker rejects the auxiliary body `x(a)` (`unsupported`). It leaves the
computed auxiliary dirty after the inverse. Unitarity of `x` is not evidence
of clean return.

## Clean discharge, live action and Resource Safety

**Clean discharge** is the local semantic Soundness obligation that a
workspace returns to its declared clean state. It does not identify which
operation acts on the live system. **Quantitative Resource Safety** is the
separate obligation to produce finite, statically computed bounds and to
preserve them through compilation.

Rules:

- For a specified coherent operation `V`, the implementation `W` must
  separately satisfy the exact clean-subspace identity
  `W (|0>_A tensor |psi>_R) = |0>_A tensor V|psi>_R`, with the specified phase
  and arbitrary external references.
- Ordinary controlled lifting also requires the same distinguished clean state
  as the inactive branch.
- A different fixed pure workspace state does not establish that controlled
  contract. Neither does a standalone channel equality that loses global
  phase.
- The equality alone grants no inverse access and no control access.
- Reset is Observe. An observing caller cannot make a falsely Unitary reset
  helper valid.
- Scratch qubits count while live, across preparation, use and cleanup.
- Generated inverse operations and physical routing count in the bound for the
  accepted artifact.
- Ending `excl` restores operation rights to the updated live owner. It does
  not restore the input state of that owner, prove clean or dirty discharge,
  or end its lifetime.
- A surface `Unit` result must not erase a live owner from resource
  accounting.

For example, compute `CNOT(q,a)` from `|+>_q |0>_a`. A second CNOT restores
`|+>_q |0>_a`. An explicit reset of the correlated auxiliary instead produces
`(I_q / 2) tensor |0><0|_a`. Both auxiliary marginals are exactly `|0><0|`,
but an X readout of q distinguishes the live actions. This agrees with the
all-input fixed-pure-state equivalence of the
[finite rule](#finite-automatic-uncomputation-rule). That equivalence does not
require the channel on the other owners to equal an independently requested
unitary.

## Conditional teaching diagnostics

The source checker uses familiar ownership intuition to explain a rejection.
The three disciplines differ:

| Value | Discipline | May be left unused |
| --- | --- | --- |
| A Rust ordinary owned value | Affine | Yes. Rust drops it. |
| A Qleisli ordinary value, such as `Bit` or `Unit` | Unrestricted | Yes |
| A Qleisli value that contains a live `Q<T>` | Linear, under its resource contract | No, including at scope exit |

Rules:

- The source checker adds an explanation only after its unresolved-name
  rejection or its implicit-owner-loss rejection. The explanation preserves
  the original diagnostic code, source span, checking order and limits.
- The checker does not inspect or evaluate call arguments to decide whether an
  unresolved Rust-shaped name deserves a hint. `drop(q)` keeps the
  unresolved-name priority (`unknown_name` or `name`).
- A diagnostic must not describe `drop(0)` as destroying a quantum argument.
- A resolved user function receives ordinary call checks.
- A local runtime value named `drop` keeps the not-callable category
  (`type_mismatch` or `type`). The checker does not reclassify it as an absent
  builtin.
- An ownership explanation states that scope exit is not physical destruction.
  It distinguishes measurement, discard, reset and checked cleanup.
- An ownership explanation does not choose a repair on the programmer's
  behalf. Those operations have different types, effects and meanings, and a
  requested profile may not support all of them.
- Use-after-move, arity, type, effect, access and capacity failures keep their
  own categories.
- Text and JSON diagnostics describe rejections. Neither carries semantic
  evidence or grants acceptance.
- Qleisli diagnostics are part of the source interface.
- A clean or dirty scope that leaves a live owner behind describes its
  distinct scratch-return contract. A `with_computed` scope explains which
  owners its body must return for checked cleanup.
- The resource checks establish the restoration equation against the scope
  body. The explanation does not replace them.

The version-1 CLI reports the optional `ownership_boundary` object for these
diagnostics on both routes. [Refinements](diagnostics.md#refinements) gives
the record form.

| Field | Value |
| --- | --- |
| `boundary` | `affine_to_linear` |
| `reason` | `unresolved_disposal`, `implicit_quantum_disposal`, `clean_workspace_return`, `dirty_workspace_return` or `computed_workspace_return` |
| `applies_to` | `if_live_quantum_owner` for unresolved disposal. `live_quantum_owner` for an ownership or workspace rejection where the checker has identified a live owner. |

The checker rejects this function (`unknown_name` or `name`), with the reason
`unresolved_disposal`:

```qli
pub unitary fn client(q: Q<Bit>) -> Q<Bit> { drop(q); q }
```

The checker rejects this function (`ownership`), with the reason
`implicit_quantum_disposal`:

```qli
pub unitary fn client(owner: Q<Unit>) -> Unit { () }
```

## Explicit calls and receiver access

In Rust, a method call `x.f()` references or dereferences its receiver
automatically. Qleisli has no method call. A program writes quantum access at
an ordinary call site, for example `h(excl q)` or `cnot(ctrl c, excl t)`.

Rules:

- The receiver spellings `q.h()` and `target.controlled_u(control)` are
  unsupported (`parse`). The compiler does not guess which access contract
  their author intended.
- The controlled application `controlled(U)(c, q)` takes its control and its
  target as owned arguments and returns both owners. Its argument list accepts
  no access marker: the parser rejects `controlled(U)(ctrl c, excl q)`
  (`parse`).
- An ordinary wrapper function must expose its interface and pass the same
  ownership, effect and access checks. A wrapper name grants no hidden
  projection and no forwarding.
- There are no user-defined `Deref` or `DerefMut` hooks and no receiver
  adjustments.
- Method receiver syntax is absent for ordinary classical and static values as
  well. Ordinary first-order calls on those values are unaffected.
- Common source preparation admits ordinary nominal record field projection
  under the
  [type-model rules](type-model.md#opaque-basis-specialization-in-the-selected-profile).
- A method syntax diagnostic reports the unsupported form without guessing the
  type of the receiver. It conditions its `excl`/`ctrl` advice on quantum
  access. It does not mechanically rewrite a receiver into either access mode.
- Explicit call lowering follows the
  [access and evaluation rules](elaboration.md) and the native obligations of
  [whole-owner exclusive calls](#whole-owner-exclusive-calls). Receiver sugar
  supplies no alternative acceptance route and no evidence.

The checker accepts this program:

```qli
use std::state::init0;

pub observe fn main() -> Bit {
    let q = init0();
    h(excl q);
    h(excl q);
    measure_z(q)
}
```

The checker rejects this function (`parse`):

```qli
pub unitary fn client(q: Q<Bit>) -> Q<Bit> { q.h(); q }
```

## Access vocabulary and workspace contracts

**Access** is public authority to operate on a quantum owner. `excl` grants
temporary exclusive arbitrary coherent access over its exact footprint. `ctrl`
grants the distinct basis-sector-preserving coherent access. Rust's `&` and
`&mut` borrow a value through a reference. Neither is an access spelling.

Rules:

- Neither access mode means state restoration, separability or cleanliness.
- An `excl` argument does not require a `mut` binding.
- Rust `&mut` is not a Qleisli access spelling. The checker does not convert
  it to either mode.
- `borrow` is not reserved and has no builtin quantum-resource semantics. The
  parser rejects `borrow q` (`parse`).
- Clean and dirty describe independent workspace contracts. Clean discharge
  requires the specified exact known state. Dirty discharge requires exact
  restoration for every initial state and external reference.
- The end of an access discharges neither obligation.
- The workspace forms are the
  [`clean` and `dirty` scopes](#explicit-clean-and-dirty-scopes) and the two
  [`with_computed` forms](#checked-cleanup-is-a-separate-contract). Each gives
  its body one scratch or auxiliary `Q<Bit>`, and each has its own bounded
  contract.
- No parameter, type or binding can be declared clean or dirty, and
  `borrow q` is not a workspace form.
- The diagnostic for `borrow q` is a located syntax diagnostic. It does not
  infer whether Rust access or dirty workspace was intended.
- Ordinary declarations, calls and bindings named `borrow` keep normal
  checking. Their name grants no access, restoration or ownership permission.
- Consuming calls and bindings express ownership transfer. This vocabulary
  adds no standalone `move q` form.
- Internal Rust documentation may discuss normal borrowing of compiler data
  structures.

For example, an implementation on ordered owners `(D,R)` can change `D`
temporarily and satisfy the exact contract `I_D ⊗ X_R`. The sequence
`CNOT(R→D); X(R); CNOT(R→D); X(D)` does so. In contrast, `Z(D); X(R)` leaves
the marginal of a Bell-entangled `D` unchanged but changes its correlation
phase with the reference. It therefore fails that identity-restoration
contract.

## Whole-owner exclusive calls

```text
AccessCall  ::= Name StaticArgs? "(" AccessArg ("," AccessArg)* ")"
AccessArg   ::= MarkedPlace | Expr
MarkedPlace ::= ("excl" | "ctrl") Ident Selection?
Selection   ::= "[" Nat "]" | "[" Nat ".." Nat "]"
```

An **access call** is a call with at least one marked place. `h(excl q)`
temporarily supplies the live lexical owner `q` to the consuming call and
keeps the returned quantum value on the same binder. The access call itself
has ordinary type `Unit`. A joint call such as `cnot(excl c, excl t)` requires
distinct owners and returns them internally in argument order.

`excl` and `ctrl` are contextual. Each is a marker only before an identifier
in an argument position. Elsewhere each is an ordinary identifier.

Rules:

- An access marker always denotes a quantum place. Each marked argument must
  name one live lexical owner (`ownership`). The place is a whole `Q<A>`
  owner, or an index `q[i]` or a slice `q[a..b]` of a `Q<Bits<N>>` owner
  (`type_mismatch` or `type`).
- Ordinary data and tuples that contain several owners are not access places.
- Marked places must not overlap. The checker rejects duplicate owners and
  selections without a compile-time proof of disjointness (`ownership`).
- An index or a slice must satisfy the static bounds of the
  [static places](elaboration.md#static-ordered-axis-places)
  (`type_mismatch` or `size`). Indexed selections have a common AST and one
  static bounds and disjointness judgment.
- The callee must have caller-visible checked `Unitary` effect under the
  [public-effect rule](source-text.md#ordinary-function-effects-and-assertions)
  (`effect`). That effect is the public contract outside the original module
  of the callee, and independently checked internal inference inside it.
- An annotation does not override body checking. Inlining or cache reuse
  cannot sharpen an external contract.
- The result of the callee must have exactly the original owner type for one
  argument, or the ordered tuple of those owner types for several arguments
  (`type_mismatch` or `type`). Exact basis trees and the owner partition
  matter, including `Q<Unit>`. Equal bit width is insufficient.
- The callee executes once. Access closure inserts no inverse, reset, discard,
  release or fresh preparation.
- Returned values keep their changed state and phase, even across a nested
  lexical boundary.
- An access lasts for the written call. No mutable-binding marker is required.
- Consuming `q` after the access makes it unavailable as usual. Access cannot
  revive a spent or hidden owner (`ownership`).
- The checker rejects measurement through `excl` (`effect`).
- A checked mixed call may also pass `()` or a lexical `Unit` value. The
  compiler keeps the source position of every argument and restores the owners
  of the marked places in order. See
  [mixed access calls](elaboration.md#ordinary-unit-arguments-in-access-calls).
- A mixed call whose markers are all `excl` may also pass a lexical ordinary
  `Bit` value, when the selected callee lowers to a single checked ordinary
  branch. Another ordinary argument expression is `unsupported`.
- A closed finite function may declare
  [access parameters](elaboration.md#declared-access-parameters). They use the
  same original-call and returned-owner checks.
- An access call must not have more than 64 arguments (`parse`).
- Unsupported Rust reference notation receives a syntax explanation
  (`parse`): for quantum access, `excl` grants arbitrary coherent access, and
  `ctrl` requires the computational-basis sector condition. The lexer does not
  infer that the expression is quantum, and it does not rewrite `&` into
  `ctrl`.

> **Implementation note.** The finite project compiler and selected Raw
> lowering partition the parent of an indexed selection and reassemble its
> updated owners. The selected hierarchy lowering replays the structural
> interval against the original places. Selected-source preparation keeps
> `ctrl` roles as obligations with their original source identities and
> spans. `ElaboratedProgram::lower_raw_with_kernel` and selected CLI Raw
> checking require a fresh native decision for every retained concrete
> control-bearing definition and for the selected root. These decisions share
> one exact-work budget. Each control call is bound to the decoded instruction
> interval and to the original ordered owners.
>
> The checker also elaborates unused closed functions whose original resolved
> dependencies reach a control obligation. They share the call, fold, depth
> and storage bounds of the selected graph. The checker adds no public entry
> and no invented static argument, and it leaves the execution root unchanged.
> The additional bodies keep their Meaning and refinement obligations. Final
> Raw consumption checks the artifact afresh and replays its source calls.
> Diagnostics keep the module and the location of the original call.

The checker accepts this program:

```qli
use std::state::init0;
use std::gate::x;

observe fn main() -> Bit {
    let q = init0();
    x(excl q);
    measure_z(q)
}
```

### Whole-owner coherent control

`cnot(ctrl c, excl t)` marks `c` as a control place. A `ctrl` place follows
the distinct live-owner rule, the Unitary effect rule and the exact
returned-interface rule of an `excl` place. It adds the sector rule below.

Rules:

- `ctrl` requires computational-basis sector preservation. It does not require
  an unchanged quantum state, and it is not read-only access. Phase kickback
  and entanglement are allowed.
- The checker rejects H and X on a control owner (`contract`), although both
  are Unitary. CNOT preserves the sectors of its control but not those of its
  target.
- Exact scalar phase on `Q<Unit>` is retained.
- Control axes follow the original argument order and owner wire order. They
  do not follow sorted wire identifiers.
- The checker checks each call occurrence, including nested calls and unused
  concrete declarations.
- Access exit neither restores the old state nor releases workspace.
- The checker rejects overlapping arguments (`ownership`).
- A fresh native decision must succeed before the updated owners are retained.
  The complete generated program must also pass ordinary native acceptance. No
  annotation and no cached decision replaces either check.
- A missing, incompatible or failed checker refuses the program. A missing
  checker executable is `project`, or `io` on the selected-entry route.
- A native control refusal explains that control is not read-only, that phase
  kickback is permitted, and that arbitrary coherent access requires `excl`.
  This guidance does not bypass the effect, alias or interface checks.
- The supported call-formed exit points follow the
  [evaluation and owner lifetime rules](elaboration.md#evaluation-and-owner-lifetime-boundaries).

> **Implementation note.** The finite project checker and compiler submit the
> emitted call interval, the original ordered owner ports, the complete basis
> forest and the requested control axes to the native `control-owners`
> checker. For indexed and sliced arguments, the checked call interval
> starts after extraction and ends before reassembly. Its ports follow the
> exact selected owner types and their order.
>
> The selected hierarchy profile ties each original control role to the
> replayed node in the executable graph. The native composition check
> reconstructs the action of that node from the hierarchy body and the
> original finite leaf bytes. It compares the exact ordered input and output
> basis trees, including zero-width ports, before it checks computational
> sectors. The decision uses the exact eighth-root scalar ring and shares work
> with the native composition and execution-view checks. The
> `source_control_checked` field reports that scoped success.

The checker accepts this program. `t` is a control place, and the call flips
`c`:

```qli
use std::state::init0;
use std::gate::x;
use std::gate::cnot;

pub observe fn main() -> (Bit, Bit) {
    let c = init0();
    let t = init0();
    x(excl t);
    cnot(ctrl t, excl c);
    (measure_z(c), measure_z(t))
}
```

The checker rejects a program that calls `h(ctrl c)` (`contract`). H does not
preserve the computational-basis sectors of `c`.

## False-friend audit

The tables give one row for each Rust habit of the audit checklist and its
implicit-operation addendum. A cell that names a construct as absent follows
the definition at the head of this chapter.

### Disposal and duplication

| Rust habit | Rust reading | Qleisli rule | Diagnostic or correction |
| --- | --- | --- | --- |
| `drop` | `drop(x)` takes ownership of `x`, and the destructor of the value runs. | No builtin and no generic quantum destruction exist. A program may ignore ordinary classical data. A resolved user consumer, including one named `drop`, must pass the normal checks. | An unresolved `drop` is `unknown_name` or `name`. Use an [explicit transition](#quantum-owners-require-an-explicit-transition). |
| Implicit scope destruction | Rust drops a value that is live at the end of its scope. | A live quantum owner must leave through the result or an admitted explicit transition. Scope closure emits no hidden physical disposal. | `ownership` |
| `Clone` | `x.clone()` returns an explicit duplicate of `x`. | No trait and no builtin exist. A reusable static description does not contain a live owner. | A duplicate use of a live owner is `ownership`. |
| `Copy` | A use of a value of a `Copy` type duplicates it, and the original stays usable. | A program may reuse ordinary data. A quantum-containing product is linear. No Rust marker trait is imported. | A second use of a consumed owner is `ownership`. |
| `forget` / `mem::forget` | `mem::forget(x)` takes ownership of `x` and does not run its destructor. | No privileged forget operation exists. An ordinary resolved function cannot hide a live owner from the checks of its body. | An unresolved `forget` is `unknown_name` or `name`. |
| `ManuallyDrop` | `ManuallyDrop<T>` wraps a value so that Rust does not run its destructor automatically. | No wrapper type, no destructor suspension and no owner-accounting exception exist. | Account for the owner through the result or an explicit transition. |
| Destructor-like trait hooks | The `Drop::drop` implementation of a type runs implicitly when Rust drops a value. | No trait or impl dispatch and no implicit cleanup hook exist. | Checked scoped cleanup has its [separate rule](#checked-cleanup-is-a-separate-contract). |
| Conflating measure, discard, release, reset or uncompute | Scope exit and `drop` end a value by one mechanism, its destructor. | The [explicit transitions](#quantum-owners-require-an-explicit-transition) are distinct. No generic spelling and no scope exit selects among them. | Choose the transition by its type, effect and meaning. |
| `Default` | `T::default()` returns the default value of a type that implements `Default`. | `Default` is unavailable for live quantum-containing types, including `Q<Unit>` and nested owners. Ordinary and static data construction and explicit quantum preparation keep their distinct contracts. A user function named `default` is a checked call. | An unresolved `default` is `unknown_name` or `name`. See [explicit construction](#explicit-construction-instead-of-default). |

### Types, patterns and relations

| Rust habit | Rust reading | Qleisli rule | Diagnostic or correction |
| --- | --- | --- | --- |
| Unchecked casts / `transmute` | `mem::transmute` reinterprets the bits of a value as another type of the same size. It is `unsafe`. | No unchecked cast and no verification bypass exist. The checker checks exact type trees, basis tags and ordered axes. | Convert through an explicit checked operation. |
| `as` | `e as T` casts a value to another type, for example between numeric types. | The contextual `as` in `basis q as p { e }` names an ordinary basis pattern for a checked [coherent map](coherent-basis.md). It is not a Rust value cast and not an implicit physical layout conversion. General casts are absent. | Convert through an explicit checked operation. |
| `Eq` / `Ord` / `Hash` | `==` uses `PartialEq`, `<` uses `PartialOrd`, and hashing uses `Hash`. `Eq` and `Ord` add total equality and total order. | No ordinary relation exists on live quantum owners, including nested and zero-width owners. Internal IDs, ordinary values, explicit coherent comparison and state-testing procedures keep distinct meanings. | A runtime comparison operator is `parse`. See [ordinary relations](#ordinary-relations-and-live-quantum-owners). |
| Wildcard and rest patterns | `_` matches a value without binding it. `..` skips the other fields of a pattern. | `_` may ignore only unrestricted data. Every quantum-containing matched field is linear. An ordinary tuple pattern keeps its exact immediate shape. Rest patterns are absent, and a later rest pattern must not hide owners. | `_` on a quantum-containing value is `ownership`. |

### Control flow and failure

| Rust habit | Rust reading | Qleisli rule | Diagnostic or correction |
| --- | --- | --- | --- |
| Early `return` | `return e` leaves the function at once, and Rust drops the values that are live there. | No early-return construct exists. The tail expression supplies the block result. | A statement such as `return q` is `parse`. Use a final expression and explicit branches that preserve every quantum owner. |
| Panic and unwinding | A panic unwinds the stack and drops live values, or it aborts the process. | No source exception and no unwinding construct exist. A host or tool failure is not an admitted path that disposes of owners. | See the [verified-core failure model](source-text.md#checking-failures-and-quantum-execution). |
| `?`, assertions and early failure | `e?` returns early with the error or the `None` of `e`. `assert!` panics when its condition is false. | No propagation operator, no assertion builtin and no language unwind path exist. The name of a user function does not supply such behavior. | See the [checking and execution boundary](source-text.md#checking-failures-and-quantum-execution). |
| Ordinary `for` / `IntoIterator` over quantum data | `for x in e` calls `IntoIterator::into_iter(e)` and runs its body until the iterator ends. | No ordinary iterator and no trait machinery exist. Bounded `qfor static ... carry ... yield ...` threads a quantum-containing carry explicitly, and the checker checks its body even for an empty range. `for static` permits only an ordinary carry. Neither has hidden quantum capture or runtime iteration. | See [Static language](static-language.md). |

### Places, references and access

| Rust habit | Rust reading | Qleisli rule | Diagnostic or correction |
| --- | --- | --- | --- |
| Assignment to initialized places | `x = e` drops the old value of `x` and moves the value of `e` in. | A program must not assign to a quantum-containing place, including a nested product and a zero-width owner. `q = h(q)` is forbidden replacement. `let q = h(q)` consumes the old owner before it rebinds. A program must not refill a consumed binding by assignment. Ordinary and static assignment are also unsupported. Field and index assignment are unsupported syntax. | A quantum-containing destination of a bare lexical assignment is `ownership`. The checker refuses it before it checks the right-hand side. An ordinary or static destination is `unsupported`. |
| Indexing / `Index` / `IndexMut` | `a[i]` calls `Index::index` or `IndexMut::index_mut` and dereferences the result. A slice index out of bounds panics at run time. | Explicit `excl q[i]` and `ctrl q[a..b]` select statically bounded, ordered places under the [selector rules](elaboration.md#static-ordered-axis-places). They form no ordinary value and no reference. They do not move owners by bare indexing, and they use no indexing trait and no runtime bounds check. Explicit `take_bit[n,k]` and `put_bit[n,k]` consume and return owners with checked static bounds and ordered axes. | An unproved bound is `type_mismatch` or `size`. |
| Method-call autoref and autoderef | `x.f()` references or dereferences the receiver automatically to match the method. | No method-call syntax and no hidden receiver conversion exist. Quantum autoref, autoderef, `Deref`/`DerefMut` dispatch, receiver coercion and access-contract overload selection never insert or forward `excl`/`ctrl`. An explicit first-order call keeps its declared argument types and access modes. | `parse`. See [receiver access](#explicit-calls-and-receiver-access). |
| `mem::swap` / exchange / physical SWAP | `mem::swap(&mut a, &mut b)` exchanges two values in place. | Ordinary `std::gate::swap` applies a physical Bit SWAP in fixed wire frames. `std::structure::permute_axes` and `transpose_axes` reorder axes explicitly. Live binding exchange is unavailable. Matrix equality grants no unchecked routing replacement and no unchecked cost replacement. | Use the operation whose contract matches: a physical SWAP or an explicit axis map. |
| `mut` | `let mut x` permits reassignment of `x` and mutable borrows of it. | A mutable-binding marker grants no quantum access. Gates change states through consuming calls and explicit returned owners. `excl` and `ctrl` need no marker. The ordinary identifier `mut`, as in `let mut = 0`, keeps the normal name rules. | `let mut q = ...` is `ownership` for a quantum-containing value and `unsupported` for an ordinary value. |
| Shared `&` / exclusive `&mut` / `ctrl` | `&x` is a shared borrow. `&mut x` is an exclusive borrow that permits mutation. | Reference notation is absent. A call marks access with `excl` or `ctrl` on a whole owner or on a static index or slice. `ctrl` is not read-only: control may accumulate phase or entanglement. | `&` is `parse`. See [whole-owner exclusive calls](#whole-owner-exclusive-calls). |
| `borrow` versus clean and dirty workspace | A borrow gives temporary use of a value through a reference. | `borrow` has no builtin quantum-resource semantics. `excl` and `ctrl` express access. Clean and dirty express independent workspace restoration obligations. | `borrow q` is `parse`. See the [access vocabulary](#access-vocabulary-and-workspace-contracts). |

<a id="acceptance-and-evidence"></a>

## Status and limits

The source checker verifies complete declarations and bodies before concrete
eligibility. A diagnostic does not alter that judgment, issue an accepted
handle or replace the independent native Lean gate. The
[production boundary](production-boundary.md) and the
[functional boundary](functional-boundary.md) state the source,
concrete-profile and preservation limits that apply to this chapter.

### Code

| Profile | Access that the profile supports |
| --- | --- |
| Finite project | `excl` and `ctrl` on whole owners and on static index and slice arguments, with a fresh native sector check for each `ctrl` call |
| Selected Raw | The same places, with a fresh native sector check for each `ctrl` call. `lower_raw` and checker-free `emit-proposal` refuse a control obligation (`unsupported`). |
| Selected hierarchy | Bounded `excl` selections, on at most eight axes of each selected owner. Bounded `ctrl` calls of a pure entry, replayed with a fresh native sector check. |

Limits of the profiles:

- The finite project profile lowers `discard(q)` and `std::state::reset(q)`.
  The selected catalog supports neither.
- The finite check of a `clean` or `dirty` scope covers full carriers of at
  most five data bits and one scratch bit, within the shared exact-work limit.
  The project compiler reports a wider data owner, or a scope body of more
  than 1024 circuit steps, as `limit`.
- A control decision uses the bounded exact native profile. It covers at most
  six physical input bits, and the compiler budget is charged with the
  cumulative exact work.
- A closed finite declared access uses the original-body profile.
- Access exists as call-site markers on whole owners and static selections,
  and as declared access parameters. The language has no other access
  footprint and no access that outlives its call.
- In the selected Raw profile, every original control obligation must have a
  concrete call in each retained specialization of its declaration. A
  different specialization cannot supply its evidence.
- The selected Raw profile does not support an unclosed generic declaration
  with a control obligation. It does not support a control call that is
  missing in an unselected static branch or in an empty loop (`unsupported`).
- A zero-count provider with a retained body is checked independently of its
  execution count.
- A symbolic inverse or controlled transform that contains an access
  obligation is `unsupported`.
- The v5 source profile checks supported `excl` and `ctrl` calls in coherent
  block arms and static continuations. It checks them against their original
  ordered places and literal Raw intervals, including extraction and
  reassembly. The
  [production boundary](production-boundary.md#version-5-source-body-requests)
  describes the bounded v5 request.
- A supported selected root whose original lexical dependency closure contains
  `with_computed` uses the common source emitter and fresh typed native
  checks. The computed boundary and the local normalization receipts are
  intact. This route supplies no source-preservation theorem, no
  operation-formal closure and no acceptance rule.
- The two-argument `with_computed` check is subject to the native graph,
  dependency, source and shared-work limits. These include the separate
  FunctionEvidence limits on the dependencies of the body.
- Retained module records fit within 128 modules and 1 MiB, including names
  (`limit`).
- Ordinary source expansion keeps its own work limit. The normalization of a
  `with_computed` body does not make every long source fit that limit, and it
  synthesizes no inverse for arbitrary source code.
- Concrete nominal execution is gated, as the
  [type model](type-model.md#opaque-basis-specialization-in-the-selected-profile)
  states.
- The absence of trait grammar supplies no proof and no implementation of
  later trait resolution. A facility admitted later must preserve the rules of
  [explicit construction](#explicit-construction-instead-of-default).
- Integration with the external qlippy tool is outside this chapter.

### Tests

- `tests/rust_boundary_diagnostics.rs`, `tests/default_construction_boundary.rs`
  and `tests/repair_diagnostics.rs` check the refusals and the permitted
  ordinary forms of this chapter on both routes.
- `tests/exclusive_access.rs` checks access calls, and
  `tests/computed_derived_source.rs` checks the two-argument `with_computed`
  bodies.
- `tests/selected_function_contracts.rs` checks the complete exact operator of
  the `(D,R)` example through the function-contract boundary. Its separate
  Bell experiment does not replace the all-input equation, and it implements
  no workspace syntax.
- The
  [first source study](https://github.com/MGYamada/Qleisli/blob/38d3f670a5e6c6de29a60742936a03ddcc0974ae/tests/fixtures/authoring_sessions/clean-marginal-v030/README.md)
  of the reset example retains its diagnostics and numerical observations
  separately from proofs.
- The
  [small cross-algorithm study](https://github.com/MGYamada/Qleisli/blob/fd0a5e27a634ce490a6e42593b2d08f340545da4/tests/fixtures/authoring_sessions/access-algorithms-v030/context.md)
  retains complete access-call and explicit-owner pairs for fixed arithmetic,
  coherent equality, a Grover iterate, a QPE controlled-power prefix and a
  walk step. These examples use the same access rule. Their local helper names
  are not standard-library APIs. The QPE example has no inverse QFT.
- That study checks finite project execution and selected Raw support
  separately. It retains the first selected Grover profile refusals.

### Proof

- The local
  [QPTL square laws](https://github.com/MGYamada/Qleisli/blob/38d3f670a5e6c6de29a60742936a03ddcc0974ae/qptl/QPTL/Clean.lean)
  transport the exact computed-image equation through an explicit inverse.
- Their
  [Raw application](https://github.com/MGYamada/Qleisli/blob/38d3f670a5e6c6de29a60742936a03ddcc0974ae/lean/qptl-application/ProtectedClean.lean)
  obtains the original predicate, the protected uses and the event from the
  dispatch check. It derives the image equation before it evaluates the
  resulting square on arbitrary correlated amplitudes. It does not assume the
  final clean equation.
- The
  [pure Raw program theorem](https://github.com/MGYamada/Qleisli/blob/38d3f670a5e6c6de29a60742936a03ddcc0974ae/lean/qptl-application/ProtectedProgram.lean)
  also covers every physical row of certified cleanup, including zero
  amplitude on dirty auxiliary rows. It replaces both kinds of clean scope
  with their original logical actions in the checked event order, and it
  connects the result to fresh graph inspection.
- In an accepted observing Raw program,
  `Qleisli.Raw.ProtectedObserving.original_interval` identifies a checked pure
  instruction and its events in the independently read root. Each inherited
  operator column can use the checked logical action, with its recorded and
  hidden outcomes. The literal suffix and the return permutation then act on
  the updated histories. The theorem covers an original top-level interval and
  uses the exact cleanup checks.
- `Qleisli.Raw.ProtectedObserving.original_program` composes the checked
  logical replacements throughout the original observing root, including both
  arms of a nested classical branch. It follows the branch checks of the
  native checker and the independent reader. It preserves each selected
  history, the quantum owner permutation at each branch join, the classical
  phi outputs and the return order of the program. Each pure event uses the
  exact check of that event.
- For explicit `clean` and `dirty` scopes,
  `RuntimeWorkspaceRestoration.literal_action` uses the original checked Raw
  interval and the independently read logical body. It proves clean return on
  every physical row. It proves dirty identity on the scratch axis for any
  joint amplitudes, including reference correlations. The clean equation
  preserves the exact phase, and `clean_sequence` composes it across two
  accepted scopes with the same interface.
- For the checked coherent-control case, the original Raw tape must match an
  empty tape on selector zero and the exact checked clean body on selector
  one. With the scratch Bit initialized to zero, the zero branch preserves the
  incoming data and reference amplitudes. The one branch applies the requested
  live operator with its full scalar phase. Both branches have zero amplitude
  in every nonzero scratch coordinate.
- The Lean application theorem
  `Qleisli.RuntimeWorkspaceRestoration.controlled_clean_action` proves these
  equations on the same output for arbitrary joint control, data and reference
  amplitudes. Its premises require both literal sector matches and the
  successful clean-body check.

### Preservation

- The Raw results above do not establish general source composition, the CPTP
  marginal equivalence or quantitative resource bounds.
- General source preservation and quantitative resource correspondence are
  open proof obligations.
- The control check establishes no general source-preservation theorem, no
  quantitative resource correspondence and no scheduling permission.
- The rules of this chapter establish no general routing correspondence.
- The Resource Safety rules are requirements. They do not assert the
  corresponding general source, realization and resource proofs. See
  [the elaboration obligations](elaboration.md).
- The absence of implicit owner loss is not a proof of a quantitative resource
  bound or of source preservation.

### Specification review

- The rules of this chapter preserve the adopted QS, PR, quantitative RS and
  EXACT obligations: QS-2026-01, PR-2026-01, RS-2026-01 and EXACT-2026-01.
  These obligations are binding and pending.
- The rules preserve the two scoped ordinary QLV1 guarantees,
  `QS-QLV1-OWNERSHIP-2026-01` for ownership and `QS-QLV1-SCOPE-2026-01` for
  classical scope. The
  [authority chapter](authority.md#current-adoption-and-proof-status) records
  their admission.
- The rules establish no broader discharge, no primitive admission, no
  resource theorem and no release approval.
- This chapter does not decide the exit and path obligations of an early
  `return`, or the wider surface classification of ordinary Rust features.

## History

- The chapter named its release as `0.3.0-beta` in its introduction and as
  0.3.0 in its section on `Default`.
- The chapter applies the ordinary
  [#68 diagnostics decision](https://github.com/MGYamada/Qleisli/issues/68#issuecomment-6009785277).
  The audit covers the original checklist of #68 and its implicit-operation
  addendum.
- [#67](https://github.com/MGYamada/Qleisli/issues/67) and
  [#68](https://github.com/MGYamada/Qleisli/issues/68) hold the wider
  decisions and acceptance criteria. The chapter recorded them as open.
- [#251](https://github.com/MGYamada/Qleisli/issues/251) holds the broad
  import of ordinary Rust surface features, including broad ordinary trait
  ergonomics.
- The
  [#79 decision](https://github.com/MGYamada/Qleisli/issues/79#issuecomment-6009973288)
  made `Default` unavailable for quantum-containing types. It kept ordinary
  and static basis data ordinary.
- [#70](https://github.com/MGYamada/Qleisli/issues/70) covers source
  workspace, and [#120](https://github.com/MGYamada/Qleisli/issues/120) covers
  extra backend synthesis workspace.
- [#72](https://github.com/MGYamada/Qleisli/issues/72) tracked the structured
  uncomputation obligations. It is closed.
- [#157](https://github.com/MGYamada/Qleisli/issues/157) tracks the general
  source, realization and resource proofs that the Resource Safety rules need.
- The [diagnostic design rule](https://github.com/MGYamada/Qleisli/issues/225)
  uses familiar ownership intuition to explain the
  [#226 distinction](https://github.com/MGYamada/Qleisli/issues/226) between
  affine and linear ownership.
- [#196](https://github.com/MGYamada/Qleisli/issues/196) holds the exit and
  path obligations of early `return` and the wider surface classification.
- [#73](https://github.com/MGYamada/Qleisli/issues/73) records the assignment
  rule, and [#77](https://github.com/MGYamada/Qleisli/issues/77) records the
  `mut` rule.
- [#76](https://github.com/MGYamada/Qleisli/issues/76) tracked general routing
  correspondence for exchange and physical SWAP. It is closed.
- The [#71 decision](https://github.com/MGYamada/Qleisli/issues/71) uses
  the word access for public quantum operation authority.
- [#29](https://github.com/MGYamada/Qleisli/issues/29) and
  [#69](https://github.com/MGYamada/Qleisli/issues/69) tracked general access.
  Both are closed.
