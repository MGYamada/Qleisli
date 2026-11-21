# Functional abstraction and the quantum boundary

The **functional boundary** is the set of rules that decide which functional
abstractions a Qleisli program may apply to quantum data. This chapter tells
you whether a program can pass an operation as an argument, build one
operation from others, or keep a function as a value.

Qleisli admits functional construction where the construction preserves six
things: exact interfaces, linear owners, physical effects, phase, ordered
axes and the independent checking boundary. An ordinary Haskell value carries
assumptions of unrestricted duplication, closure, laziness and partiality.
Qleisli does not import those assumptions into quantum ownership.

This chapter is normative for the callable and abstraction boundary of
constitutional edition 2026. It is subordinate to the
[authority hierarchy](authority.md). Rust and Haskell influenced the design.
They are not independent semantic authorities. Familiar notation, an
annotation, a compiler result or the project's name cannot establish a
mathematical law or a constitutional certification.

The chapter specifies forms that exist and says where a program is refused.
It adds no language feature, primitive, trusted assumption, interpretation or
guarantee.

Two terms recur:

- The **common judgment** is the source check that the common checker applies
  to every program, on both [routes](diagnostics.md#routes) of the CLI.
- A **profile** is one concrete lowering path of the implementation. A profile
  may refuse a program that the common judgment accepts.

A Meaning is a declaration of the exact action of an operation.
[Checked operations](checked-operations.md) defines it.

Where a rule names two diagnostic codes, the first is the project-route code
and the second is the selected-entry code. [Codes](diagnostics.md#codes) lists
both vocabularies.

## Quantum owners

A **quantum owner** is a runtime value of type `Q<A>`. It gives the program
the use of one quantum system. An owner is one linear resource: a program
cannot copy it, and cannot drop it without saying so. An owner is **live**
until an operation consumes it.

Rules:

- A tuple that contains an owner is linear. This includes an owner of zero
  physical width.
- A program may copy or drop an ordinary `Unit`, `Bit` or `Bits<n>` value, and
  a product that contains only ordinary fields.
- A program must move, return or explicitly consume an owner under an admitted
  rule. A second use of a consumed owner is an error (`ownership`).
- Holding two owners separately does not imply that their quantum states are
  separable.
- Exact shape, phase and reference correlations are obligations. A variable
  name supplies no information about them.

The checker rejects this function with `ownership`. The ordinary tuple holds a
zero-width `Q<Unit>` owner, so the function cannot return the tuple twice:

```qli
pub unitary fn client(env: (Bit,(Q<Unit>,Unit)))
    -> ((Bit,(Q<Unit>,Unit)),(Bit,(Q<Unit>,Unit))) {
    (env, env)
}
```

## Ordinary function calls

An **ordinary function** is a declaration that a program calls with all its
static and runtime arguments, in order. A call names the declared function
and passes every argument at once. It does not go through a function value.

Rules:

- A runtime call must be first-order. The language has no general runtime
  function value or closure value, no currying and no partial application.
- A call must supply every argument. A missing argument is an arity error
  (`arity`). The incomplete call does not construct a callable that waits for
  the rest.
- A program must not call a local runtime value (`type_mismatch`; `type`).
  When a name resolves to a local value, the call does not fall back to a
  global function with the same name.
- A function can return a live owner or put it in a package. Doing so does not
  make that package a reusable function.
- Runtime arguments and right-hand sides evaluate before binding. Each one
  evaluates completely, once, and they evaluate from left to right.
- Evaluating an argument can have effects. Those effects belong to the caller,
  even when the program ignores an ordinary result.
- The common judgment applies to function bodies and to unused declarations.
  It applies to both arms of a branch and to the body of a fold with zero
  iterations. Checking both arms does not mean executing both arms.
- Outside the original module of a callee, a caller sees the public contract
  of the callee. Inside that module, a caller sees the inferred effect.
- Eligibility checks come before specialization, inlining and cache reuse.
  Inspecting the body of a callee must not sharpen its external contract.

The [source rules](source-text.md#ordinary-function-effects-and-assertions)
keep three things apart: internal principal effects, independent body
checking and checked public effects.

The checker accepts this call, which supplies both arguments:

```qli
unitary fn pair(flag: Bit, q: Q<Bit>) -> (Bit, Q<Bit>) { (flag, q) }
pub unitary fn client(q: Q<Bit>) -> (Bit, Q<Bit>) { pair(1, q) }
```

It rejects `pair(1)` and `pair(q)` in the same position with `arity`. Neither
omission constructs a partially applied callable.

The checker rejects the next call with `type_mismatch` on the project route
and `type` on the selected-entry route. The local `pair` is not callable, and
the checker does not use the global function `pair` in its place:

```qli
unitary fn pair(flag: Bit, q: Q<Bit>) -> (Bit, Q<Bit>) { (flag, q) }
pub unitary fn client(q: Q<Bit>) -> Q<Bit> { let pair = 0; pair(q) }
```

### Total classical functions

A `classical fn` declares a total, pure finite function on ordinary values. A
program calls it at run time with an ordinary call, like any other function.
[Total classical declarations](source-text.md#total-classical-declarations)
gives the grammar, the migration and the concrete profile limits.

Rules:

- The body of a `classical fn` is a restricted pure expression. It follows the
  same rules for ordered ordinary arguments and the same exact type rules.
- When an argument observes, the observation is an effect of the caller.
- A call of a classical function must not turn a live `Q<A>` into an ordinary
  `A`.
- A static Meaning or a coherent basis body may use the same definition. The
  finite-domain and injectivity checks of those forms apply there.
- An ordinary computation that is not injective grants no coherent access. It
  grants no evidence for an inverse or for control.

## Closure-shaped expressions

```text
ClosureShape  ::= "move"? "|" ClosureParams? "|" ClosureBody
ClosureParams ::= ClosureParam ( "," ClosureParam )* ","?
ClosureParam  ::= Pattern ( ":" Type )?
ClosureBody   ::= Expr | Block | "->" Type Block
```

A **closure-shaped expression** has the form `|| body` or
`|pattern, ...| body`, with an optional contextual `move`. The parser
recognizes these forms only so that the checker can diagnose them. No
closure-shaped expression is a callable value.

The diagnostic depends on what the body uses from the enclosing scope. An
**outer** name is a name that the enclosing scope binds. The body **captures**
an outer value when it uses that value.

Rules:

- A program must not use a closure-shaped expression. The checker rejects
  every one.
- When the body uses an outer live quantum owner, the checker reports
  `ownership` at that use. This rule covers a product that contains an owner,
  a `Q<Unit>` owner and a `Q<Bits<0>>` owner.
- A use of an outer owner that the program consumed earlier keeps its
  ownership error (`ownership`).
- A closure parameter can shadow an outer name, and so can a binding that is
  local to the body. Neither is a capture.
- A name supplies no evidence of a quantum type. Neither does a type
  annotation on the closure.
- When the checker finds no live quantum capture, it rejects the expression as
  an unsupported runtime closure (`unsupported`). An ordinary classical
  capture grants no callable implementation.
- The refusal infers no callable type. A quantum callable that is linear,
  one-shot or higher-order requires its own specified contracts for type,
  usage, effect and access.
- A program may use the bounded
  [static operation composition](#admitted-operation-construction) instead.
  That composition stores no live owner.

> **Implementation note.** The parser builds a diagnostic-only node for these
> forms. The common checker uses resolved lexical identities and the checked
> types of the enclosing scope to find a captured live owner at its use. Both
> source lowering paths refuse the node, so no hidden environment reaches an
> accepted artifact.

The checker rejects this function with `ownership`, at the use of `packet`
inside the closure-shaped expression:

```qli
pub unitary fn client(packet: Q<Bit>) -> Q<Bit> { let f = || packet; packet }
```

The checker rejects this function with `unsupported`. The captured `q` is an
ordinary `Bit`, and the expression is not a callable value:

```qli
pub fn client(q: Bit) -> Bit { let f = || q; q }
```

## Static operation descriptions

```text
OpType ::= "Op" "<" Basis ( "->" Basis )? ( "," MeaningName )? ">"
```

An **operation description** is a static value of type `Op<A>` or
`Op<A -> B>`. It lets a function take an operation as a parameter: the caller
chooses the operation, and the function applies it. A program uses a
description through explicit static parameters and arguments.

A **provider** is the implementation behind a description. In accepted
source, a provider is an ordinary function, with explicit static arguments
where it has static parameters.

A description is **endomorphic** when its input and its output have the same
basis tree. An **arrow** has an input tree and an output tree, which can
differ.

| Type | Reading |
| --- | --- |
| `Op<A>` | An endomorphic description on the basis tree `A`. It abbreviates `Op<A -> A>`. |
| `Op<A -> B>` | An arrow with separate input and output trees |
| `Op<A,M>` | `Op<A>` refined by the Meaning `M` |
| `Op<A -> B, M>` | The arrow refined by the Meaning `M` |

Rules:

- A description is not an ordinary runtime value. It contains no live quantum
  owner.
- Reusing a description does not duplicate its input. Each application
  consumes one owner and returns one owner.
- A program must write an arrow between two basis trees with `->`, as in
  `Op<A -> B>`. The slot after the comma holds a Meaning refinement and is not
  a general codomain. `Op<A,B>` therefore does not denote an arrow from `A` to
  `B`.
- The [type model](type-model.md#general-pure-operation-arrows) gives the
  application rules, the capability rules and the concrete profile rules of
  an arrow.

The common judgment accepts this declaration. It applies one endomorphic
operation twice:

```qli
unitary fn twice[const U: Op<Bit>](q: Q<Bit>) -> Q<Bit>
requires Applicable(U) {
    U(U(q))
}
```

The inner application consumes `q` and returns the input of the outer one.
The fragment states a generic contract. It is not a closed CLI entry, and it
proves nothing about an arbitrary supplied implementation.

Two uses of the original `q` violate ownership. The checker rejects this
declaration with `ownership`:

```qli
pub unitary fn bad[const U: Op<Bit>](q: Q<Bit>) -> (Q<Bit>, Q<Bit>)
requires Applicable(U) {
    (U(q), U(q))
}
```

## Admitted operation construction

A program builds a description from a provider and from the static
constructors below. Each row of the table says what a form requires before
the common judgment accepts it. The table covers endomorphic descriptions.
For a description with separate ports, the
[general pure-arrow rules](type-model.md#general-pure-operation-arrows) give
the rules.

| Form | Required interface and access |
| --- | --- |
| Resolved provider or explicit specialization | A permitted `Q<A> -> Q<A>` provider. The effect that its callers see is Unitary. Its static bindings and its access are checked. It captures nothing at run time. |
| `then_op(U,V)` | Both descriptions have the same exact basis `A`. The result applies them in sequence to one owner. |
| `tensor_op(U,V)` | The result has the ordered packed basis `(A,B)`. It does not implicitly join separate owners. |
| `adjoint(U)` | Construction requires `Adjointable(U)`. The description exchanges the Applicable and Adjointable capabilities of `U`, and execution requires the transferred capability. Mathematical unitarity alone supplies no API. |
| `controlled(U)` | A description on the packed basis `(Bit,A)`. Its capabilities derive from the Controllable capability of `U`. Using it needs the corresponding capability, and the use keeps phase. |
| `power(U,n)` | A static count that is checked and supported. The obligations of the child apply, including when `n` is zero. |
| `conjugate_op(C,U)` | Both descriptions have one exact common basis. The capabilities of the result derive from the Applicable and Adjointable capabilities of `C` together with the corresponding capability of `U`. |
| `checked_op(implementation, Meaning)` | The declaration-identifier form and the exact Meaning obligation of [Checked operations](#checked-operations-and-finite-materialization). |

Rules:

- Composition compares full basis trees and static premises. Equal bit width
  is not sufficient.
- Two trees that differ in tensor order or in their Unit nodes are distinct.
  `Bit` and `Bits<1>` are distinct.
- Constructing a description is distinct from obtaining executable access to
  it. [Operation access](#operation-access) gives the capability rules.
- In the common judgment, `then_op`, `tensor_op`, `adjoint`, `controlled`,
  `power` and `conjugate_op` drop an attached Meaning refinement. The
  judgment does not prove that a refinement carries over automatically.
- The spelling of a composition cannot manufacture an exact refinement or its
  discharge. Pending semantic obligations and concrete evidence are separate.
- `checked_op` keeps its own explicit attachment and checking boundary.
- A runtime local, a spent value or a quantum owner must not become a static
  provider (`type_mismatch`; `type`).
- Ordinary runtime data must not select a static size, provider or Meaning.
- The language has no general user-defined static builder.
- A successful common judgment cannot replace the independent evidence that a
  profile requires.

## Operation access

Building a description does not let a program run it. To run a description,
the program needs a capability. A **capability** is a justified way to execute
a description. The three capabilities are Applicable, Adjointable and
Controllable. The Adjointable capability gives inverse access, and the
Controllable capability gives controlled access.

A generic declaration states the capabilities that it needs. A **capability
requirement** is one of `Applicable(U)`, `Adjointable(U)` and
`Controllable(U)` in a `requires` clause. An **Op formal** is a static
parameter whose type is an operation description, such as `U` in these
requirements.

Rules:

- An Op formal starts without executable access. It has no capability.
- `requires Applicable(U)`, `Adjointable(U)` and `Controllable(U)` each
  provide one assumption for checking the generic declaration that states it.
  One requirement grants neither of the others.
- A call and a forwarded provider must satisfy the requirements of the callee.
  A concrete binding also needs its independently checked implementation
  path.
- An application or a forwarded actual argument must establish the capability
  that it requests. A missing capability is an error (`capability`; `access`).
- Constructing a description does not execute it.
- The capability requirements of the common judgment are mandatory on every
  profile. Neither a Unitary label nor a Meaning annotation grants a missing
  capability.

### Derived capabilities

A constructed description has the capabilities that the checker derives from
its parts. For the enabled endomorphic descriptions, write A(U), D(U) and C(U)
for `Applicable(U)`, `Adjointable(U)` and `Controllable(U)`. The table derives
the available capabilities of each description. Read a row as follows:
`adjoint(U)` has the A capability when D(U) is available.

| Description | A | D | C | Basis condition |
| --- | --- | --- | --- | --- |
| Op formal U | Exactly its declared A assumption | Exactly its declared D assumption | Exactly its declared C assumption | Its declared exact basis |
| `adjoint(U)` | D(U) | A(U) | C(U) | U's basis |
| `controlled(U)` | C(U) | C(U) | C(U) | Ordered `(Bit,A)` for U over A |
| `power(U,n)` | A(U) | D(U) | C(U) | U's basis and a checked supported count |
| `then_op(U,V)` | A(U) and A(V) | D(U) and D(V) | C(U) and C(V) | Identical basis trees |
| `tensor_op(U,V)` | A(U) and A(V) | D(U) and D(V) | C(U) and C(V) | Ordered product of the two bases |
| `conjugate_op(U,V)` | A(U), D(U), A(V) | A(U), D(U), D(V) | A(U), D(U), C(V) | Identical basis trees |
| `checked_op(U,M)` | A(U) | D(U) | C(U) | Exact basis agreement and the separate Meaning obligation |

Rules:

- An `adjoint(U)` description is well-formed only when D(U) is available.
  This condition is the **construction premise** of the adjoint. The checker
  tests the premise before it derives the capabilities above.
- The construction premise applies inside another description, in an unused
  static actual, in a dead source arm and under a zero power. It also applies
  to zero-width bases.
- A double adjoint requires the original D(U) capability. It also requires the
  A(U) capability, which serves as D of the inner adjoint.
- The rules of the table apply at count zero and on zero-width bases.
- C(U) alone permits a program to apply the constructed `controlled(U)`
  description. It does not permit the bare application `U(q)`.
- The adjoint of a controlled implementation is built from the retained exact
  circuit of that implementation, and so is a further control of it. Both
  preserve phase. A black-box assertion of channel equality supplies no such
  circuit.
- The adjoint of `controlled(U)` may use the D capability of that constructed
  description. Constructing `controlled(adjoint(U))` additionally requires the
  original D(U) capability. An outer control does not waive the construction
  premise of the bare adjoint.
- The table infers no refinement law for a composed description.

The checker rejects `bad` with `capability` on the project route and `access`
on the selected-entry route. The description `adjoint(U)` is a static actual
that `ignored` never uses. Its construction premise fails all the same,
because `bad` assumes only A(U):

```qli
unitary fn ignored[const A: Basis, const V: Op<A>](q: Q<A>) -> Q<A> { q }
unitary fn bad[const U: Op<Bit>](q: Q<Bit>) -> Q<Bit>
requires Applicable(U) { ignored[type(Bit), adjoint(U)](q) }
```

The common judgment accepts the same source when the clause reads
`requires Applicable(U), Adjointable(U)`.

### Providers

A **transparent provider** is an ordinary source function that a program
supplies as a provider. Its body is available to the checker. These rules say
which capabilities such a provider has, and how the checker finds the
provider behind a name.

Rules:

- A transparent provider must have three things: a body that is independently
  checked, a Unitary effect as its callers see it, and the required exact
  interface.
- Its Applicable capability is available after all the declared requirements
  on its actual arguments are checked.
- Its Adjointable capability additionally requires both A and D for every
  actual Op argument, including unused ones.
- Its Controllable capability requires all three capabilities for every such
  argument.
- With no Op arguments these conjunctions are empty. The checks of the body,
  the effect, the interface and materialization apply all the same.
- These derivations are conservative. They do not claim to infer everything
  that an arbitrary body would justify.
- Lookup tries lexical bindings and ordinary declarations or imports before
  primitives. When the ordinary target that it finds has the wrong category,
  is moved or is rejected, the lookup never retries a builtin.
- Closed source Meaning evidence keeps its provider, its ordered interface,
  its source dependencies and its independently checked implementation.
  Replacement evidence or stale evidence cannot stand in for that binding.
- QPE controlled powers use these same rules and the same phase-sensitive
  checking boundary.

### Primitive targets

A language primitive is not an ordinary function. These rules say where a
primitive may stand for an operation.

Rules:

- `adjoint`/`controlled` or `qif` can take a primitive directly as its target.
  That primitive must be bare `h` on `Bit`, or `global_phase_eighth` on the
  complete Basis tree of the target. Another primitive identity in that
  position is rejected (`effect`).
- For another primitive, an ordinary checked wrapper supplies a static or host
  provider.
- A language primitive itself is not a general static or host Op provider
  (`type_mismatch`; `type`).
- The ordinary gates in `std::gate`, including X, Z, T, S and identity, use
  the transparent provider rules. `id` takes explicit Basis actuals.
- A phase provider uses an ordinary wrapper with its explicit `[j,k]` actuals.
- The concrete obligations for coefficients, materialization and access
  apply. They apply to unused actuals too.

## Checked operations and finite materialization

Attaching a Meaning to an implementation does not, by itself, show that the
two agree. [Checked operations](checked-operations.md) separates two things.
The first is the obligation that the implementation equals its Meaning, which
is pending in the common judgment. The second is finite materialization.
**Finite materialization** checks a closed implementation against its exact
finite Meaning.

Rules:

- Finite materialization requires closed declarations whose effects, as
  callers see them, are Unitary. An abstract formal must not bypass this
  refusal.
- Finite materialization keeps the source dependencies, the exact basis and
  the ordered ports.
- Equal probabilities, or equality up to global phase, do not establish the
  exact equation.
- Attaching a Meaning grants no inverse access and no controlled access.
- A successful common judgment, or a pending obligation, supplies no missing
  emitter and no accepted handle.
- Static operation construction does not erase the limits of a profile.
- A direct runtime-group transform is distinct from an opaque single-owner
  `Q<A> -> Q<A>` operation. The
  [type model](type-model.md#direct-runtime-transforms-and-opaque-operations)
  gives both sets of rules, and this chapter does not merge them.

> **Implementation note.** The selected native checker checks the
> implementation against the exact finite Meaning. The bounded finite Meaning
> adapter materializes closed operation arguments through ordinary helper
> calls. An independent source replay then checks callee bindings, ordered
> actions and suspended caller owners. On the selected-entry route, the native
> checker checks every original request before a hierarchy artifact is
> emitted. Each finite endomorphic Meaning request checks the Raw artifact
> with Lean and then replays its source steps independently. For finite
> construction, the independent native gate checks the bound artifact.

## Provider selection and quantitative resource evidence

An operation has three independent contracts. Each answers a different
question. This section concerns the third. A resource bound holds for one
selected implementation, so a claim about resources depends on which provider
runs.

| Contract | Question it answers |
| --- | --- |
| Exact Meaning and interface | What action does the provider implement on the declared ordered inputs and outputs? |
| Operation capabilities | May the caller apply, invert or coherently control that action using the available implementations? |
| Resource contract | What checked finite bound holds for the selected implementation under the specified target and cost model? |

A **quantitative claim** states a checked finite bound for one selected
implementation.
[Quantitative resource claims](realization.md#quantitative-resource-claims)
gives the resource model.

Rules:

- `Applicable(U)` permits the evidenced call. A quantitative claim
  additionally requires a bound for the implementation that runs.
- A generic definition may use capability requirements and leave the
  implementation open.
- Before a concrete certificate is issued, every cost-relevant actual must be
  resolved. This covers every operation actual, however a program selects it.
- The language has no static builder that returns an operation and no trait
  that selects one. A later mechanism of either kind must resolve to one
  provider before certification.
- The [closed specialization](realization.md#closed-specialization) fixes the
  actuals and the provider dependencies before lowering and accounting.
- An ambiguous or unresolved choice makes the quantitative request fail.
- The independent check binds the provider and its retained implementation to
  the specialization, the emitted artifact, and the versioned target and cost
  model. It also binds them to the counted quantities, the input and
  scheduling premises, and the layout and workspace requirements.
- The independent check covers a finite bound and the declared composition
  premises.
- The provider that lowering and execution select must be the provider that
  the check used.
- Replacing the provider, its dependencies or the emitted implementation
  requires revalidation for the replacement subject. This holds even when the
  two providers have the same Meaning or the same name.
- A capability witness, a producer annotation or an identity hash alone
  supplies no bound.

### Bounds for composed descriptions

A composed description has a bound only when the accounting for the
composition itself is checked.

Rules:

- Composition and tensor require checked accounting for the resulting order,
  lifetimes and target schedule.
- A tensor must not assume shared scratch or parallel depth without evidence.
- Repetition requires a closed count and a checked composition rule for that
  count.
- Adjoint and control need a bound for the inverse or controlled
  implementation itself. Reusing the forward count requires a profile rule
  that applies to the emitted inverse.
- The bound of a controlled implementation includes control synthesis,
  routing and additional workspace.
- Semantic equivalence and capability derivations do not establish these
  rules.

### Foreign execution

These rules say when work outside checked source may count toward a
quantitative claim.

Rules:

- A foreign call is outside quantitative Resource Safety, unless it re-enters
  through a closed operation or provider contract. The finite implementation,
  the effects, the ordered ownership and the exact workspace obligations of
  that contract must be independently checked.
- A resource claim must include its explicit target costs. Depending on the
  model, these include hidden allocation and scratch, measurements and
  feed-forward, bounded branches or retries, and scheduling or duration.
- An opaque device instruction receives no default zero cost and no constant
  cost based on its spelling.
- An unknown or unbounded behavior makes certification fail.
- A program must not make an arbitrary runtime callback into host code. The
  source profile rejects it.
- A later callback that claims coverage must resolve to a closed, checked
  provider before certification.
- Host orchestration may invoke foreign work outside the certified region.
- A plugin or a compiler extension supplies proposals as an ordinary producer.
  Its installation and its annotations grant no authority to accept source,
  IR, implementations, resources or target mappings.
- A later FFI must declare which side of the boundary each call occupies. It
  must use the existing independent checks for anything inside.

These rules are admission requirements for future foreign execution.

## Patterns, observation and Unit

Classical pattern matching, structural ownership maps and physical observation
are three distinct mechanisms. A pattern inspects an ordinary value. A
structural map rearranges owners and observes nothing. An observation reads a
quantum owner. None substitutes for another.

### Ordinary patterns and structural maps

An ordinary tuple pattern or Unit pattern inspects the shape of an ordinary
value. The structural maps `split` and `join` take one owner of a product
apart and put two owners together.

Rules:

- A pattern over an ordinary product that contains owners moves those fields
  under the ownership rules. A wildcard must not silently drop a quantum
  field.
- Destructuring one `Q<(A,B)>` requires an explicit `split`. Constructing it
  from two owners requires an explicit `join`.
- These structural maps preserve ordered factors and reference correlations.
  They observe nothing, and they claim no separability.
- An ordinary pattern must not inspect an unmeasured quantum label.

### Coherent basis maps

A coherent basis map applies a function on basis labels to one quantum owner,
without a measurement. [Coherent basis maps](coherent-basis.md) use
`basis input as pattern { expression }`. The labels of such a map are ordinary
basis data in an isolated total computation.

Rules:

- The injective map has coefficient `+1` on each basis transition. It acts
  linearly, including on entangled inputs.
- Copying a label inside the map can create correlations. It does not copy an
  arbitrary quantum state.
- The body is one restricted basis expression. It is not an ordinary statement
  block, a closure or a measurement.
- The body must not capture an outer runtime value.
- Quantum Unit owners follow their separate explicit rules.

### Observation and classical data

Only an explicit observing operation reads a quantum owner. A classical data
form does not.

Rules:

- A program obtains physical information through an explicit observing
  operation such as `measure_z`. That operation consumes its logical owner.
- An ordinary `if` requires an ordinary `Bit` condition. A `Q<Bit>` condition
  is rejected (`type_mismatch`; `type`).
- Coherent quantum control has its own rules for owners, phase and access.
- Fieldless `enum` declarations and `struct` records declare ordinary finite
  types.
  [Parsed finite type declarations](source-text.md#parsed-finite-type-declarations)
  specifies them and ordinary `match`.
- An ordinary `match` must select on an ordinary enum value. A live `Q<T>`
  selector is rejected (`type_mismatch`; `type`).
- A variant carries no payload, and `match` has no payload pattern and no
  wildcard pattern. This chapter admits no general algebraic data type.
- A classical data type and its `match` do not implicitly establish coherent
  quantum sum semantics. Coherent selection is the separate
  [`qmatch` form](source-text.md#exact-label-coherent-selection).

### Unit

Ordinary Unit and `Q<Unit>` are different types with different rules.

Rules:

- Ordinary Unit is unrestricted singleton data.
- `Q<Unit>` is a linear owner of a one-dimensional quantum system. It can
  carry a nontrivial scalar phase although it has zero wires.
- Returning ordinary Unit, or omitting its transported result port, must not
  omit argument work or body work. It must not erase a scalar action that the
  program performed.
- Ordinary `()` is neither an implicit state preparation nor an implicit
  elimination of a quantum owner.

[Unit owners retain phase](type-model.md#unit-owners-retain-phase) specifies
explicit `unit`, `finish`, the structural maps and their profile limits.

## Scoped bodies, finite elaboration and effects

A **scoped body** is a `with_computed` body, a certified-computed body or a
static-fold body. The compiler checks it in place.

Rules:

- The binders of a scoped body create no reusable callable value.
- When the compiler checks a scoped body, it keeps the live frame of the
  caller, linear use, the inferred effects and the exact cleanup obligations
  that apply.
- The functional boundary does not prohibit scoped bodies. It does not weaken
  them into unrestricted closure capture.

### Recursion and finite elaboration

The source admits the documented runtime self-calls in which a natural
parameter decreases. These include the specified direct runtime transforms.

Rules:

- In a runtime self-call, every natural parameter must satisfy the nonincrease
  requirement. At least one must strictly decrease under the checked premises
  (`recursive_call`; `cycle`).
- A mutual dependency cycle, a recursive opaque provider and an unproved
  decrease are rejected.
- Closed specialization and supported finite folds elaborate under the work
  and storage limits of the implementation.
- Zero-count construction does not hide an invalid body or dependency.
- Accepted Core has no general runtime lazy thunk, no bottom primitive and no
  unrestricted recursive execution.
- Symbolic descriptions and shared circuit structure do not imply lazy
  physical execution.
- Exhausting a checking or elaboration budget rejects the program. The
  rejection establishes no quantitative resource guarantee. It does not show
  that the requested mathematical property is impossible.
- Success on one instance is not a proof for an entire family.

### Names without built-in semantics

Some names carry a meaning in other languages that Qleisli does not give them.

Rules:

- Names such as `Monad`, `Either`, `IO`, `bottom` and `undefined` supply no
  built-in monad, sum, host effect or partial-value semantics.
- Where the ordinary lexical and category rules permit, a program may use them
  as ordinary identifiers. An ordinary function called `undefined`, for
  example, needs a valid declaration and body. Its name grants no bottom
  semantics.

### Effects

The language has three quantum effects. They are ordered
`Unitary <= Isometry <= Observe`.

Rules:

- The effect of a function keeps the effects of its body, its callees and its
  arguments.
- An annotation must not downgrade observation, reset or discard.
- The language has no generic quantum-core Monad interface and no accepted
  `do/pure` syntax. The Kleisli origin of the project's name supplies none.
- Host filesystem, network, device orchestration and other I/O are outside
  this three-effect quantum language. Host tooling does not extend the effect
  lattice by implication.

## Boundary classification

The table classifies the fourteen concerns of the functional boundary.

| Concern | Admitted boundary |
| --- | --- |
| Functional influence | The boundary consists of explicit contracts, which are subordinate to the authority hierarchy. Rust and Haskell slogans are mnemonics. |
| Descriptions and owners | A static description contains no live Q. Each application keeps linear ownership. |
| Higher-order abstraction | The language admits static operation formals, specialization and constructors, with explicit access. General arrows keep both exact ports and their concrete profile limits. General builders are separate work. |
| Closure capture | The language has no general runtime closure or function value. Scoped bodies keep their own checks. |
| Pattern meanings | Ordinary patterns, explicit quantum structural maps and physical observation are distinct. |
| Algebraic sums | Fieldless enums with ordinary `match` are classical data, and `qmatch` is a separate coherent form. No payload-carrying ADT or general coherent sum is admitted here. A classical ADT cannot silently define a quantum sum. |
| Unit | The ordinary singleton and the zero-width quantum owner are distinct. The owner keeps its exact scalar phase. |
| Traits and laws | Capability requirements and concrete evidence are separate. The language has no general trait or class syntax. |
| Laziness, bottom and recursion | Calls are eager, Core is explicit and finite, and recursion uses the documented checked Nat decrease. No quantum work is deferred out of sight. |
| Currying and partial application | Every call has its full arity. Capturing an argument or an owner yields no reusable callable. |
| Monad and effects | The language has no general quantum Monad and no `do`. The principal Unitary, Isometry and Observe boundaries stay explicit. |
| Host I/O | Host I/O is outside the quantum effect lattice and the accepted source surface. |
| False friends | Qleisli's own diagnostics plus the explanations below. External qlippy integration is excluded. |
| Surface convenience | Finite explicit proposals, retained identity and independent checking; no fallback acceptance. |

## False friends and diagnostics

A **false friend** is a spelling that suggests a meaning from another language
and does not carry it in Qleisli. The table gives two removed spellings and
the source that a program writes in place of each.

| Removed source | Source |
| --- | --- |
| `do p <- q; pure e` | `basis q as p { e }` |
| `bind_op(implementation, Meaning)` | `checked_op(implementation, Meaning)`, with the same arguments |

Rules:

- `pure` does not prepare a state, and the basis form is not monadic bind.
- `bind_op` is not an alias. `checked_op` confers no constitutional
  certification.
- The Qleisli library and the CLI reject both removed spellings with a located
  diagnostic (`parse`), in text output and in JSON output.
- Ordinary classical matching does not measure a `Q` owner.
- A zero-width owner is not disposable ordinary Unit.
- Probability agreement does not supply exact phase equality.
- The Unitary label of an operation provides no inverse access and no
  controlled access.
- A diagnostic suggestion must not imply any of these four substitutions.

Each other refusal keeps the stage that finds it:

| Failure | Stage | Code |
| --- | --- | --- |
| A missing argument | Arity | `arity` |
| A local runtime value used as a callee or as a provider | Callable or provider category | `type_mismatch`; `type` |
| A consumed owner | Ownership | `ownership` |
| An incompatible exact type tree | Type compatibility | `type_mismatch`; `type` or `size` |
| Missing operation access | Capability checking | `capability`; `access` |
| A false effect assertion | Semantic checking | `effect` |
| An unsupported concrete form | Eligibility | `unsupported` |

Rules:

- An unsupported concrete form fails eligibility. It does not fall back to a
  weaker acceptance path.
- The parser can refuse a closure-shaped form, or an unimplemented data form
  such as a payload pattern. Such a refusal does not prove a later capture,
  match or semantic rule.
- This chapter explains the boundary. It does not promise a specialized
  diagnostic for every absent grammar form.

## Evidence identity

Evidence is bound to more than the meaning of a program. The binding includes
the retained snapshots of the source and of its dependencies, the static
bindings, the identities of the provider and of the Meaning, and the ordered
ports. A source rewrite can therefore change the identity of an artifact
while it preserves the intended exact meaning.

Rules:

- After a source rewrite, evidence must be reconstructed and independently
  checked.
- A producer must not remove source bindings or reuse stale receipts to force
  byte equality.
- Historical sources, counterexamples and real observations are unchanged.
  Explicit derivatives for the present language sit beside them.

## Status and limits

The common judgment applies the rules of this chapter on both routes. The
profiles lower part of what it accepts. Whether a program is eligible for
concrete lowering depends on the profile and on retained evidence.

Limits of the common judgment:

- A closure-shaped expression has at most 64 parameters. The 64-level limit
  on syntax nesting and the source-work budget also apply to it.
- Opaque providers and certified external providers are unsupported. A Unitary
  annotation or a Meaning alone cannot grant their capabilities.

Limits of the profiles and their components:

| Profile or component | Supported | Limits and refusals |
| --- | --- | --- |
| Bounded finite Meaning adapter | Closed operation arguments. Forward, adjoint and controlled access keep the provider definition, the exact argument tree and the original Meaning requests. Adjoint reverses the pure circuit and its exact phases. Controlled access keeps the conditional scalar phase, also for `Q<Unit>`. Structural split/join routing preserves ordered logical coordinates. Nested repetitions keep the obligations of their children at zero count. | The exact pure Raw circuit profile applies, with its bounds on work, depth, storage and wires. Phases finer than an eighth turn, other unsupported primitive forms and opaque provider assertions are explicit target refusals. |
| Finite provider materialization | Closed declarations, as [Checked operations](#checked-operations-and-finite-materialization) requires | Refuses explicit specialization through this path |
| Selected hierarchy projection and bounded pure Raw materialization | Ordered constructor trees and both exact ports. Finite endomorphic Meaning requests apply to the whole tree and to every annotated child, including children under zero repetitions. Adjoint reverses both ports. | Packed control and repetition require endomorphisms. Unsupported Raw primitives are rejected. |
| Ordinary project adapter and selected Raw adapter | Separate ports for general arrows. Rectangular Meaning equations, through fresh native `pure-leaf` checks of the original bodies and exact two-port matrices, including `V†V = I`. Ordinary `Bits<n>` values, including copyable `Bits<0>`, under the [transport rules](type-model.md#one-finite-type-universe). | The finite widths that the transport rules give |
| Selected hierarchy | The unrefined construction of the [general pure-arrow rules](type-model.md#general-pure-operation-arrows) | Its refined finite leaf is square. It has separate concrete limitations for ordinary `Bits<n>` values. |
| Finite construction | Explicit circuit and operation proposals with retained evidence | Only the supported constructions |
| Selected-source specialization | — | Its own concrete eligibility rules |
| Closed `checked_op` bindings and Meaning-refined bindings | The all-binding native gate of the [type model](type-model.md#direct-runtime-transforms-and-opaque-operations) | — |
| Coherent lifting | The maps that [Coherent basis maps](coherent-basis.md) lists for each profile | The source contract grants no unsupported emitter. |
| Bounded OpenQASM terminal report | Gate counts, derived from the decoded target word after exact checking | Rejects a realization whose scalar phase the gate vocabulary cannot represent |

The profiles keep exact Unit, Bit, Bits and product quantum interfaces. An
unsupported constructor is an explicit refusal.

Notes on the OpenQASM terminal report:

- For a composed inverse, the emitted word may be empty after phase
  cancellation.
- Under a tensor of unlike phases, the ordered physical operands distinguish
  the two implementations.
- Source checking accepts an applicable provider with an uncontrolled scalar
  phase. Terminal reporting rejects that realization when the gate vocabulary
  cannot represent the phase.

Code, tests, proof, preservation and specification review are separate:

| Aspect | Status |
| --- | --- |
| Code | The common checker implements the call, closure, construction and capability rules of this chapter. The profiles above implement lowering within their limits. The foreign-execution rules are admission requirements for future foreign execution. |
| Tests | `tests/functional_boundary.rs`, `tests/rust_boundary_diagnostics.rs` and `tests/checked_operations.rs` check small instances of the call, closure and capability rules. They are conformance checks, not source-preservation proofs. |
| Proof | This chapter discharges no proof obligation. The broader QS, PR, quantitative RS and EXACT duties are pending, and the profile checks are not a full discharge of them. |
| Scoped guarantees | `QS-QLV1-OWNERSHIP-2026-01` and `QS-QLV1-SCOPE-2026-01` cover ownership and classical scope for the ordinary QLV1 decoded root. They keep their recorded scopes, premises and evidence obligations unchanged. They are not enlarged into a guarantee of functional source abstraction. |
| Preservation | The profile checks keep phase and ordered ports. They are not a general source-preservation theorem. Valid proposed IR alone is not a general proof of source preservation. |
| Specification review | The boundary classification states language contracts and implementation limits. It does not declare that the acceptance checks of the decision, or the broader feature Issues, are finished. The decision changes neither these statuses nor edition 2026. It creates no release approval and no proof discharge. |

The [production boundary](production-boundary.md) distinguishes source
judgment, concrete lowering, native acceptance and runtime or emitted-artifact
correspondence.

Separate work:

- General builders, further capability extensions and linear closures are under
  separate decisions and implementation work. The retired
  [operations design packet](../design/operations.md) records the proposals
  that no decision adopted.
- Algebraic data types beyond fieldless enums and records, including
  payload-carrying variants, are under the same separate work.
- The general-arrow rules adopt none of these proposed extensions.

Tooling:

- The public Qleisli library and the CLI produce the diagnostics of this
  chapter.
- External qlippy implementation, compatibility and diagnostics are excluded.
  The exclusion waives neither the Qleisli compiler diagnostics nor the Rust
  Cargo Clippy checks. It establishes no qargo support and no other consumer
  support.

## History

- This chapter follows the
  [ordinary decision in #80](https://github.com/MGYamada/Qleisli/issues/80#issuecomment-6009479668).
  The boundary classification covers the fourteen boundary concerns of that
  Issue. The chapter stated the boundary for the `0.3.0-beta` release.
- The chapter was later aligned, under the same Issue, with the implemented
  general arrows `Op<A -> B>`, the rectangular Raw Meaning checks and the
  transport of ordinary `Bits<n>` values.
- Qleisli 0.3.0 removed the `do ... pure ...` form and renamed `bind_op` to
  `checked_op`.
- The provider resource contract follows
  [#161](https://github.com/MGYamada/Qleisli/issues/161) and
  [#162](https://github.com/MGYamada/Qleisli/issues/162).
- The admission requirements for foreign execution follow
  [#164](https://github.com/MGYamada/Qleisli/issues/164).
- The maintainer explicitly authorized the exclusion of external qlippy
  implementation, compatibility and diagnostics from the beta release.

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
