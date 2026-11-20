# Ordinary types, quantum owners and equality

An **ordinary finite type** is a type of finite classical values: `Unit`,
`Bit`, `Bits<n>`, an ordered tuple, a fieldless enum or a record. A **quantum
owner** is a value of type `Q<A>`. It is the linear ownership of one quantum
system whose basis is the ordinary finite type `A`. **Type equality** is
definitional: two types are equal only when their complete trees agree.

This chapter specifies these types for edition 2026. It covers their values,
the linear rules of owners, type equality, patterns, static parameters,
operation types, the transforms of operations, nominal types and the
selected-entry commands. It is subordinate to the
[authority hierarchy](authority.md). The frontend uses the canonical ordinary
spellings `Unit`, `Bit`, `Bits<n>`, `0` and `1`.

To see the linear rule in a running program, [follow a quantum owner
through measurement](../learn/ownership.md) and try using its ordinary result twice.

## Routes, profiles and checks

The CLI checks source through two [routes](diagnostics.md#routes): the
**project route**, on a source root, and the **selected-entry route**, with
`--entry` and `--module` bindings. The chapter uses these terms:

| Term | Definition |
| --- | --- |
| **Common judgment** | The one source check that both routes apply to every complete original declaration and body. The common frontend is the only source grammar and the only source judgment. |
| **Native checker** | The checker executable that `lean-kernel/` builds. It decides the acceptance of a proposal independently of the component that produced it. |
| **Finite project** | The lowering profile of the project route. It lowers the closed instances of a project to finite Raw and QIRF proposals. |
| **Selected projection** | The body projection that `Instantiation::elaborate` performs on the selected-entry route. |
| **Selected Raw** | The lowering profile that lowers the selected projection to a Raw proposal. |
| **Selected hierarchy** | The lowering profile that lowers the selected projection to hierarchy and finite-leaf proposals. |
| **Typed route** | The path that lowers the original source through the common emitter and submits a typed root request to the native checker: `finite-ordinary-root-v2` or `finite-runtime-root-v2`. Both CLI routes use it. [Typed routes](#typed-routes) gives the use of each request. |
| **v5 source check** | The native check of a version-5 original-source request. Its report names the profile `finite-source-basis-context-v5`, `finite-source-qmatch-context-v5`, `finite-source-meaning-context-v5` or `finite-source-access-context-v5`. |

Rules:

- The common judgment runs before every check of concrete eligibility. It
  retains exact type trees, owners, static premises, access and principal
  effects.
- The common judgment covers every original declaration, owner rule, effect
  rule, capability, dependency and static branch. This includes private and
  unused declarations, both arms of a branch, the body of a loop with zero
  iterations and all eight ordinary bundled modules.
- The checker reports a source-semantic error before it decides whether the
  program is eligible for a concrete profile.
- An input that is a directory or a qrate and an input of explicit modules
  differ in three ways: the loader, the provenance and the concrete consumer.
  After the common judgment, the project route requires its concrete
  declarations to fit the Finite project profile. The selected-entry route
  seeks native acceptance only for the requested concrete specialization.
- Native results distinguish those scopes. They do not certify every possible
  specialization, and they do not establish general source preservation.
- Four things have their own checks after the common judgment: closed host
  bindings, concrete capacity, emitted evidence and native acceptance.
- A generic check that succeeds does not imply that concrete lowering
  succeeds.
- All frontend output is an untrusted proposal. The native gates are
  mandatory: the root, request, contract, hierarchy and finite-leaf gates.

After a rule, the chapter names in parentheses the common checker class of a
program that breaks the rule, as in (`ownership`). The code `parse` marks a
syntax error. [Codes](diagnostics.md#codes) maps each class to the `code`
that a route reports.

> **Implementation note.** The selected projection consumes the original
> resolved identities of the common judgment, with its completed lexical
> facts and effect facts. It records a projection restriction per
> declaration. A restriction excuses no check: the checker checks an unused
> definition, both branches and an empty loop all the same.

<a id="one-finite-type-universe"></a>

## Ordinary finite types

An ordinary finite type describes classical data. The same type also serves
as the basis of a quantum owner `Q<A>`.

The ordinary finite types are `Unit`, `Bit`, `Bits<n>` and ordered tuples of
finite types. Nonempty fieldless enums and records with finite ordinary
fields are ordinary finite types too. `n` is a checked static natural.
**`Basis`** is the static kind of these finite type trees.

| Type | Value and ownership |
| --- | --- |
| `Unit` | Ordinary singleton, with value `()` |
| `Bit` | Ordinary finite bit, with values `0` and `1` |
| `Bits<n>` | Ordinary sequence of exactly `n` bits, retaining ordered positions |
| `(A,B)` | One ordered product value, retaining its immediate arity and nesting |
| `Q<A>` | One linear quantum owner with basis `A` |
| `(Q<A>,Q<B>)` | Two linear owners, without any assumption of state separability |

Rules:

- An ordinary value may be copied or dropped.
- A basis argument of `Q` must not contain a quantum owner.
- An ordinary tuple may mix ordinary fields and quantum owners. Each field
  that contains a quantum owner retains its linear obligations.
- No `C<A>` constructor exists.

### Bit literals

A program writes a Bit literal as `0` / `1`. The spelling is the same in
ordinary computations and in basis computations.

Rules:

- `false` / `true` migrate explicitly to `0` / `1` (`parse`). Every other Bit
  numeral is rejected (`parse`).
- A numeral in a position that takes a static Nat denotes a natural. The
  distinction is one of stage and category, and it does not inspect quantum
  data.
- No literal creates a quantum owner. Typing an expression against an
  expected type must not implicitly prepare or measure data.
- Both routes type `0`, `1`, `not`, `and` and `xor` by one exact Bit
  judgment. Both routes evaluate the operands eagerly, from left to right.
  Both operands of `and` evaluate even when the left value is zero.
- The checker does not coerce a quantum operand, a `Bits<1>` value, a static
  natural or a product to `Bit`.

### `Bits<n>` registers

A `Bits<n>` register holds `n` bits in a fixed order. An ordinary `Bits<n>`
value is one typed value with ordered classical elements. `Bits<0>` has one
empty value. It is a copyable singleton basis distinct from `Unit`.

Rules:

- `empty_bits()` constructs `Bits<0>`.
- `prepend_bit` with static argument `n` takes `Bit` and `Bits<n>` and returns
  `Bits<n+1>`. The head comes before the tail.
- A program may copy or ignore an ordinary register. A quantum owner
  `Q<Bits<n>>` retains the linear rules.
- No profile treats two types of equal width as one type. No profile infers a
  missing static argument.
- The retained source graph retains the exact `Unit`, `Bit` and `Bits` tags and
  the tuple trees. Flattening the classical transport ports creates no type
  coercion.
- A closed size of zero retains the `Bits` tag. The ordinary empty value is
  copyable and emits no classical identity. `Q<Bits<0>>` retains a distinct
  linear owner and branch phi even with no wires.

> **Implementation note.** Selected Raw retains an ordinary `Bits<n>` value as
> one typed source value with ordered classical elements. Source-step replay
> checks the ordered elements against the artifact that the native checker
> accepted. This bounded check is not an AST preservation theorem. Finite
> project also retains ordered classical elements and exact quantum register
> owners. [Capacities](#capacities) gives the width limit of each profile.

## Quantum owners

A program holds a quantum system through an owner. `Q<A>` is linear quantum
ownership over the finite value space `A`. Typing keeps four things distinct:
ordinary bindings, static bindings, linear owners and semantic effects.

Rules:

- A program must move, return or explicitly consume every quantum owner
  according to an admitted rule (`ownership`).
- An ordinary binding of a `Q<A>` value does not require a `qlet` spelling.
- A move takes the linear ownership of a value away from every later use.
  Copying an ordinary value neither creates nor consumes a quantum owner.
- A static binding must not be used as a runtime value.
- The checker does not infer effects from ownership alone. An annotation
  must not downgrade the effect of its body.
- Measurement explicitly consumes a supported `Q<A>` and produces ordinary
  data with Observe semantics.
- An ordinary `if` consumes an ordinary `Bit` condition. It cannot read a
  `Q<Bit>`. Coherent control has its separate rule.
- Physical state spans pending arguments and suspended callers. Separate
  ownership never implies that those subsystems are separable.

The [ownership diagnostics](rust-boundary.md#conditional-teaching-diagnostics)
explain the linear obligation at the rejected source location.

### The typing judgment

The conceptual typing judgment is `Γ ; Δ ⊢ e : T ! ε`. It says that the
expression `e` has the type `T` and the effect `ε` under the environments `Γ`
and `Δ`.

| Part | Content |
| --- | --- |
| `Γ` | Ordinary values and the separately classified static environment |
| `Δ` | Live linear quantum ownership, including quantum fields of ordinary products |
| `ε` | The semantic effect computed from the complete body and its callees |

The judgment describes the source contract. It does not claim that a general
source-soundness theorem has been discharged. The normative
[Observe instrument judgment](source-text.md#instruments-and-ordinary-feed-forward)
relates this effect to complete outcome maps and quantum-owner interfaces.

> **Implementation note.** The checker may store ordinary and linear bindings
> in one table. It checks their different reuse rules from the exact type, and
> it tracks moves by binding identity.

### Surface roles

Four rules determine how a program expresses quantum and ordinary operations.
A single expression may use more than one rule.

| What the program does | Surface form | Meaning |
| --- | --- | --- |
| Select an operation coherently or iterate with a quantum owner | `qif`, `qmatch`, `qfor static` | The first two preserve coherence across selector sectors. A static quantum fold moves its complete carry once per iteration. Its index and bounds are ordinary compile-time values. |
| Give a call temporary access to an existing owner | `excl q`, `ctrl q` | Exclusive access permits a checked action on the selected place. Coherent control must preserve its computational-basis sectors and may accumulate phase or entanglement. The caller retains the owner after the call. |
| Move a live value of type `Q<A>` | Ordinary `let`, tuple construction, function application and tail expressions | The type makes each owner linear. A binding transfers the owner, and an owned call consumes its argument. |
| Compute with ordinary data or specialize a program | Ordinary `if`, `match`, `const` arguments and `for static` with an ordinary carry | A runtime condition reads an ordinary bit or discriminant. Compile-time arguments and loop bounds are fixed during specialization. |

For example, `let r = h(q);` moves the result into `r`. The call
`h(excl q);` instead leaves the updated owner bound to `q`. Access markers
must appear on the argument that requests temporary access. The language
has no implicit receiver adjustment that inserts one.

An ordinary `if` requires `Bit`. To branch on a measured value, the program
must explicitly measure its owner. A `qif` carries its selector through the
operation. A `q` prefix grants no operation capability or effect. Each form
also follows the type, ownership and effect rules of its arguments.

See [coherent selection](source-text.md#exact-label-coherent-selection),
[static folds](static-language.md#static-folds) and
[exclusive and coherent-control access](rust-boundary.md#whole-owner-exclusive-calls).
The [control diagnostics](source-text.md#diagnostics-at-control-boundaries)
identify the failed selector or carry rule.

## Structural equality, coherence and physical maps

Two types are equal only when they are the same tree. Definitional type
equality compares constructor tags, evaluated static sizes, immediate tuple
arity, nesting and ordered leaves:

- `Bit` and `Bits<1>` are distinct.
- `Unit` and `Bits<0>` are distinct.
- `((A,B),C)`, `(A,(B,C))` and `(A,B,C)` are distinct.
- `Q<(A,B)>` and `(Q<A>,Q<B>)` are distinct ownership interfaces.

**Canonical coherence** is a structural map with its own separate
justification. It is not definitional equality. A **physical map** is SWAP,
preparation, observation, reset, discard or a nontrivial phase.

Rules:

- Equal width, cardinality or Hilbert-space dimension does not make two types
  equal (`type`).
- For symbolic sizes, the bounded static solver must establish equality under
  the same explicit premises. A search that finds no counterexample does not
  establish equality.
- An admitted coherence must preserve ownership and ordered axes with exact
  phase `+1`. This includes extension by an arbitrary reference system.
- The checker introduces no implicit coherence. `split`, `join` and any
  subsequent reassociation or unit map are explicit and independently checked.
- The checker never inserts a physical map as an ordinary type coercion.
- A program that rearranges bindings gains no permission to rearrange axes.
- Destructuring a tuple with a pattern does not implicitly split a quantum
  owner whose basis is a tuple.
- A value of the same width and a different tree needs an explicit specified
  conversion. Without one it is rejected. No implicit cast exists.
- The common frontend must retain the full source tree. It must use an
  explicit representation mapping or reject an unsupported lowering profile.
  It must not silently map `Bits<1>` to `Bit` or `Bits<0>` to `Unit` to obtain
  evidence.

> **Implementation note.** The finite QIRF basis representation has Unit, Bit,
> Pair and Tuple and an explicit Bits atom. The hierarchy also distinguishes
> Unit, Bit, Bits and tuple.

## Predicate domains and argument lists

This section fixes the parameter list of a predicate that a program passes
to `with_computed`. A predicate used by either form of `with_computed` takes
**one** ordinary basis parameter. The parameter has the exact basis type of
the source register, and the predicate returns `Bit`. A `Meaning` function
follows the same exact single-domain convention.

Rules:

- The checker does not implicitly fold an argument list into a tuple.
- A predicate on `Q<Unit>` takes `u: Unit` or `_: Unit`. A nullary function is
  not an implicit predicate on the Unit domain.
- A call of a classical function uses the arity of the declared argument
  list. `f(a,b)` and `f((a,b))` are distinct, and an ordinary nullary call is
  nullary.
- For a predicate used in both roles, update its ordinary callers or write a
  separate unary wrapper with an explicit product pattern. No implicit
  packing, reassociation or physical conversion repairs a mismatch.
- A predicate must be total. It need not be injective. Constant and AND
  predicates are valid, and their computed auxiliary must satisfy the
  applicable exact cleanup rule.
- Coherent basis lifting retains its separate injectivity check.
- Four things are unchanged: the leaf order of the truth table, the retained
  phase, the correlations with an external reference and the exact type of
  the original owner.

The checker accepts this predicate for a register of basis
`((Bit,Bit),Bit)`:

```qli
classical fn p(((a,b),c): ((Bit,Bit),Bit)) -> Bit { a and c }
```

A flat `(Bit,Bit,Bit)` register or a right-nested `(Bit,(Bit,Bit))` register
requires a parameter with that precise tree.

## Unit owners retain phase

An owner without wires is an owner all the same. `H(Unit)` is
one-dimensional, not zero-dimensional. `Q<Unit>` is a linear owner although
it has zero physical wires. So is `Q<Bits<0>>`.

Rules:

- A program that copies, silently drops or revives either owner is rejected
  (`ownership`).
- The scalar operator `[-1]` cannot be erased. Under coherent control it
  becomes the nontrivial relative phase `diag(1,-1)`. Structural
  simplification must retain that action and the owner and evidence interface.
- A pure map that introduces or eliminates a Unit owner needs its own
  explicit checked rule. Ordinary `()` supplies neither such a map nor an
  implicit `Q<A> -> A` conversion.
- The common judgment retains `Q<Unit>` and `Op<Unit>` alongside `Q<Bit>`,
  `Q<Bits<n>>` and complete packaged Basis trees. Helpers and operation
  providers retain the exact basis and the linear owner even when the list of
  physical axes is empty.
- An input or a return of type `Q<Unit>` retains a distinct linear owner, with
  an empty wire list, through ordinary calls and exact products. Ordinary
  `Unit` supplies no owner.

The [primitive boundary](primitive-boundary.md) lists the primitives of this
section.

### `global_phase_eighth`

`global_phase_eighth(q)` applies a scalar phase to a complete owner. It
consumes one `Q<A>` owner for any Basis tree `A`. It returns an owner of the
same exact type, with the scalar action `exp(i*pi/4) I`.

Rules:

- The sole argument evaluates once. The primitive takes no static arguments
  and has the Unitary effect.
- An ordinary value or a tuple of separate owners is not a valid argument.
- The coefficient is exactly `exp(i*pi/4)` times the identity on the complete
  ordered basis and on any retained reference. This holds for packaged tuples
  with Unit and Bits factors.
- The scalar is distinct from `phase[1,3]`, whose Bit action is
  `diag(1, exp(i*pi/4))`. On `Bit` it is a scalar times the identity on both
  basis labels, not T on one axis.
- The adjoint conjugates the scalar. Eight repetitions give the identity.
  Coherent control of four repetitions gives Z on the control.
- Removing a Unit factor cannot remove the scalar.
- Concrete preparation preserves the original tree and axes. It neither
  splits the owner nor erases a zero-width factor.
- The work of the argument, which comes before, and an observation that
  follows stay in source order.
- The type, width, work and backend limits of the requested profile apply.

> **Implementation note.** Hierarchy lowering retains the scalar through
> explicit checked Unit structure and a finite scalar leaf, tensored with the
> identity of the original owner. The internal Unit owner adds no physical
> wire and does not change the source basis. Raw lowering multiplies the
> complete `Q<A>` owner by exactly `exp(i*pi/4)` with the zero-axis monomial.
> It consumes the original token and returns a fresh token with the same shape
> and wires. Raw source-step comparison independently checks the scalar
> opcode, the exact phase, the empty controls and axes, and the intended
> owner. Fresh native validity is mandatory.

### `unit` and `finish`

A program creates a `Q<Unit>` owner with `unit` and gives one up with
`finish`. The common source catalog exposes these two explicit structural
maps:

- `unit(u)` takes exactly one ordinary `Unit` argument and returns one fresh
  `Q<Unit>` owner.
- `finish(q)` consumes exactly one `Q<Unit>` owner and returns ordinary
  `Unit`.

Rules:

- Both maps take no static arguments. Both have Unitary quantum action with
  the exact coefficient `+1`.
- Neither map allocates a physical wire, measures, discards or converts
  another basis implicitly.
- `unit()` is an arity error (`arity`). Write `unit(())`.
- `Bit`, `Bits<0>` and their quantum owners are not substitutes for the
  specified argument types.
- Each argument evaluates completely, once, before its map. An observing
  argument makes its caller observing.
- `finish(global_phase_eighth(unit(())))` has the scalar coefficient
  `exp(i*pi/4)`. Its ordinary `Unit` result does not erase that computation.
- Reintroducing a Unit owner after `finish` gives a fresh owner. It never
  revives the consumed binding, and it preserves the phase and any retained
  reference.
- The maps can form explicit left and right maps on separate-owner products,
  such as `(Q<Unit>, Q<Bit>)` to `Q<Bit>`.
- An observing discard is no substitute for either map. A retry after a
  native failure is no substitute either.

> **Implementation note.** The maps lower to the checked `pack_unit` and
> `unpack_unit` constructors, `RawOp::PackUnit` and `RawOp::UnpackUnit` in
> Raw. Hierarchy, Finite project and shared Raw lowering retain the explicit
> maps. Raw `pack_unit` creates a fresh zero-axis owner, and `unpack_unit`
> consumes an existing one. Each transition of a zero-axis owner retains the
> complete live caller frame and the scalar phase. The native checker retains
> issued identities after consumption and rejects their reuse.

### `split` and `join`

`Q<(A,B)>` is one owner, and `(Q<A>,Q<B>)` is two. A program converts
between the two types with two explicit maps:

- `split(q): Q<(A,B)> -> (Q<A>,Q<B>)` consumes one owner and returns two fresh
  owners in left/right order.
- `join(a,b): (Q<A>,Q<B>) -> Q<(A,B)>` consumes two distinct owners and
  returns one fresh owner with the complete ordered basis tree.

Rules:

- Both names are bare language primitives. They take no static arguments and
  have Unitary action with the coefficient `+1`.
- `split` has one argument and requires an immediate binary basis tuple.
  `join` has two arguments, not one ordinary tuple argument.
- The arguments evaluate completely, once, from left to right.
- Both maps preserve nested trees, zero-axis factors, correlations with
  retained owners and the physical axis order.
- Neither map asserts separability, flattens a tuple, changes a basis tag,
  measures or silently discards an owner.
- An ordinary tuple pattern cannot unpack a `Q<(A,B)>` owner.

> **Implementation note.** The maps use the native `split_tuple` and
> `join_tuple` rules. Native support for other arities does not widen the
> source signature. Selected hierarchy admits packaged quantum bases built
> recursively from `Unit`, `Bit`, `Bits<n>` and ordered tuples. It also admits
> `Op<A>` for those bases.

> **Implementation note.** The source Raw leaf adapter supports the two maps
> for packaged bases built from exact Unit/Bit product trees. Each logical
> owner retains its complete ordered wire vector, which is an empty vector for
> a zero-width factor. The independent ordered replay checks fresh owner
> identities, exact source field trees, split partitions and join operand
> order. Raw transport widths do not replace source types. The unary native
> finite request also retains the complete original Basis signature and the
> returned wire order. This finite representation mapping retains atomic Bits
> tags. It does not expand them into Unit/Bit products or identify them by
> width alone.

### Unitors

A unitor removes a Unit factor from a packaged owner, and its inverse adds
one. An explicit left unitor on `Q<(Unit,A)>` is `split` followed by `finish`
on its Unit owner. Its inverse is `join(unit(()), a)`. The right unitor uses
the other factor.

Rules:

- The coefficient is exactly `+1` on every basis value and retained reference.
- Scalar work already performed on an eliminated Unit factor stays in the
  composition.
- Implicit coercion never inserts a unitor.

## Tuples and patterns

A pattern takes a value apart by its shape. One rule for the shape of a
pattern applies in four places: ordinary function parameters, `let`
bindings, classical function parameters and coherent basis maps. Ordinary
`Unit` has no quantum owner identity.

Rules:

- An ordinary `Unit` value may be copied, dropped or matched by the empty
  pattern `()`. This holds inside an ordinary tuple too.
- The pattern `()` matches only ordinary `Unit`. It does not match an empty
  tuple, `Bits<0>`, `Q<Unit>` or `Q<Bits<0>>`.
- A nonempty tuple pattern preserves the immediate arity and recursively
  matches the exact shape of each child.
- A typed parameter is one argument. Matching an argument does not flatten the
  calling convention.
- Parameter names must be unique across the complete parameter list and
  distinct from static parameters.
- An ordinary wildcard may ignore unrestricted data. It cannot discard a
  quantum owner. This holds for an owner nested inside an ordinary product
  and for an owner of zero width.
- Empty parentheses are value and pattern syntax, and an empty argument list
  is nullary. In a type position, write `Unit`.

The checker accepts this declaration. The function takes two arguments:

```qli
unitary fn f((a, b): (Bit, Bit), (): Unit) -> Bit { a xor b }
```

The pattern in `basis q as () { () }` describes the ordinary Unit basis of its
quantum input. The [coherent basis map](coherent-basis.md) consumes and
returns a `Q<Unit>` owner with the coefficient `+1`, and it retains any scalar
already present on its input. It is not runtime `let () = q` or an implicit
owner elimination.

A computation that returns `Unit` can consume owners or perform observable
work. Omitting its result port does not omit its body.

> **Implementation note.** Selected Raw implements the Unit basis map through
> the `LiftBasis` proposal and a separate source-step comparison. Selected
> hierarchy admits the singleton table `[0]` with the coefficient `+1` under
> the narrow
> [zero-basis conversion and preparation profile](coherent-basis.md#concrete-profiles-and-proof-boundary).
> Other tables and table-dependent static transforms are unsupported there,
> and its quantum Unit, depth and work limitations apply. Lowering of the
> selected projection omits ordinary `Unit` value ports. It retains the exact
> source interface and all executed operations.

### Rest patterns

A rest pattern such as `..` would stand for components that a pattern leaves
out. Rest patterns are not part of the source grammar. Qleisli diverges here
from the ergonomics of ordinary Rust patterns on purpose.

Rules for a future pattern form that elides components:

- Every omitted component must be proven unrestricted or already explicitly
  consumed under a separate language rule.
- Rest syntax never implies discard, reset, release or measurement.
- When the checker rejects an elided live quantum component, the rejection
  must identify that field or component. This includes nested and zero-width
  owners.

These rules do not admit rest syntax, and they promise none of these
diagnostics before the syntax is implemented.

## Callable values and scoped bodies

A function cannot hide a live quantum owner inside a callable value. At the
live-owner boundary, ordinary quantum functions are first-order. Arguments
and results explicitly expose their quantum owners.
[Closure-shaped expressions](functional-boundary.md#closure-shaped-expressions)
gives the surrounding boundary.

Rules:

- A declaration name is not a runtime callable value that can be copied,
  stored or returned with hidden quantum state.
- A static `Op<A>` description contains programs and their provider
  identities. It contains no captured live `Q<A>` owner. The
  [static language](static-language.md#capability-derivation-for-enabled-descriptions)
  specifies the bounded composition and capability rules.
- Unrestricted capture of a live quantum owner by a closure is forbidden.
  This includes nested and zero-width owners.
- A future linear or one-shot quantum callable requires a separately specified
  type, usage, effect and access contract.
- Ordinary closure values are unsupported. The parser retains three bounded
  forms solely to report their rejection: `||expr`, `|pattern, ...|expr` and
  the form with a block body. The forms include an optional contextual
  `move`, parameter annotations and block return annotations. None can be
  lowered or executed.
- An annotation supplies no type or ownership evidence for this rejected
  syntax.
- A closure body that refers to an outer live quantum owner is rejected
  (`ownership`). The checker reports the rejection at the original resolved
  use, with the checked type of the outer binding.
- An ordinary classical value named `q` is not a quantum capture.
- Closure parameters and body-local bindings retain separate lexical
  identities, so shadowing does not capture the outer binding.
- An outer binding that is already consumed retains its consumption error.
- Every other closure value is refused (`unsupported`). Parsing the diagnostic
  syntax does not admit callable values.

### The body of `with_computed`

The `|...|` body of `with_computed` is a scoped construction. It is not a
closure value.

Rules:

- The body cannot escape or be stored for later invocation.
- The two-argument form permits ordinary classical outer values and hides
  outer live quantum owners.
- The three-argument certified form hides all outer runtime values and exposes
  the explicit data and auxiliary binders.
- The checker reports a forbidden outer use at the use of that resolved
  binding.
- A body-local binding with the same name has its own identity and is not an
  outer capture. An already consumed binding retains its consumption
  diagnostic.
- These checks do not replace two separate evidence obligations: the exact
  compute/use/uncompute obligation and the logical-operation obligation. See
  the
  [workspace boundary](rust-boundary.md#checked-cleanup-is-a-separate-contract).

## Inference and generic responsibilities

The [static language](static-language.md) specifies natural expressions,
guarded arithmetic, termination and the specialization capacities. This
section gives the responsibilities of inference, of static bindings and of
operation parameters.

### Inference

These rules limit what the checker infers.

Rules:

- The checker infers only uniquely determined static structure under
  specified rules. It rejects ambiguous type substitutions, callable
  categories and provider choices.
- No search may manufacture meaning, an inverse, coherent control or semantic
  evidence. This holds for a search for a convenient implementation, for a
  numerical coincidence or for a matching name.
- For a fixed source, dependency set and selected toolchain, preparation is
  deterministic. It terminates under its published static limits on work,
  storage and depth.
- An unresolved constraint is rejected. A check that exhausts its budget is
  neither a successful inference nor a proof of impossibility.
- Trait or capability resolution must not use cyclic guessing or the absence
  of a contradiction as evidence.
- Callable resolution must establish a unique declared category before
  ordinary checking.
- An effect annotation cannot downgrade the meaning of the body.

### Explicit static bindings

The conservative profile requires Nat and Op bindings that are complete,
explicit and closed. Even an unused static parameter must be bound.

Rules:

- The report of a binding mismatch names the selected entry, the binding
  category, and the missing and unexpected names in lexical order.
- When a provider lacks a Nat binding, the report also identifies the
  affected Op binding and the resolved provider.
- An arity error at a source call identifies the resolved declaration, the
  names and categories of its static parameters in order, and the supplied
  count.
- These diagnostics choose no missing value and no provider.
- The checker reports an error in a natural binding before an error in an
  operation binding. When the declaration introduces Basis parameters, it
  reports an error in a Basis binding before an error in a natural binding. A
  declaration with only Nat and Op parameters keeps the first priority.

### Closed instances and the specialization cache

Specialization substitutes closed values for the static parameters of a
declaration. After the common judgment, it checks closed substitutions, exact
type trees, provider identity, premises and aggregate work.

Rules:

- Numeric and operation obligations share the
  [ordered `requires` mechanism](static-language.md#unified-requires-obligations).
  The closed check consumes its normalized facts. It does not reclassify the
  source definition.
- The success of an instance is not a proof about every member of a generic
  family.
- The specialization cache belongs to one immutable checked program and its
  resolved dependency universe. The owning checked program supplies the source
  and dependency identity. The key is not a process-wide name or width cache.
- A cache key retains the resolved declaration, exact Basis trees, closed Nat
  values and the recursive operation identity. That identity includes provider
  specializations, constructor arguments and retained Meaning identities.
- Relevant premises and capabilities come from that declaration and its
  checked substitutions. Equal width, matching display names or a cache entry
  from a different source cannot replace them.
- Each specialization keeps exact constructor tags, tuple order and nesting,
  the selected type, Nat and provider bindings, the original source and
  dependencies, and local identities. Width alone never selects a cache entry
  or a conversion.
- Reusing a cache entry retains the aggregate call accounting. It supplies no
  native acceptance and no source-preservation proof.
- A concrete instance lowers to the native representation and receives a
  fresh decision of the native checker. Specialization introduces no native
  primitive and no accepted-handle constructor.

[Specialization identity and reuse](static-language.md#specialization-identity-and-reuse)
gives the identity of an operation description.

### Capability requirements of operation parameters

A capability requirement is an entry of a `requires` clause that names a
capability of an operation parameter. It states one kind of access that the
body has to that parameter. An endomorphic `Op<A>` formal starts with no
executable access.

Rules:

- Each `requires Applicable(U)`, `Adjointable(U)` or `Controllable(U)` grants
  only that named generic assumption. It must refer to an operation parameter
  of the same declaration.
- Repeating a capability requirement is rejected (`access`). One capability
  does not grant the other two.
- The body and every forwarded call must satisfy their own capability
  requirements (`access`). This holds even when they are unused or inside a
  fold with zero iterations.
- A mathematical Meaning refinement or a Unitary effect is not a capability.
- A concrete provider requires its checked implementation paths. A generic
  assumption is not evidence for an arbitrary external provider.

<a id="opaque-basis-specialization-in-the-selected-profile"></a>

## Opaque Basis parameters and nominal types

A declaration can take a basis as a static parameter, and a program can
declare finite types of its own. The common grammar admits `const A: Basis`,
`Q<A>` and `Op<A>`. A **nominal type** is a declared fieldless enum or
record.
[Parsed finite type declarations](source-text.md#parsed-finite-type-declarations)
gives the declaration forms. [Typed routes](#typed-routes) gives the routes
that execute nominal source.

### Opaque `Basis` parameters

A generic body cannot look inside a Basis parameter. An abstract `A : Basis`
is opaque. The identity of `A` is the binder of its resolved declaration, not
its spelling or an inferred width.

Rules:

- An ordinary value of the abstract type `A` may be copied.
- A body may move and return a `Q<A>` owner. It may pass the owner to an
  operation that an explicit capability requirement justifies.
- A body must not inspect `A` as a tuple, assume a width or prepare a state
  merely because `A` is finite. Abstract decomposition, reflection and quantum
  preparation are unavailable.
- A favorable instance does not rescue an invalid generic body.
- Static parameters are explicit and ordered. The kind of a parameter may
  refer only to earlier parameters.
- A runtime value never determines a static size or a provider.
- The common judgment checks all supplied declarations, all branches and the
  bodies of folds with zero iterations. It does so before it considers any
  selected type binding or provider binding.

### Static arguments and `type(T)`

A call supplies a Basis argument in one of two forms. A source call forwards
a resolved opaque parameter by name. An explicit concrete static argument is
`type(T)`. The common judgment accepts both forms. The first call forwards
the parameters `A` and `U`, and the second supplies the concrete tree `Bit`:

```qli
inner[A,U](q)
inner[type(Bit),identity_bit](q)
```

Rules:

- `type(T)` creates no runtime type value and no quantum owner.
- A runtime function named `type` is an ordinary function. Contextual static
  Nat names such as `Bit` retain their category.
- The checker infers no argument from an expected width, a type or an
  available provider.
- `type(T)` also retains an original resolved finite enum or record. This
  includes aliases and field sizes that closed Nat helpers give. Field sizes
  stay rooted in the type declaration. They are not invented Nat occurrences
  in the calling function.
- An ordinary Basis/Nat dependency may forward the same nominal trees. This
  includes concrete `type(T)` arguments and nested tuples. The original
  binders of the caller and of the callee, the numeric premises and the
  module-public effects stay distinct.
- The checker checks a closed argument even when it is unused. Ordinary
  forwarding grants no operation capability, and this preparation grants no
  execution, inverse or control capability.

> **Implementation note.** The common static plan binds the original type
> occurrence of `type(T)` to its canonical declaration in the same checked
> collection. The selected projection keeps the complete nominal source tree.

### Host bindings

A host binds the static parameters of the selected entry through the CLI or
the Rust API.

| Binding | CLI form | Rust API |
| --- | --- | --- |
| A Basis parameter of the entry | `--type=A=Bit`, or an exact closed ordinary product | `BasisBinding::parse`, `ParsedProgram::basis_binding`, `instantiate_with_types` |
| A Basis parameter of a provider | `--operation-type=U.B=Bit` | `OperationBinding::with_types` |

Rules:

- A provider binds the types of its own declaration separately. It does not
  inherit the parameters of the caller by name.
- A binding that is missing, extra or of the wrong category is rejected.
- `--basis=N` has a distinct role: it is the runtime input of a hierarchy
  execution.
- A closed description uses the same type grammar and requires EOF. It rejects
  unavailable names, quantum owners, unresolved sizes and invalid bounded
  arithmetic.
- `BasisBinding::parse` works without a source context, and its contract
  covers built-in types only. A portable built-in description needs no source
  context.
- `basis_binding` also resolves fully qualified public finite type names and
  public reexports, for example `program.basis_binding("labels::Tri")`. It
  retains the original canonical tree. It also keeps the source bytes of the
  relevant declaration, of its alias and of its transitive Nat helpers.
- Every preparation that receives that selection rechecks it before closure
  or cache use. Private names, changed dependencies and substitute trees of
  the same width are rejected. Host selection grants no module-private
  privilege.
- The `instantiate` method and the provider `new` method supply empty type
  maps.
- A host Basis description and an `Instantiation` are untrusted preparation
  data.

The typed route accepts this root with `A` bound to `main::Tri` and `n` bound
to 1. It retains the original generic header, the closed actuals and the
numeric premise:

```qli
pub enum Tri{A,B,C}
pub unitary fn keep[const A:Basis,const n:Nat](q:Q<A>,word:Bits<n>)->(Q<A>,Bits<n>) requires n>=1 {(q,word)}
```

### Nominal values

A program builds a value of a nominal type with one of two forms and reads a
record field with a third. The common judgment checks fieldless
`Type::Variant` values, explicit `Type { field: expression, ... }` records
and ordinary `value.field` projection. It checks them in runtime blocks and
in classical bodies.
[Nominal values](elaboration.md#nominal-values) gives the elaboration
contract.

Rules:

- A type reference uses the original occurrence table, with its public
  reexports and local shadowing. A local Basis or runtime name does not fall
  back to a global type of the same spelling.
- Member names and diagnostics retain their original source spans.
- A qualified call is a function call. No payload variant and no imported
  bare-variant API exists.
- A record supplies every field exactly once, with its exact declared ordinary
  type.
- The checker checks initializers in their written order of evaluation. The
  resulting type retains the declaration order and the nominal identity.
- The checker checks field privacy in the original declaring module. This
  holds for zero-width fields too.
- Projection checks its receiver once and requires an ordinary record.
  `Q<Record>` is one owner, with no implicit decomposition or observation.
- A call in an initializer retains its normal effects, dependencies and
  ownership transitions. A Unitary or Isometry annotation cannot hide
  observation.
- Empty records and singleton enums are distinct from `Unit` and `Bits<0>`.
- Shorthand, record updates, methods and general `const<T>` are outside these
  forms.
- Execution requires a typed route. Common preparation that succeeds supplies
  no accepted handle.

### Ordinary `match`

An ordinary `match` chooses one arm by the variant of an ordinary enum
value. The common judgment checks
`match value { Type::A => expression, ... }` in both ordinary expression
grammars.
[Ordinary match](elaboration.md#ordinary-match) gives the elaboration
contract.

Rules:

- The scrutinee, which is the value that the `match` inspects, must have an
  ordinary enum type. An ordinary `match` cannot inspect a live `Q<T>`.
- Labels resolve through their original type declarations and visibility.
  A foreign enum cannot substitute through equal spelling, width or
  cardinality.
- Every declared variant must occur exactly once. Wildcard, payload and
  complement patterns are outside this form.
- A normal arm may contain a block. A classical arm is an ordinary expression.
- Parenthesize a record literal in a scrutinee, to distinguish its braces from
  the arm list.
- The checker visits the scrutinee once and checks every arm. This includes
  the arms of a constant constructor in an unused function.
- All arms have the same complete result type tree. Each arm preserves the
  same outer owner frame, zero-width owners included.
- Calls and observation in any arm contribute their normal dependencies and
  effects. Constant selection cannot hide an observing body behind a pure
  public label.
- These source judgments provide no accepted handle independently of the
  concrete route. No route provides implicit measurement, coherent `qmatch`,
  general `const<T>` or a source-preservation theorem.

### Coherent selection

A `qmatch` selects an operation on a target owner by the label of a selector
owner. It preserves coherence across the selector sectors. The coherent
[exact-label `qmatch` form](source-text.md#exact-label-coherent-selection)
checks a `Q<A>` selector and a distinct `Q<B>` target. An arm is a resolved
static operation or an inline block. That section specifies both arm forms.

Rules:

- `qmatch` preserves the complete `(Q<A>,Q<B>)` result.
- Every static arm must have the exact `B -> B` interface, the Unitary effect
  and the `Controllable` capability.
- A fieldless enum label retains the canonical identity of its original
  declaration and the logical variant order. A built-in label retains its
  exact ordinal.
- Neither padding tags nor equal physical width identify a label or a target.
- A nominal target retains its full enum or record tree, and an empty record
  is such a tree. This holds with a built-in ordinal selector and with an
  enum selector.
- No inverse or control capability follows merely from a label.
- Common nominal preparation alone grants no execution.

> **Implementation note.** The finite executable built-in slice uses a fresh
> native whole-circuit encoded equation. A small closed function with named
> arms and a nominal selector or target also uses the native source/arm gate,
> before runtime-root acceptance. It submits its complete callee fragment,
> the original two-owner frame and the separate controlled arm bodies to
> that gate. The physical arm proposal does not erase the target type or
> confer a provider capability. The native code/body and controlled equations
> are required.
> [Coherent selection components](#coherent-selection-components) gives the
> limits.

## General pure operation arrows

```text
Op<A -> B>
Op<A -> B, M>
```

The type `Op<A -> B>` describes a pure operation whose input and output
bases can differ. It retains the exact input basis tree and the exact output
basis tree separately. These two trees are the ports of the operation.
`Op<A>` abbreviates `Op<A -> A>`. The comma slot is a Meaning refinement, so
`Op<A -> B, M>` is unambiguous. [Checked operations](checked-operations.md)
specifies Meanings.

Rules for the type:

- Both ports use only preceding static binders and undergo ordered
  substitution. Equal width does not identify distinct trees.
- Given `U: Op<A -> B>` and `requires Applicable(U)`, applying `U` consumes
  one `Q<A>` owner and returns one `Q<B>` owner. For general ports, the upper
  bound of the effect is Isometry.
- When the common exact-tree judgment establishes `A = B`, the explicit form
  retains the Unitary bound of its endomorphic abbreviation.
- Preparation is the ordinary `Unit -> A` case. `Q<Unit>` is a logical owner.
- A generic body uses the capability bounds and effect bounds that it
  declares. It never uses a more fortunate concrete provider that is bound
  later.
- The common judgment checks the port rules and the capability rules before
  profile selection.

Rules for a provider:

- A concrete provider must be an ordinary unary quantum function. Its checked
  effect, as visible in the original module of the caller, must be at most
  Isometry.
- An external provider uses its public effect. So does a public provider that
  the host selects. Private or internal analysis within the same module
  retains checked inference.
- An annotation cannot make an Observe body pure or make an Isometry body
  Unitary.

Rules for the capabilities and the constructors:

- `Adjointable(U)` requires a provider whose effect is Unitary as its caller
  sees it, and a supported reverse implementation. An adjoint exchanges the
  ports.
- For an opaque formal `U: Op<A -> B>`, direct `adjoint(U)(q)` consumes `Q<B>`
  and returns `Q<A>`. Applying the static adjoint through another operation
  parameter does the same.
- A direct adjoint of an ordinary unary function also exchanges its exact
  ports. The multi-owner
  [runtime-group rule](#direct-runtime-transforms-and-opaque-operations) is
  endomorphic.
- `Controllable(U)` also requires the exact endomorphism `A = B`.
- Repetition requires `A = B`, even for a count of zero.
- Sequential construction matches the exact middle tree. Tensor construction
  retains the ordered pairs of both input and output trees.
- Conjugation preserves the order `C† -> U -> C`. For `C: A -> B`, the middle
  operation is over `A` and the result is over `B`.

Rules for Meaning refinements:

- A monomial Meaning refinement is endomorphic: both ports must match its
  exact declared basis.
- The rectangular `meaning M: A -> B = reference(f);` retains both exact
  trees. The shorthand `meaning M: A = ...;` retains equal ports.
- Composition matches the exact intermediate tree. Tensor retains both ordered
  pairs. Hidden observation, reset or discard is rejected.
- An unsupported path must not omit a codomain, a child or a Meaning
  obligation.

> **Implementation note.** Finite project and Selected Raw retain separate
> operation and Meaning ports within their finite checking bounds. They also
> retain the original provider and Meaning requests of an adjoint. Both check
> the original pure body of a rectangular Meaning and its exact rectangular
> matrix with native `pure-leaf`, including `V†V = I`.
> [Operation arrows in each profile](#operation-arrows-in-each-profile) gives
> the support of each profile.

## Direct runtime transforms and opaque operations

A **direct runtime transform** applies `adjoint`, `controlled` or `power` to a
target. The target is an ordinary function name, its explicit static
specialization or a transparent `power` wrapper. A program writes one to run
the adjoint, a controlled form or a power of a function on live owners. Its
**runtime target type** `T` is the complete input type of a function with one
runtime parameter. With more parameters, `T` is the exact ordered tuple of
the complete input types.

The rules below have one exception: the adjoint rule for a unary function
with differing ports, in
[General pure operation arrows](#general-pure-operation-arrows).

Rules:

- A target of arity zero is rejected.
- `T` must be a nonempty tree of quantum owner leaves. It must equal the
  checked result under the substitutions and the caller premises.
- `Q<Unit>` and `Q<Bits<0>>` are valid leaves, with their ownership and scalar
  phase intact.
- Ordinary `Unit`, `Bit` and `Bits`, empty tuples and mixed classical and
  quantum trees are rejected. Equal width cannot repair a different tree.
- Direct `adjoint` and direct `power` evaluate their input once and return
  `T`.
- Direct `controlled` evaluates the control, then the target, once each. It
  returns `(Q<Bit>,T)`.
- The transform consumes and returns each original owner exactly once. No
  implicit split, join, packing or reassociation occurs.
- The named body must have a Unitary effect as its caller sees it, and the
  required implementation path.
- A transparent Repeat checks its count and its child even at zero.
- Only a runtime self-call to the same DefId under a direct transform may use
  the checked Nat decrease. This permits neither recursive opaque providers
  nor mutual dependency cycles.

The checker records a located RuntimeGroupProvider obligation. The obligation
retains the original provider DefId, the complete runtime interface and the
visible effect. Its association with the source is not an equality of
transformed operators, a provider correspondence or a source-preservation
proof.

### Opaque operations

The runtime-group rule lets a direct transform act on a function with several
runtime parameters. This rule does not widen an opaque `Op<A>`, a static or
host provider, a Meaning refinement, a certified logical operation or a
FunctionEquality contract.

Rules:

- Three interfaces keep one input `Q<A> -> Q<A>`: an opaque `Op<A>`, a static
  or host provider and a certified logical operation.
- Pure FunctionEquality keeps that interface for its checked implementation
  and for any ordinary specification function.
- A declared Meaning is a semantic object, not a runtime function.
- A `tensor_op` description acts on one packed quantum basis, so it also keeps
  one input.
- Transparent specialization derives access conservatively from every Op
  argument, unused ones included. Inverse access requires the `Applicable`
  and `Adjointable` paths of each argument. Controlled access also requires
  `Controllable`.
- A body annotation or a mathematical Unitary property grants none of those
  paths.
- Concrete transform evidence and native checking are separate obligations.

### Function contracts

A function contract pairs an implementation with a specification.
`apply_contract` applies the implementation and records the obligation that
it equals the specification. `apply_contract` evaluates its input first and
consumes one exact quantum owner.
[Function contracts](elaboration.md#function-contracts) gives the
elaboration contract.

Rules for the pure overload:

- The implementation and the ordinary specification are closed declarations
  of type `Q<A> -> Q<A>`, with a Unitary effect that the caller can see. A
  declared finite Meaning may supply the specification instead.
- The common judgment records a located FunctionEquality obligation. It binds
  both exact original DefIds, the interface, category and effect, and the
  source span.
- Binding the identity of a Meaning or of a provider is not matrix equality,
  injectivity, clean return on all inputs, provider correspondence or source
  preservation. Those properties are pending until the independent concrete
  evidence gates discharge them.
- A declared Meaning supplies the request. It is never projected as a runtime
  function.

Rules for the observing overload:

- It compares two closed ordinary functions. Each has an Observe effect that
  the caller can see and one `Q<A>` argument. Both have the same complete
  finite result type.
- The native instrument profile also requires original bodies that genuinely
  observe. A conservative Observe declaration over a pure body does not
  select pure-contract evidence. That concrete route is explicitly
  unsupported, and this holds for dormant obligations too.
- The comparison treats all of these as significant: the complete result
  nesting, the ordered quantum and classical projections, zero-width owners,
  hidden histories and residual states.
- The overload admits no observing `Meaning` and no inverse or coherent
  control access.
- An unsupported result shape or lowering shape is rejected explicitly.

A rejected exact equation can yield a mismatched coefficient within the
diagnostic work limit. The diagnostic then shows the input basis value and
the output basis value with the declared tree shapes:

- The first bit leaf is the least significant coordinate.
- `Unit` contributes no bit and stays visible in the printed value.
- For an encoded equation the labels use the logical input type and the
  physical output type.
- JSON also reports the zero-based integers `counterexample.input_column` and
  `counterexample.output_row`, as [Refinements](diagnostics.md#refinements)
  describes.

> **Implementation note.** Finite project and Selected Raw compare the
> implementation with the independently selected function or Meaning through
> fresh native evidence. For the observing overload they obtain a private
> native instrument equation for the two original accepted artifacts. Each
> executes only the implementation and freshly compares the emitted call
> interval with the selected original reference. The private pair and the call
> receipts retain source identity and stay separate from a whole-root request.
> [Function contracts and Meaning requests](#function-contracts-and-meaning-requests)
> gives the selected checks, including the all-binding native gate.

## Retired spellings

| Retired surface | Replacement |
| --- | --- |
| `CBit` / `CBits<n>` | `Bit` / `Bits<n>` |
| Ordinary `false` / `true` | `0` / `1` |
| The result-type spelling `()` | `Unit`. The value spelling `()` is unchanged. |
| A same-width value of a different tree | An explicit specified conversion, or rejection. No implicit cast exists. |

The retired type and literal spellings are rejected with migration diagnostics
(`parse`). They are not accepted aliases.

<a id="selected-source-execution"></a>

## Selected-entry commands

The selected-entry route takes one selected entry function and explicit
module bindings. On this route, the commands `check`, `run`, `sample` and
`emit-proposal` take these arguments:

| Argument | Role |
| --- | --- |
| `--entry=module::function` | The selected entry |
| `--module=name=PATH`, repeated | The module bindings |
| `--type`, `--nat`, `--operation`, `--operation-type`, `--operation-nat` | The explicit static bindings of the entry and of its providers |
| `--ir-profile=auto\|raw\|hierarchy` | The IR and checker route |
| `--basis=N` | The quantum input selector of a hierarchy execution |
| `--request=PATH` or `--qpe-provider=PATH` | Check the hierarchy against a caller-supplied composition request or a named QPE provider. Supply at most one. |
| `--shots=N` and `--seed=N` | Sampling requires both. The shot count ranges from 1 through 1024. |
| `--output=PATH` | Destination for `emit-proposal`. |
| `--lean-kernel`, with the alias `--kernel` | The native checker. An explicitly configured `QLEISLI_KERNEL` also selects it. |
| `--format=json` | The common [`qleisli.result` envelope](diagnostics.md#the-result-envelope) |

Rules for the commands:

- The `sized` prefix is removed. `qleisli sized ACTION ...` is a usage error
  (`usage`) with exit status 2 and a migration hint. The CLI reports it
  before any source or native work. Write `qleisli ACTION ...`. Both the text
  error and the JSON error identify the removed prefix.
- A selected command returns a JSON result object. With `--format=json` it
  uses the envelope for success and for diagnostics. Without that flag, an
  error is text on stderr.
- A result retains the entry, the IR profile and the fields for the source
  scope and the native scope. A consumer must not require the narrower JSON
  object of the removed hierarchy-command wrapper. Protocol, schema and
  machine profile identifiers are unchanged.
- Duplicate checker aliases are rejected. The CLI downloads nothing and falls
  back to no alternate checker.
- `emit-proposal` writes an untrusted proposal. It invokes the native checker
  only for a source with function contracts or operation Meaning requests.
  It must check those before emission. It is distinct from the project
  command `emit-ir`, which freshly verifies its emitted artifact.

Rules for the root:

- An explicit selection of a public `main::main` uses the eligibility of an
  exported function.
- Project invocation has a separate contract: an ordinary zero-argument
  `fn main` with a closed classical result. A private project `main` does not
  become an exported selection.
- A selection may name a public `classical fn` as its ordinary root, subject
  to its input and profile restrictions. The typed route uses the original
  classical header and body. It invents no ordinary wrapper.
- A valid quantum declaration that is not selected is source checked. It is
  not an execution root.
- On Raw and typed ordinary or mixed routes, `run` and `sample` require
  zero original runtime parameters. A parameter of zero physical width counts
  as a parameter. Hierarchy execution can take a quantum basis input. Its
  [root and effect requirements](#hierarchy-roots) also govern sampling.

Rules for `--ir-profile`:

- `--ir-profile=auto|raw|hierarchy` selects an IR and checker route, not a
  physical target model.
- `auto` uses the hierarchy for its supported root signature, effect and
  source-step profile. An explicit capability mismatch selects Raw.
- Generic errors and capacity failures are not profile selectors.
- A caller request or a named-QPE provider fixes the hierarchy route.
  Combining one with explicit Raw is rejected before native checking.
- After a route is selected, its lowering failure or native failure
  propagates. The CLI retries no weaker route.
- For a source that needs the typed route, `auto` and `raw` select that route.

### Raw execution

Raw execution runs a selected entry that takes no runtime input. Raw checking
retains the original source signature.

Rules:

- Raw `run` and `sample` require zero declared runtime parameters and no
  quantum result. A `Unit` parameter is an argument, although it has zero
  physical width.
- Any explicit `--basis` is rejected on Raw, even one of zero.
- Native acceptance comes before the independent source-step comparison and
  the Raw execution.
- The result reports native validity, no caller request, the step comparison
  and `source_meaning_verified: false`.
- Acceptance of the Unit maps does not make Raw execution with a quantum
  result available.

### Hierarchy roots

Hierarchy execution takes the computational basis input selected by
`--basis=N` (default 0). A public unitary root can act on that input.
An observing root can produce measurement outcomes. For example, consider
these public entries in module `main`:

```qli
pub unitary fn keep(q: Q<Bit>) -> Q<Bit> { q }

pub observe fn read(q: Q<Bit>) -> Bits<1> {
    let b = measure_z(q);
    prepend_bit[0](b, empty_bits())
}
```

With `--ir-profile=hierarchy --basis=1`, `run` on `main::keep` returns
amplitudes `[[0,0],[1,0]]`. Sampling `main::read` with `--shots=3 --seed=7`
returns outcomes `[1,1,1]`. Sampling `main::keep` fails with `unsupported`
because this entry performs no observation.

The preparation profile admits a root with a checked public Isometry effect
and an actual Unitary or Isometry effect. The root has quantum entry values
and quantum results, optionally accompanied by one ordinary `Bits<0>` result.

Rules:

- An Isometry root must fit the preparation and pure-operation profile. That
  profile is fresh zero initialization where needed, followed by checked
  unitary hierarchy operations, with no observation.
- A unitary implementation needs no fresh preparation. Its `SourceDefinition`,
  `SourceStep` and Raw effects stay Unitary.
- The public Isometry bound governs eligibility as an external provider,
  eligibility for a Meaning and eligibility for inverse or control access.
- A public Observe bound over that implementation cannot recover the sharper
  hierarchy eligibility.
- Ordinary `Unit` result ports are omitted, as
  [Tuples and patterns](#tuples-and-patterns) describes.
- `check` on an Isometry root reports the `sized-isometry` profile.
- `run` on an Isometry root returns the residual quantum width and the
  unnormalized complex coefficients of the single branch. It does not remove
  the scalar phase.
- A retained `Q<Unit>` owner, explicit `unit` and `finish` work and every live
  caller frame retain their original ownership and phase obligations.
- `sample` and named-QPE selection require a public Observe contract and an
  observing supported artifact. A broader annotation does not fabricate
  observing operations or rewrite the Raw effect.
- A hierarchy result retains its separate scope: producer-consistency,
  caller-composition or named-QPE. It does not claim the Raw step
  comparison.
- An unsupported combination of source and profile is refused explicitly. Raw
  retains its own classification.

> **Implementation note.** The Isometry profile uses the
> initialization/evolution/readout transport with zero measurements. Its
> single empty outcome is a transport carrier. It introduces no source Observe
> effect, no measurement and no conversion between `Unit` and `Bits<0>`. The
> hierarchy `lower()` path retains its quantum and ordered-readout contracts
> and rejects Boolean steps at their source locations. A failed native
> hierarchy decision is never retried as weaker Raw validity.

## Status and limits

This section states what the implementation supports and what is proved.
Finite project and the selected projection both implement bounded opaque
Basis specialization. Three pieces of work are in progress: the convergence
of the concrete emitters, the integration of Meaning evidence and general
source preservation.

### Capacities

| Capacity | Limit | Scope |
| --- | --- | --- |
| Work of the common judgment | 1,000,000 units | Both routes, before specialization |
| Type capacity of one value | 4096 cells, depth 64 | Both routes |
| Retained runtime scopes | 16,384 cells | Selected-entry route |
| Width of a word and of a closed Basis binding | Eight total basis bits: `n <= 8`, and `n < 8` for `prepend_bit` | Selected-entry route |
| Width of a closed Basis/Nat substitution | Twelve physical bits, including nonzero registers. The result of `prepend_bit` must fit. | Finite project |
| Closed type description | 4096 type nodes, depth 64 | Selected-entry route |
| Function expansions, counting calls and folds | 1024 | Selected-entry route |
| Call depth | 16 | Selected-entry route |
| Raw instructions | 10000 | Selected-entry route |
| Producer work and preparation storage | 100000 units or cells | Selected-entry route |
| Live wires across whole call frames, checked before allocation | 16 | Selected Raw |
| Carrier type profile | Six physical bits, 128 nodes, prefix depth 32 | `BasisBinding::carrier_description` and the `finite-ordinary-root-v2` request |
| Ordinary-root domain | 64 input rows, 64 parameters, 128 total parameter nodes, 128 input storage nodes | The `finite-ordinary-root-v2` request |
| Dense mixed-runtime component | Six bits | The `finite-runtime-root-v2` request |
| Built-in `qmatch` slice | Six joined bits, 1024 steps | Finite executable profile |
| Operation Meaning bindings | 1024 bindings, 100000 aggregate provider bytes | `check_operation_meanings` |
| Shots of `sample` | 1024 | Selected-entry route |
| Shots of `sample` | 1,000,000 | Project route |

Limits that apply to these capacities:

- The common work budget charges before source visits, for copied or allocated
  type and lexical cells, and for normalization and solver work.
- The selected producer applies a conservative work ceiling. The source,
  metadata and native caps are separate from it.
- The expansion of a substitution is checked before copied trees are
  allocated. Retained type bindings and cache data count against the
  100000-cell preparation budget.
- Finite project has its own aggregate, type and snapshot limits. The limits
  of this table are separate from them and from native and evidence work.
- The carrier type profile does not replace the twelve-bit contract of the
  broader finite language.
- Logical cardinality and code coordinates are separate from physical width.
- Packaged hierarchy bases retain the width limits of the selected-entry route.
  Every node of a basis tree, a zero-width factor included, is charged to the
  preparation limits on storage and depth before copied trees are
  materialized.
- These are limits of the implementation, not prohibitions on source types.
  They establish no separate type universes.
- A capacity refusal is not a proof of a semantic impossibility. The
  preparation limits and the shot capacities are adapter limits. They are not
  a discharged quantitative RS theorem or a quantitative resource certificate.

### Lowering profiles

Each lowering profile supports a part of the language. The lists below give
that part for each profile.

Finite project:

- It supports ordinary `Unit`, `Bit` and `Bits` values and exact products,
  together with their supported quantum owners.
- Complete explicit substitutions for Basis, Nat and Op parameters close each
  original checked interface before the body is lowered. This includes
  nonzero registers.
- Static branches and carry folds use their original resolved plans. Unused
  declarations, inactive arms and empty fold bodies retain their contract
  checks.

Selected Raw:

- It transports ordinary `Bits<N>` values within the selected-entry bounds.
  Quantum basis shapes outside the exact coefficient and constructor profile
  are rejected.
- It supports `phase[j,k]` only when the exact angle is an integral multiple
  of an eighth turn. The source domain requires `k <= 8` and `j < 2^k`, and
  `8*j / 2^k` must be an integer. That many T gates implement the phase, and
  zero gates implement the identity. Smaller angles are not rounded.
- `phase[1,3]` and `phase[2,4]` are exactly T. `phase[1,4]` requires the
  hierarchy phase target. This distinction is one of target capability, not
  of source type or edition.
- It supports retained quantum Unit inputs and returns, exact
  `global_phase_eighth` and the explicit Unit maps.
- Closed Definition/Repeat providers support forward, inverse and controlled
  access through ordinary calls within the exact pure-circuit profile. This
  includes conditional scalar action on a Unit owner. Their original Meaning
  requests are mandatory, even for unused bindings and zero repetitions.
- Coherent lifting evaluates complete bounded ordinary label bodies and emits
  Raw `LiftBasis`, with separate native acceptance and source-step comparison.
- Independent source-step comparison checks the ordered owner result. Native
  validity alone cannot establish that a source returned the intended
  zero-width owner.
- Exact unary `Q<Unit>` and `Q<Bit>` endomorphisms retain the finite root
  interface that is derived from their source. A separate native finite
  request can then bind the same artifact to an independently supplied
  matrix. No conversion to a different basis is inferred from width.
- Checked open runtime invocation and runtime branches are unfinished.

Selected hierarchy:

- Its coherent-lifting bridge admits only the singleton `[0]` zero-basis
  conversions and zero-Bit preparations of the
  [coherent-basis profile](coherent-basis.md#concrete-profiles-and-proof-boundary).
  The restrictions on other tables, static transforms and preparation after
  observation apply.
- Its Unit owner port, its `Bits(0)` owner port and its empty list of quantum
  ports are three distinct interfaces.

Shared behaviour:

- Finite project emission and Selected Raw emission share quantum registers
  and fresh identities. They also share the transitions for init0, H, X, CNOT
  and measurement. A measurement consumes its owner and produces an ordinary
  `Bit` that Boolean operations may use.
- Each call gets its own source-ID environment. The global token, wire and
  classical supplies stay fresh.
- A total `classical fn` body is reusable as an ordinary runtime computation.
  Supported Unit, Bit and product calls use the same checked expression nodes
  and eager ordinary operations in both consumers.
- The effects of runtime arguments stay in the caller. An ordinary call
  grants no coherent injectivity and no Meaning evidence.
- Both Raw adapters transport ordered ordinary `Bits` values within their
  finite widths.

### Operation arrows in each profile

| Profile | Support for general arrows |
| --- | --- |
| Finite project | Different ports, with the Unit/Bit/product and closed-entry restrictions |
| Selected Raw | Retained sequential, tensor, adjoint, control, repetition and conjugation trees, under their checked port, capability and capacity restrictions |
| Selected hierarchy | Transparent providers and ordered constructor trees. Its refined finite leaf is square, so a rectangular Meaning requires Raw lowering. |

Selected Raw:

- Its structural `unit` and `finish` maps retain zero-width logical owners
  without allocating or discarding a physical qubit.
- Original finite endomorphic Meaning requests are checked against their
  materialized Raw bodies before checked hierarchy construction. This holds
  for requests on whole constructor trees and on their annotated descendants,
  and for descendants under zero repetition.
- The checked collection also supports refined Raw direct, sequential, tensor,
  inverse and controlled application. Instruction-interval checks and
  transformed-substep checks apply under the finite bounds.

Selected hierarchy:

- Sequential application lowers both bodies. Tensor splits the packed input,
  applies the left and right factors, and joins their ordered results.
- Initializations retain their source paths and complete caller frames.
- A separate replay checks the canonical split/join boundaries of the tensor
  and the stable initialization extraction. It is not a proof of the source
  meaning of every gate.
- Principal-Unitary adjoints exchange exact ports, even when the trees
  differ. Packed control requires an exact endomorphism. Powers check that
  condition even at zero.
- All proposals require fresh native acceptance under the capacity bounds.

Native acceptance of produced IR does not establish source preservation.
Public results retain `source_meaning_verified: false`. Bounded independent
exact requests and small complex executions are regression evidence, not a
general QS or PR theorem.

### Typed routes

A typed route carries the original source types to the native checker in a
typed root request. The lists below say when a route is typed and what each
request checks.

Selection:

- Preparation of the complete original types, bodies and effects retains
  nominal declarations. It does not silently omit their unused functions or
  quantum effects.
- For a source with nominal declarations, `--ir-profile=auto` and `raw`
  execute a public runtime function through the common finite emitter and the
  `finite-ordinary-root-v2` or `finite-runtime-root-v2` gate.
- A selected root with Basis or Nat parameters retains its original generic
  header, closed actuals and numeric premises through the
  `finite-runtime-root-v2` gate. A nominal actual such as
  `--type=A=labels::Tri` is bound by its name and source, and an unused
  nominal actual retains its original source.
- A typed route refuses a selected root with an operation formal or with
  operation bindings (`unsupported`). The closure of an operation formal has
  no typed transport.
- The selected projection refuses a source with a finite type declaration
  (`unsupported`).
- `emit-proposal` is refused on a typed route (`unsupported`). Portable export
  cannot erase the typed frame.
- The common emitter handles ordinary and mixed interfaces, including
  ordinary generic dependencies. Small quantum temporaries use the same Raw
  emitter and all-history checks.
- Finite project checks finite ordinary parameters and results and executes
  eligible closed callers through the typed route.
- The wider `qmatch` profile, full nominal `qmatch` and the
  source-preservation proofs are pending. No inverse or control access follows
  from preparation.

The `finite-ordinary-root-v2` request:

- The request retains the original selected function and the ordered forests
  of ordinary parameters and results. It also keeps the complete SSA storage
  of the inputs and outputs, the proposed input rows and the public effect.
- The native checker independently reads the original signature, checks the
  nominal declarations and the Raw root, and enumerates every canonical input
  from those types. The proposed rows must equal that entire ordered domain.
- For every input the native checker checks the complete input storage. It
  reconstructs every hidden instrument history, zero-probability histories
  included. It interprets the complete result storage.
- Flattened storage must equal the ordered classical input and output lists
  exactly. A changed enum axis, record field order, nominal identity or
  zero-width node is refused.
- This ordinary-only component enables no quantum input or output carrier. A
  version-1 request is refused without fallback.
- A read of an original parameter type or result type retains every lookup of
  an import and of a public reexport. This includes type references inside
  record fields. The same independent reader reconstructs the nominal tree
  and these original source rows. An alias keeps the identity of its terminal
  declaration.
- When a supplied source row needs body provenance, the same native root check
  uses the original body and callee reader to justify the extra type paths.
  Row projection and coverage comparisons are charged. Unused Nat helpers and
  unrelated modules cannot justify their own source rows.
- QLV3 compares the retained objects with the fresh description of the native
  checker before it issues its private accepted program. The objects are the
  graph, the selected entry, the parameter and result types, the complete
  input rows, the storage and the effect. Clones retain those typed objects.
  Untyped rechecking rejects this mode.
- Text and JSON check reports identify ordinary-result checking separately
  from an external algorithm specification. Runtime output distributions
  retain the declared low-axis-first classical output order.
- This gate does not prove original AST lowering, the decoder and native
  compiler, or numerical runtime preservation.
- The simulation APIs require closed roots. Parameter checking grants no
  unchecked runtime for arbitrary inputs.

The `finite-runtime-root-v2` request:

- The project emitter and the selected emitter connect mixed runtime
  interfaces to this gate. These include `Q<enum>`, `Q<record>`, mixed
  tuples, zero-width owners and structural split/join. Nominal quantum owners
  use it.
- The emitters snapshot the input storage before expansion consumes it. They
  retain complete output types and ordered owner ports. Native reconstruction
  checks the emitted body and does not trust its descriptor.
- An internal runtime-signature reader retains complete parameter and result
  prefixes, not only a flattened list of quantum owners. Ordinary `Unit`,
  every tuple boundary and each explicit `Q` node stay present. The original
  finite type queries retain nominal declarations and source paths.
- Reading a declared effect annotation does not check its body or certify that
  effect. The reader alone provides no runtime capability. Typed-root
  execution needs the full type tree, the body and effect, and the native
  code-space binding.
- The internal mixed-runtime root component matches those complete types to
  ordinary storage and ordered Raw quantum ports. It then reuses fresh
  original-root validation.
- The component independently enumerates every ordinary input. For each one
  it checks every reconstructed hidden history, the exact quantum code-space
  equations and the complete logical Gram sum.
- Logical cardinalities and the Raw effect bound the public label. A physical
  square matrix cannot justify a rectangular logical Unitary label.
  Observation is Observe, even at logical dimension one.
- The mode reads the full original request. Through QLV3/QDV it compares the
  request with the retained Rust objects. The comparison covers the freshly
  checked graph, the full parameter and result types, the ordinary storage
  and the ordered quantum ports. It also covers the complete named Basis/Nat
  actuals, the canonical inputs and the public effect.
- Its execution-only decision retains the complete request in the accepted
  program and in every clone. Rechecking walks those same objects again.
  Altered types, storage or graph metadata are refused.
- Closed simulation and sampling also inspect the original runtime parameters,
  zero-width arguments included.

Nominal source:

- Finite project may construct enum and record values, project fields and
  execute exhaustive ordinary `match` inside an eligible closed root. This
  includes ordinary parameter functions inlined through the same body path.
- Eligible closed ordinary project roots and public selected roots use the
  typed route for ordinary `match`. General selected integration is
  unfinished.
- A classical function with a built-in signature may use nominal intermediate
  values. A nominal constructor visit in a nested call or a branch also
  selects a typed route when the final result is a built-in type.
- Ordinary nominal classical calls lower their checked original bodies in the
  internal producer. They require no enumeration of physical label tables.
- Table preparation follows the original resolved uses of types and callees.
  It defers a table whose parameter or result types contain nominal nodes. It
  also defers a table whose original resolved body uses nominal values,
  directly or through classical callees. It defers the callers too. It does
  not interpret nominal values as untyped physical labels.
- Unused original bodies are checked. Built-in-only tables stay eager. A
  basis or Meaning consumer refuses a function whose nominal table semantics
  are not implemented.
- When a selected dormant operation reaches a concrete table consumer,
  preparation follows only that original classical function and its classical
  callees. Unrelated declarations do not become table roots.
- The ordinary-root, runtime-root and v5 `qmatch` routes can retain imported
  nominal dependencies that only the original body uses. The coverage check
  requires a resolved original use.
- Selected roots and project roots can use coherent basis maps over canonical
  nominal codes. The maps evaluate the deferred bodies on canonical source
  values. The v5 source check binds the original finite expression to the Raw
  interval, with or without a coherent selection.
- A selected coherent arm or a standalone checked application can use a
  Meaning with a built-in signature and a classical helper that contains
  nominal values. The native check compares the original Meaning with the
  applied operator.
- Supported square and rectangular Meaning applications also check their
  exact nominal ports and their original supplying operations.
- The two finite `with_computed` forms use the same original-source route for
  supported nominal predicates. The checker evaluates the exact logical input
  codes, checks the physical padding and binds the emitted region to the
  original use body. The certified form also checks the original logical
  supplier and the exact auxiliary cleanup. The
  [production boundary](production-boundary.md) gives the scope and the work
  limits.
- Closed function-equality and Meaning obligations in unused declarations and
  zero-count regions use the shared finite evidence gates before a selected
  result is returned. Their dependencies on original Meanings, tables and
  native bodies are prepared in dependency order. This includes references
  outside the selected closure. Each dependency retains its original
  declaration. Source checking alone does not discharge those semantic
  obligations.
- The exact computation witnesses have a separate scope from complex
  denotation, original source-body preservation and numerical-runtime
  correspondence.

These are bounded implementation checks. They are not a source-preservation
theorem.

### Coherent selection components

This section gives the routes that carry a coherent selection and the
components that check one.

Routes:

- Selected built-in `qmatch` and ordinary Basis/Nat callers use the common
  source emitter. They prepare named arms through the provider evidence gates.
- The hierarchy projection is separate.
- The bounded adapter for small closed functions with named arms does not
  support general bodies.
- The full extension to twelve joined bits and 64 labels is separate required
  work. So is original-source preservation.

The internal `Qirf.ContextSector` component:

- It reads the written arm names, the full source target trees and the public
  effects. It associates each arm with an original function-evidence entry and
  derives the implementation index from that entry.
- One fresh graph includes those evidence subjects and the original main, arm
  and control programs. Original function bytes and resolution paths stay
  bound to the same checked entry, with its complete input, body and
  dependency snapshot. Keeping an evidence table and an index cannot change
  the resolved function name.
- Exact checks of the code space, the phase and the controlled action are
  required.
- Original quantum parameter patterns and structural `let` and tuple moves
  identify the selector and the target in a complete linear source frame.
- The complete original function keeps every quantum parameter and returned
  owner. This includes additional zero-width owners and a differing parameter
  and result order. The independently derived local pair stays in
  selector/target order.
- The pure contract of the pair cannot sharpen the public Isometry or Observe
  label of the outer function. Neither can the whole-subject Unitary request.
- The two-port subject uses the exact original parameter and result order. It
  retains distinct logical identities even when both types and physical widths
  coincide.
- The complete structural suffix and the final expression retain the order of
  the returned owners. An unswapped Raw subject cannot implement a reordered
  return merely because both owners have equal or zero physical width.
- Unknown prefix and suffix expressions are refused.
- Direct `h` and `global_phase_eighth` calls are checked as exact primitive
  events before, between and after selections. This includes grouped and
  nested calls, with their original callee-token coordinates.
- The source traversal derives the evaluation order of the arguments
  independently of the proposed literal positions.
- Arbitrary calls, control flow and a general source-to-Raw mapping are
  required separate work.
- The enclosing internal native/QDV route checks this component. It grants no
  handle for ordinary source execution. It proves no general lowering of
  source bodies. It does not complete the twelve-bit scope.

The source component:

- It derives the transport of logical owners from the original Raw
  operations, independently of coincident wire lists.
- Explicit join/split pairing retains complete source roles through unitary
  owner moves. It checks each returned token against the source result.
- Matching zero-width source and Raw permutations are allowed. Mismatched
  permutations are refused.
- An atomic source `Q<T>` stays opaque to this structural transport.
- Other typed refinements, allocation and release, and general source/arm
  mappings are separate obligations.

### Function contracts and Meaning requests

[Checked operations](checked-operations.md) specifies `checked_op` and the
Meaning forms. This section gives the checks of the selected projection, one
API at a time.

Function contracts:

- `ElaboratedProgram::check_function_contracts(kernel, budget)` returns an
  immutable preparation. It contains checked receipts for every original
  FunctionEquality obligation, those of unused callers and zero-count bodies
  included. The receipts retain the exact implementation, specification and
  source dependencies.
- One shared exact-work budget covers these checks and their dependency
  checks. The limits on depth and on aggregate artifact bytes apply.
- Unchecked Raw lowering and hierarchy lowering reject outstanding function
  contracts. `lower_raw_with_kernel` performs the checks before emission. The
  CLI checks them before it selects its concrete IR profile.
- Pure Raw emission carries the receipt in its Contract step. Independent
  source replay checks the original pair, the owner, the direction and the
  ordered axes.
- Hierarchy emission embeds the complete bytes of the wrapper that bears the
  receipt in a checked finite leaf, with its dependency evidence.
  Initialization replay checks that wrapper and its surrounding coordinate
  renaming.
- Both emitted artifacts require fresh native acceptance. A replacement with
  an equal matrix and different implementation or specification bytes cannot
  substitute for the original receipt, which is bound to the source.
- For the observing overload, selected compilation uses the finite Raw
  profile. Its separate source replay checks the original call and the ordered
  result before a fresh native equation checks the interval. Hierarchy
  lowering and checker-free emission reject this overload.
- These bounded checks are not a general source-preservation proof.

Meaning tables:

- Selected preparation evaluates every declared finite Meaning from its
  original classical body and resolved dependencies, unused targets included.
- A permutation target must be a total bijection. A phase target returns the
  exact three-Bit product for powers of zeta_8, including a scalar phase on
  `Unit`.
- These bounded checks retain Unit, Bit, Bits and product tags and leaf order.
  They share the common work budget.
- The immutable preparation retains the tables under the original resolved
  Meaning definition IDs, with the complete basis tree and the permutation or
  phase rows. Closed operation binding checks that same requested basis. It
  does not substitute another target of the same width.
- Tables are untrusted requested data. They do not establish provider equality
  or authorize execution. Providers must separately satisfy the original
  requested tables through the native comparison below.

`ParsedProgram::finite_meaning_target`:

- It resolves one original Meaning into an untrusted `FiniteMeaning` request.
  It selects no provider and issues no accepted handle.
- The finite signature describes exact Unit, Bit, atomic Bits and ordered
  product trees. Its Bits width is an explicit unsigned 32-bit field.
  `Bits<0>` is distinct from `Unit`, `Bits<1>` from `Bit`, and `Bits<2>` from
  a two-Bit product. Neither conversion nor native checking substitutes a
  type of the same width.
- The native finite-leaf gate can compare the request with provider bytes. The
  caller must bind that result to the source instance and its dependencies.
  Requesting a target alone does not enable a refined operation.

`RawSourceProposal::check_finite_meaning`:

- It checks an independently requested operator on the bytes of that proposal
  through the native finite gate. It then replays the retained ordered source
  steps.
- The returned `SourceMeaningCheck` borrows the immutable source and the
  requested target and retains the native leaf. It cannot substitute another
  source or request.
- The profile requires a unary Unitary endomorphism on an exact
  Unit/Bit/Bits/product quantum basis. The Unit maps `unit` and `finish` do
  not widen that interface.
- Unsupported interfaces, substitutions of a type of the same width and
  invalid work budgets are rejected before native IO.
- This single-leaf API is not an AST-to-step theorem. It does not
  automatically check a declared `Op<A,M>` annotation. Generic admission
  requires the all-binding collection below, which covers unused providers.

`ElaboratedProgram::lower_raw_operation(name)` and
`lower_raw_operation_at(caller, name)`:

- The first selects one original entry operation binding and its called
  dependencies. The second selects a binding in another retained instantiated
  definition.
- The returned proposal retains the complete immutable caller graph and the
  original instantiation. `operation_binding()` identifies the original caller
  and binding. `definition()` identifies the underlying closed provider
  definition. `operation()` retains the complete operation wrapper.
- A repeated subject is the entire repeated operator, and the exact
  zero-count identity is such a subject. It is never only the base
  definition. Emission and independent ordered replay apply each retained
  repetition within the aggregate call, work and depth limits.
- A zero count retains the quantum owner and does not bypass the capability
  preflight of the dependencies.
- The interface, the emitted bytes and the ordered replay derive from that
  subject, not from the caller or a rewritten caller identity.
- Closed Definition/Repeat operation bindings may be forwarded through
  ordinary helpers. Forwarding preserves their arguments and their original
  requested meanings.
- Inverse and controlled access materialize the pure circuit with exact phase
  and ordered routing. Independent source replay checks its action and the
  suspended caller owners.
- Opaque assertions and unsupported operation constructors are rejected.
- This explicit preparation API neither admits the caller nor performs the
  mandatory check of all unused bindings. Generic Meaning-refined execution
  requires that enforcement.

`SourceMeaningCheck::lower_hierarchy()`:

- For an explicitly checked original operation binding, it emits the caller
  hierarchy. It uses the exact QIRF bytes and the requested matrix of that
  leaf as the finite node for the complete operation key. Explicit renaming
  preserves the typed owners and axes.
- The resulting hierarchy is an untrusted proposal. Fresh native hierarchy
  checking rechecks the embedded bytes against their matrix description.
- A separate native-valid provider cannot replace those bytes while it retains
  a different requested operator.
- This bridge does not automatically collect or check other original Meaning
  annotations, and it does not prove source elaboration sound.

`ElaboratedProgram::check_operation_meanings(kernel, budget)`, the all-binding
native gate:

- It locates every original `Op<A,M>` formal by its resolved definition ID in
  each retained specialization. This includes unused bindings and nested
  callers.
- It checks the closed exact basis against the original Meaning. It compares
  the complete provider operation, repetition included, with that fixed
  target through fresh native finite checking. It then replays the source
  steps.
- One shared exact-work budget covers all bindings. Exhaustion and unsupported
  interfaces are rejected.
- The selected projection also retains explicit
  `checked_op(implementation, M)` requests by their original resolved Meaning
  ID. These requests apply even when the receiving formal is unrefined or
  unused.
- A request attached to a repeated child is checked against that child, even
  under a zero-count repetition. It is not compared against the outer
  identity. Forwarding an operation and requesting another Meaning retains both
  requirements.
- A direct operation-valued step, such as
  `adjoint(checked_op(implementation, M))(q)`, checks the underlying
  implementation before it applies the requested transformation.
- The immutable proposal locates the original caller binding or step and the
  exact child depth. Equal names or a native-valid replacement do not
  substitute another subject.

The private `CheckedSourceMeanings` collection:

- Only this collection can lower a refined caller hierarchy. Its finite nodes
  embed the checked provider bytes and matrices. The complete output graph
  requires fresh native hierarchy acceptance.
- Plain hierarchy lowering, single-leaf hierarchy lowering and unchecked Raw
  root lowering refuse refined callers.
- `CheckedSourceMeanings::lower_raw` independently replays the
  direct-application intervals. It retains their real owner IDs, scalar events
  and ordered axes, and it freshly checks each interval against the original
  requested matrix. The complete Raw proposal requires fresh native validity
  and source replay.
- Inverse and controlled access retain the original subtree requests, the
  substep ranges and independent axis boundaries. Fresh native equations
  compare these with adjoint or control-lifted exact matrices.
- Conditional coordinate reconstruction preserves hidden output reordering
  and the Unit phase.
- Source `ctrl` can coexist with Meaning requests on Selected Raw through the
  exact sector gate. Finite equations and their sector replay share the budget
  of the caller.
- Expanded closed audit roots check every original request in their own
  concrete graph, requests in unused bodies included. All original control
  obligations must retain concrete call coverage.
- Unclosed generics, erased call intervals and symbolic inverse or control
  bodies that contain source `ctrl` are rejected.
- The selected-entry commands use the same all-binding gate. A native failure
  cannot select another profile. For a refined source, `emit-proposal` needs
  the native checker for these binding checks, and its output is an untrusted
  proposal.

Scope of these checks:

- They connect exact Unit/Bit/Bits/product provider bindings to emitted finite
  nodes. A zero-width Bits owner retains its scalar phase, even when control
  makes it a relative phase.
- The finite limits on width, shape, depth and work apply. Unsupported
  provider capabilities and the materialization of ordinary runtime Bits are
  rejected explicitly in this leaf profile.
- Four kinds of preservation are separate proof obligations: original
  source-to-table, AST-to-step, execution and general hierarchy preservation.
  A successful collection is not a full source-preservation theorem or a
  constitutional guarantee.

### Rust API

A Rust program reaches the selected-entry route through the types of this
section. Import `ParsedProgram`, `BasisBinding`, `OperationBinding`,
`Instantiation`, the elaborated source types and the proposal types from
`qleisli::frontend::compile`. No `qleisli::frontend::sized` module and no
compatibility alias exists. The internal `specialize` module is private. A
prepared source or an emitted proposal grants no native acceptance authority.

| API | Contract |
| --- | --- |
| `ParsedProgram::instantiate_runtime_with_types` | Checks all host bindings and defers the selected projection |
| `Instantiation::compile_runtime_with_kernel` | Borrows the unchanged original AST and text and obtains a fresh complete common judgment with its own original occurrence associations. It never combines cached facts with the indices of a different check, and it never fabricates a nongeneric source header. |
| `SelectedRuntimeProgram` | Retains the immutable instantiation and the accepted artifact and request. Its source check covers every supplied declaration. Concrete eligibility and root acceptance concern the selected dependency closure. |
| `Instantiation::compile_ordinary_with_kernel` | Requires an ordinary-only interface and uses the same emitter. `SelectedOrdinaryProgram` is a compatibility name for the retained wrapper. Neither API synthesizes source. |

`BasisBinding::carrier_description()`:

- It produces the ordered prefix atoms for an untrusted internal carrier
  request. It retains the exact nominal source bytes, the order of variants and
  fields, the product shape, and singleton and zero-width nodes.
- Constructing these atoms grants no accepted handle and no
  source-preservation result. The complete typed ports, the body and
  dependencies, and the exact logical request need fresh native checking.

`Instantiation::check_carrier(kernel, logical, budget)`:

- It is a separate bounded route that only checks. It uses the common
  judgment, the selected Builder and the Raw emitter for pure quantum owners
  and ordinary Unit products, and it retains complete nominal trees.
- The caller supplies the independent exact logical matrix. The adapter never
  infers the requested action from its emitted physical matrix.
- Fresh native checking binds the typed input and output owner forests, the
  public effects, the original nominal declarations, the Raw dependencies and
  the exact code/body equation. A second reader replays the retained source
  steps against that same immutable native-compared body.
- Original source rows must be covered by exact nominal origins in the
  request. Unrelated rows are refused. So is an uncovered module that holds
  only helpers or only imports. Ordinary native checking retains its
  evidence-only source-use rule.
- The returned `CheckedSourceCarrier` retains its complete source preparation
  privately and lets a caller inspect the artifact and the request. It offers
  no escape to an ordinary accepted program, no runtime invocation and no
  inverse or controlled access.
- `source_meaning_verified()` is false. Retained-step replay does not prove
  original AST elaboration.
- The route checks real enum and record identity and scalar bodies. It enables
  no ordinary constructor values, `match`, `qmatch` or general source
  execution.

The public `SourceType` view:

- `kind()` returns `"unit"`, `"bit"`, `"bits"`, `"tuple"`, `"nominal"` or
  `"unresolved"`. An ordinary leaf and a quantum leaf have the same kind.
  Callers must use `is_quantum()` to distinguish their ownership.
- Ordinary `Unit` and `Q<Unit>` both have kind `"unit"`, width zero and no
  tuple fields. Only the latter has a quantum owner.
- A packaged quantum tuple has kind `"tuple"` and no ordinary destructuring
  fields. `quantum_basis()` exposes its exact read-only basis tree, and
  `FramePort::basis()` retains the same whole tree on a quantum port.
- Code must not infer ownership, arity or equality from width or kind alone.
- The migration of the source spellings changes no native classical port tag.

`ElaboratedProgram::lower_raw`:

- It produces an untrusted finite proposal for Unit, Bit and Bits values and
  exact ordinary or packaged quantum products. The proposal includes
  specialized ordinary helper calls and static folds.
- Its `source()` retains whole parameter and result trees and the original
  source instance. Native `Kernel::accept` must check `proposal()` before
  execution.
- `validate_source_steps` separately compares the exact accepted Raw
  instructions with the retained source-step graph. It does not prove the
  preceding source elaboration, and it grants no native acceptance.
- Ordinary open inputs are represented and checked, and `sim::run_closed`
  requires a closed artifact. A closed source wrapper is a distinct
  specialization of an open function. It is not an execution of that original
  open artifact.

### Code, tests, proof, preservation and specification review

Code:

- A selected native success certifies only its checked artifact and contract
  under the disclosed boundary.
- The Selected hierarchy root adapter introduces no native primitive and no
  theorem.
- The [source migration](source-text.md#finite-and-sized-programs) and
  [selected-entry commands](#selected-entry-commands) record the grammar
  and CLI replacements for finite and sized programs.

Tests:

| Subject | Regression tests |
| --- | --- |
| Exact product trees and tuple constructors | `tests/source_judgments.rs`, `tests/ordinary_types.rs` |
| Loss and duplication of zero-width owners | `tests/ordinary_types.rs`, `tests/quantum_tuple_unitors.rs` |
| Controlled scalar phase | `tests/operation_parameters.rs` |
| Rejection of ordinary runtime values in static bindings | `tests/static_naturals.rs` |

Proof:

- The [two admitted scoped guarantees](../design/initial-guarantees.md) do not
  by themselves prove source type-tree preservation.
- This chapter does not discharge QS, PR or quantitative RS.
- The source, native and execution proof limits apply to selected execution.

Preservation:

- Three obligations are recorded separately: concrete Meaning evidence, the
  convergence of the emitter and the projection, and the source-preservation
  proofs.

Specification review:

- This chapter records no specification review of these rules.

## History

- The chapter specifies the 0.3.0 target contract under the adopted type
  boundary of [#22](https://github.com/MGYamada/Qleisli/issues/22) and
  [#27](https://github.com/MGYamada/Qleisli/issues/27). The
  [profile limits](#status-and-limits) state the concrete implementation scope.
- The retired [foundation packet](../design/type-foundation.md) records the
  original experiments. Their historical failures are not acceptance results
  of this chapter.
- The single predicate domain removed the historical left-folding behavior
  tracked in [#25](https://github.com/MGYamada/Qleisli/issues/25). That Issue
  records the implementation and the migration evidence.
- The [#35 pattern contract](https://github.com/MGYamada/Qleisli/issues/35)
  requires the rules for elided components of a rest pattern.
- The adopted
  [callable boundary #89](https://github.com/MGYamada/Qleisli/issues/89)
  forbids unrestricted closure capture of live quantum owners.
- General arrows were resumed for 0.3.0-beta under
  [#83](https://github.com/MGYamada/Qleisli/issues/83).
- The direct-group distinction is recorded in the
  [ordinary #32 clarification](https://github.com/MGYamada/Qleisli/issues/32#issuecomment-6005081767).
- The catalogue of future implicit coherence and inference conveniences is in
  [#197](https://github.com/MGYamada/Qleisli/issues/197).
- The bounded checks of the typed routes and of the coherent selection
  components do not complete
  [#64](https://github.com/MGYamada/Qleisli/issues/64) or
  [#195](https://github.com/MGYamada/Qleisli/issues/195).
- The `sized` command prefix and the `qleisli::frontend::sized` Rust module
  were removed in 0.3.0-alpha. An earlier text of this chapter dated the Rust
  removal to 0.3.0-beta; the changelog records both under 0.3.0-alpha. The
  removal kept the methods, the preparation limits, the exact provider and
  Meaning checks and the native acceptance requirements.
- Historical validation commands describe their original revisions. They are
  not CLI instructions for this edition.

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
