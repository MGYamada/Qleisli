# Primitive boundary and admission

A **language primitive** is an operation that the language supplies under a
bare spelling, such as `h` or `measure_z`. Edition 2026 has 13 language
primitives. Each one has a typed identity that fixes its typing rule and its
effect. A language primitive grants no native acceptance and no general
inverse or control capability.

This chapter specifies the source primitive boundary of edition 2026. It
covers the lookup of a bare spelling, the contract of each primitive and the
migration of the 27 retired qualified names. It also covers the ordinary
library, the roles of each production path, and **primitive admission**: the
reviewed decision to add semantic authority.

The chapter is subordinate to the [authority hierarchy](authority.md),
`TRUSTBOUNDARY.md` and `STDLIB.md`. Its inventory is a technical
classification. It is neither a human adoption of a minimal generating set
nor a constitutional interpretation or guarantee. Source access by bare
spelling and by ordinary definitions changes neither the meaning of the
[Raw constructors](#core-forms-and-independent-meaning) nor the native
acceptance authority.

The [project route and the selected-entry route](diagnostics.md#routes) both
use the common checker. A rule in this chapter names the class that the common
checker gives to the diagnostic of a program that breaks the rule, such as
`name`. [Codes](diagnostics.md#codes) gives the code that each route reports
for a class.

A **concrete adapter** lowers a checked program to a concrete proposal under
fixed capacities. The **finite adapter** lowers a program to finite Raw IR.
The **selected adapter** is the concrete preparation of a selected entry for
the ordinary Raw gate or a dedicated hierarchy gate. The capacities and the
supported forms of an adapter are its **concrete profile**.
[Status and limits](#status-and-limits) gives both profiles.

## Meaning, spelling and implementation

The project separates four categories of meaning. Each category has its own
authority and its own obligation.

| Category | Authority and obligation |
| --- | --- |
| **Semantic primitive**, or irreducible semantic rule | An existing operation, instrument, ownership transition or effect rule at the independent semantic and checking boundary. Its intended meaning, its premises and the acceptance that the checker implements require review. Moving the rule into a backend or a package does not remove these duties. |
| Language primitive | One typed `PrimitiveId`. Its bare spelling is available only when lexical resolution and the resolution of ordinary declarations and imports leave that spelling unbound. The identity fixes the typing rule and the effect. It grants no native acceptance and no general inverse or control capability. |
| **Derived library definition** | Inspectable ordinary `.qli` source that the checker checks like user source, with a separately reviewed contract. Its home under `std::` grants no privilege. |
| **Backend implementation intrinsic** | An implementation of an existing meaning. The target output, phase, axes, workspace and resources keep their separate preservation and realization obligations. An internal operation tag is not an additional source primitive. |

Rules:

- Only native Lean checking issues a production accepted handle. Parsing, Rust
  catalogs, lowering, simulation and exporter output issue none.
- An intended mathematical specification must stay independent of
  acceptance. It requires specification review.
- A technical inventory, a refreshed source hash or a successful test is not
  primitive admission, proof of irreducibility or source preservation.

## Bare lookup and ordinary shadowing

A **bare spelling** is an unqualified callable name. An **ordinary
declaration** is a declaration in `.qli` source, which receives the same checks
as user source. The checker resolves a bare spelling to the first of these
that applies:

1. A lexical runtime or static binding. This includes a moved binding and a
   binding of the wrong callable category.
2. An ordinary declaration of the same module, or an explicitly imported
   ordinary public declaration, under the ordinary visibility and collision
   rules.
3. One of the six original public declarations that the
   [derived prelude](prelude.md) supplies, unless the module opts out.
4. The language primitive with that spelling.

Rules:

- Resolution is lexical. It is not overload selection by argument type.
- A lexical binding determines the use. Its ownership or category error is
  final. Lookup never retries a declaration or a primitive of the same name.
- An ordinary declaration determines the use even when its spelling matches a
  primitive. Its signature, public effect, access requirements and body
  obligations apply.
- A spelling resolves to a primitive only when steps 1 to 3 leave it unbound.
  A name that no step binds is an error (`name`).
- A failed type, arity, effect, capability, concrete-profile or native check
  never selects another callee or another authority.
- Parameters, `let` bindings, fold binders, static providers and restricted
  classical or basis expressions keep their category and scope rules.
- A primitive is not an import, a prelude declaration, a reserved identifier
  or a hidden alias. A program calls `h(q)` or `global_phase_eighth(q)`
  without a `use`.
- An ordinary function may have the name `h`. It receives ordinary source
  checking, and its name grants no Hadamard meaning. A moved local `h` shadows
  both that function and the primitive.
- The prelude must not reexport a bare primitive spelling (`name`).
- Ordinary gates and the state and structure definitions use ordinary
  declarations, imports or qualified references. Six common derived
  definitions are also in the prelude.
- The bare name `phase_eighth` is not an alias of `global_phase_eighth`. It is
  an unresolved name (`name`).
- A retired qualified path is never a lookup path.
  [Retired qualified names](#retired-qualified-names) gives its rules.

The checker accepts this program. The ordinary declaration `empty_bits`
determines the use, so the basis body yields the label 1 and not the empty
label:

```qli
classical fn empty_bits() -> Bit { 1 }
pub isometry fn f(q: Q<Unit>) -> Q<Bit> { basis q as () { empty_bits() } }
```

The checker rejects this program (`type`). The local `x` determines the use,
and the checker does not retry the `x` of the prelude:

```qli
observe fn main() -> Bit { let x = 0; measure_z(x(init0())) }
```

The checker accepts this program. A module that opts out of the prelude keeps
the bare primitives `measure_z`, `h` and `unit`:

```qli
#![no_implicit_prelude]
observe fn main() -> Bit { measure_z(h(basis unit(()) as _ { 0 })) }
```

The checker rejects this program (`name`). After the opt-out, no step binds
`init0`:

```qli
#![no_implicit_prelude]
observe fn main() -> Bit { measure_z(init0()) }
```

`tests/frontend_types.rs`, `tests/selected_coherent_basis.rs` and
`tests/shared_resolution/prelude.rs` check these sources.

> **Implementation note.** `src/frontend/resolve/locals.rs` resolves a lexical
> binding before any global name. `Resolution::lookup` in
> `src/frontend/resolve.rs` applies steps 2 to 4, and
> `PrimitiveId::lookup_unbound` supplies step 4.

## Primitive inventory

The table lists the 13 language primitives. Static arguments stand in square
brackets after the spelling, as in `phase[1,2]`. `A` and `B` stand for
complete supported Basis trees, not for bit counts. The effect is the
principal effect of a call.

| Spelling | Identity | Static arguments | Runtime arguments | Signature | Effect | Typing |
| --- | --- | --- | --- | --- | --- | --- |
| [`h`](#h) | `H` | None | 1 | `Q<Bit> -> Q<Bit>` | Unitary | Fixed |
| [`phase`](#phase) | `Phase` | `[j,k]` | 1 | `Q<Bit> -> Q<Bit>` | Unitary | Fixed |
| [`global_phase_eighth`](#global_phase_eighth) | `GlobalPhaseEighth` | None | 1 | `Q<A> -> Q<A>` | Unitary | Inferred from the argument |
| [`unit`](#unit-and-finish) | `Unit` | None | 1 | `Unit -> Q<Unit>` | Unitary | Fixed |
| [`finish`](#unit-and-finish) | `Finish` | None | 1 | `Q<Unit> -> Unit` | Unitary | Fixed |
| [`split`](#split-and-join) | `Split` | None | 1 | `Q<(A,B)> -> (Q<A>,Q<B>)` | Unitary | Inferred from the argument |
| [`join`](#split-and-join) | `Join` | None | 2 | `(Q<A>,Q<B>) -> Q<(A,B)>` | Unitary | Inferred from the arguments |
| [`measure_z`](#measure_z) | `MeasureZ` | None | 1 | `Q<Bit> -> Bit` | Observe | Fixed |
| [`discard`](#discard) | `Discard` | None | 1 | `Q<A> -> Unit` | Observe | Inferred from the argument |
| [`take_bit`](#take_bit-and-put_bit) | `TakeBit` | `[n,k]` | 1 | `Q<Bits<n>> -> (Q<Bit>,Q<Bits<n-1>>)` | Unitary | Fixed, with `k<n` |
| [`put_bit`](#take_bit-and-put_bit) | `PutBit` | `[n,k]` | 2 | `(Q<Bit>,Q<Bits<n-1>>) -> Q<Bits<n>>` | Unitary | Fixed, with `k<n` |
| [`empty_bits`](#empty_bits-and-prepend_bit) | `EmptyBits` | None | 0 | `() -> Bits<0>` | Unitary | Fixed |
| [`prepend_bit`](#empty_bits-and-prepend_bit) | `PrependBit` | `[n]` | 2 | `(Bit,Bits<n>) -> Bits<n+1>` | Unitary | Fixed |

A primitive with fixed typing has the signature of the table for its static
arguments. A primitive with inferred typing takes its result type from the
type of its arguments.

Rules:

- A call must supply the static arguments of the table (`static-arity`) and
  the number of runtime arguments of the table (`arity`).
- The runtime argument list and the tuple shape of the result are separate.
  `join(a,b)` takes two arguments, and `unit(())` takes one.
- Each quantum argument evaluates once, in source order. The call consumes its
  owner. The primitive returns or eliminates that owner explicitly.
- Every quantum equation of this section extends with the identity on an
  arbitrary retained reference.
- Distinct owners may be entangled. A zero-axis owner is linear.
- A concrete adapter may refuse an identity that it does not support
  (`unsupported`). The refusal does not restore qualified lookup, and it does
  not replace the source judgment.

`tests/review_v021.rs` checks each of these declarations as an accepted
project of its own:

```qli
unitary fn f(q:Q<Bit>)->Q<Bit>{h(q)}
unitary fn f(q:Q<Bit>)->Q<Bit>{phase[1,2](q)}
unitary fn f(q:Q<(Bit,Unit)>)->Q<(Bit,Unit)>{global_phase_eighth(q)}
unitary fn f(v:Unit)->Q<Unit>{unit(v)}
unitary fn f(q:Q<Unit>)->Unit{finish(q)}
unitary fn f(q:Q<(Bit,Unit)>)->(Q<Bit>,Q<Unit>){split(q)}
unitary fn f(a:Q<Bit>,b:Q<Unit>)->Q<(Bit,Unit)>{join(a,b)}
observe fn f(q:Q<Bit>)->Bit{measure_z(q)}
observe fn f(q:Q<(Bit,Unit)>)->Unit{discard(q)}
unitary fn f(q:Q<Bits<1>>)->(Q<Bit>,Q<Bits<0>>){take_bit[1,0](q)}
unitary fn f(a:Q<Bit>,z:Q<Bits<0>>)->Q<Bits<1>>{put_bit[1,0](a,z)}
unitary fn f()->Bits<0>{empty_bits()}
unitary fn f(b:Bit,z:Bits<0>)->Bits<1>{prepend_bit[0](b,z)}
```

> **Implementation note.** `src/frontend/primitive.rs::PrimitiveId` and its
> `ALL` list hold the 13 identities. `src/frontend/check/primitive.rs` types
> them for the common checker. The finite and selected adapters consume the
> same identity. They do not classify a name by its string. Internal tags of
> the adapters, such as X, Cnot, Init0 and Empty, are transport and emitter
> vocabulary and have no language identity.

### `h`

`h` applies the Hadamard gate to one Bit owner:
`H|b>=(|0>+(-1)^b|1>)/sqrt(2)`. The result is on the same axis.

Rules:

- The argument must have type `Q<Bit>` (`type`).
- `h` keeps the amplitude-mixing action as a primitive rule. A deterministic
  basis map alone cannot express that superposition.

### `phase`

`phase[j,k]` applies `diag(1,exp(2*pi*i*j/2^k))` to one Bit owner. The static
arguments `j` and `k` are exact dyadic arguments.

Rules:

- The argument must have type `Q<Bit>` (`type`).
- The static arguments must pass the coefficient and profile checks of the
  concrete adapter. [Status and limits](#status-and-limits) gives them.
- `phase` is a relative phase on a Bit. It is distinct from a scalar.

### `global_phase_eighth`

Let `ζ = exp(i*pi/4)`. `global_phase_eighth` multiplies the state of one owner
by the scalar ζ. Its action is `ζ I_A`.

Rules:

- The argument must be one quantum owner of type `Q<A>` (`type`). The basis
  `A` may be `Unit`, `Bits<0>` or a complete packaged tree.
- `global_phase_eighth` keeps an explicit scalar phase that has no physical
  wire.

The checker rejects each of these declarations (`type`). An ordinary `Bit` is
not a quantum owner, and a tuple of two owners is not one owner:

```qli
pub unitary fn f(b: Bit) -> Bit { global_phase_eighth(b) }
pub unitary fn f(q: Q<Unit>,r: Q<Bit>) -> (Q<Unit>,Q<Bit>) { global_phase_eighth((q,r)) }
```

`tests/quantum_unit_source.rs` checks these sources.

### `unit` and `finish`

`unit` introduces a fresh zero-axis owner with coefficient +1. `finish`
consumes a zero-axis owner with coefficient +1.

Rules:

- The argument of `unit` must have the ordinary type `Unit` (`type`). The call
  `unit(())` is unary: its one argument is the value `()`.
- The introduction of an owner is an explicit semantic transition. It is not
  the classical value `()`, and it is not an implicit preparation.
- The argument of `finish` must have type `Q<Unit>` (`type`). `finish`
  consumes exactly that owner and keeps all preceding scalar work.
- `finish` performs no observation. It infers no clean state for another
  basis.

### `split` and `join`

`split` partitions one product owner into two owners. `join` combines two
owners into one ordered product owner. Both have coefficient +1.

Rules:

- The argument of `split` must have type `Q<(A,B)>`, a product of two fields
  (`type`).
- `split` keeps the complete child trees and the left and right axes. It does
  not flatten implicitly, and it promises no separability.
- Each argument of `join` must be a quantum owner (`type`). The two owners
  must be distinct: a second use of one owner is an error (`ownership`).
- `join(a,b)` is a call with two arguments. It is not a call with one tuple
  argument, and it is not a physical SWAP.

The checker rejects this declaration (`ownership`). `join` receives the owner
`q` twice:

```qli
pub unitary fn f(q:Q<Unit>)->Q<(Unit,Unit)>{join(q,q)}
```

`tests/quantum_tuple_unitors.rs` checks this source.

### `measure_z`

`measure_z` is the complete destructive Z instrument with the Kraus operators
`K_b=<b|`. It includes every unnormalized reference branch.

Rules:

- The argument must have type `Q<Bit>` (`type`).
- `measure_z` consumes the logical owner.
- A pure label cannot represent the observation. A function that calls
  `measure_z` under a `unitary` or `isometry` label is an error (`effect`).

The checker rejects this declaration (`effect`):

```qli
unitary fn f(q:Q<Bit>)->Bit{measure_z(q)}
```

`tests/body_effects.rs` checks this source.

### `discard`

`discard` takes the explicit partial trace of one complete subsystem. It keeps
the marginal of the reference and every erasure history.

Rules:

- The argument must be one quantum owner of type `Q<A>` (`type`).
- `discard` is not a clean release, not a proof of a zero state and not an
  implicit destruction at scope exit.

### `take_bit` and `put_bit`

`take_bit[n,k]` extracts coordinate `k` of a `Bits<n>` register and keeps the
order of the other coordinates. `put_bit[n,k]` inserts its first argument at
coordinate `k` and keeps the other coordinates. Both have phase +1. They are
the explicit routing and typing rules of an atomic register.

Rules:

- The static arguments must satisfy `k<n` (`size`).
- The argument of `take_bit` must have type `Q<Bits<n>>` (`type`). A
  zero-width remainder, as for `take_bit[1,0]`, is an owner.
- The arguments of `put_bit` must be two distinct owners of types `Q<Bit>` and
  `Q<Bits<n-1>>` (`type`).
- `put_bit` is not a physical SWAP and not a coercion by width alone.

### `empty_bits` and `prepend_bit`

`empty_bits()` returns the exact ordinary empty label of type `Bits<0>`. The
label is copyable and has no owner. `prepend_bit[n]` builds an ordinary label
with the head before the tail. It has no quantum action.

Rules:

- `empty_bits` takes no runtime argument. The call `empty_bits(())` is an
  error (`arity`).
- In a restricted basis or classical expression, only the resolved identity
  `EmptyBits` receives the constructor rule. An ordinary function of the same
  name does not gain it.
- The arguments of `prepend_bit[n]` must have the ordinary types `Bit` and
  `Bits<n>` (`type`).
- `prepend_bit` keeps the type rule of a sized label. It is not a preparation
  and not a measurement.

### Effects and types

The effect and the types of a primitive call follow these rules.

Rules:

- `Unitary` classifies the quantum action at fixed ordinary inputs. It does
  not make ordinary copying or dropping a reversible classical computation.
- `Bit`, `Bits<1>`, `Unit`, `Bits<0>`, nested and flat tuple trees, and
  products of separate owners are distinct types.
- Effect inference checks a body independently of its public annotation.
  External callers, specialization and provider selection use the public
  effect.
- A `Unitary` or `Isometry` label must not conceal observation, reset or
  discard (`effect`).
- Unitarity alone grants neither inverse nor control access.

### Derivation and removal

These rules constrain a later derivation of a primitive rule in ordinary
source, and its removal.

Rules:

- A further derivation or a removal of a primitive rule must first express the
  whole recorded interface in ordinary checked source.
- It must also provide the applicable independent correspondence of phase,
  type, reference, owner and effect, cleanup and resources.
- A gate identity that holds only up to phase, or a match of widths, is
  insufficient.
- The [admission process](#admission-and-replacement-process) applies to an
  addition of authority.

## Retired qualified names

A **retired name** is one of the 27 qualified entries of the four retired
compiler namespaces `std::quantum`, `std::observe`, `std::registers` and
`std::classical`. The table accounts for every one of them.

| Retired name | Source access | Derivation or retained semantic rule |
| --- | --- | --- |
| `std::quantum::h` | bare `h` | The Hadamard action and its exact amplitude rule. |
| `std::quantum::phase` | bare `phase` | The exact dyadic relative-phase rule. |
| `std::quantum::phase_eighth` | bare `global_phase_eighth` | The full scalar `ζ I`, named explicitly to distinguish it from T. |
| `std::quantum::unit` | bare `unit` | Explicit introduction of a zero-axis Unit owner. |
| `std::quantum::finish` | bare `finish` | Explicit elimination of a Unit owner, with the phase retained. |
| `std::quantum::split` | bare `split` | Explicit ordered binary partition of an owner. |
| `std::quantum::join` | bare `join` | Explicit ordered combination of owners. |
| `std::quantum::init0` | ordinary `std::state::init0` | `basis unit(()) as _ { 0 }`: the injective singleton-to-Bit rule with table `[0]` and coefficient +1. Isometry; one fresh physical wire. |
| `std::quantum::x` | ordinary `std::gate::x` | `h(z(h(q)))`, the exact X including coefficient +1. |
| `std::quantum::z` | ordinary `std::gate::z` | `phase[1,1]`, the exact `diag(1,-1)`. |
| `std::quantum::t` | ordinary `std::gate::t` | Coherent control of `global_phase_eighth` on an explicit Unit owner, then `finish`. The exact `diag(1,ζ)`, with no auxiliary physical wire. |
| `std::quantum::s` | ordinary `std::gate::s` | `phase[1,2]`, the exact `diag(1,i)`. Readability does not require a power of T. |
| `std::quantum::sdg` | ordinary `std::gate::sdg` | `adjoint(s)`, the exact `diag(1,-i)`. |
| `std::quantum::tdg` | ordinary `std::gate::tdg` | `adjoint(t)`, the exact `diag(1,ζ^-1)`. |
| `std::quantum::id` | ordinary `std::gate::id[type(A)]` | Returns the same owner with coefficient +1. The explicit Basis argument preserves the complete tree. |
| `std::quantum::cnot` | ordinary `std::gate::cnot` | Ordinary coherent control of X, control first and target second. Both owners return in order. |
| `std::quantum::toffoli` | ordinary `std::gate::toffoli` | Ordinary control of the packed CNOT. Three distinct owners and the original nested result tree. |
| `std::quantum::controlled_phase` | ordinary `std::gate::controlled_phase[j,k]` | Ordinary control of the phase provider, in the exact order of control and target, under the same coefficient and profile premises. |
| `std::observe::measure_z` | bare `measure_z` | The complete destructive measurement rule. |
| `std::observe::discard` | bare `discard` | The explicit subsystem erasure rule. |
| `std::observe::reset` | ordinary `std::state::reset` | `discard(q); init0()`, Observe. Returns a fresh zero owner. The erased input is not cleanly uncomputed. |
| `std::registers::take_bit` | bare `take_bit` | The typed extraction rule of an atomic register. |
| `std::registers::put_bit` | bare `put_bit` | The typed insertion rule of an atomic register. |
| `std::registers::empty` | ordinary `std::structure::empty` | `basis unit(()) as _ { empty_bits() }`: the explicit singleton representation from Unit to Bits<0>, with phase +1 and one zero-axis owner. |
| `std::registers::consume_empty` | ordinary `std::structure::consume_empty` | `finish(basis q as _ { () })`: the exact singleton representation from Bits<0> to Unit, followed by explicit elimination of the owner. |
| `std::classical::empty_bits` | bare `empty_bits` | The ordinary constructor of the empty label. |
| `std::classical::prepend_bit` | bare `prepend_bit` | The ordinary sized constructor of head and tail. |

Rules:

- A retired name is not a callable alias. The four retired namespaces have no
  callable entry and no compatibility alias. The table preserves the migration
  and nothing else.
- An import of a retired name is an error with migration guidance. The project
  route reports the code `project`, and the selected-entry route reports
  `name`.
- A qualified call of a retired name is an error with the same guidance. The
  project route reports `unknown_name`, and the selected-entry route reports
  `name`.
- Migration guidance is never a lookup path.
- A derived replacement has its ordinary public interface and its declared
  static arguments. Replacing an import is not a fallback to the same name.
- The channel of `std::state::reset` is
  `rho_AR -> |0><0|_A tensor Tr_A(rho_AR)`, with a fresh output owner. This
  formula includes arbitrary reference correlations.
- The conversions between Unit and Bits<0> in the table are explicit source
  maps. They are never a definitional type equality or an inserted coercion.
- A scalar phase accumulated before such a conversion stays in the
  composition.
- A pure structural elimination does not invoke `discard`.

The checker rejects this declaration (`name`). The guidance names the bare
primitive `empty_bits`:

```qli
pub unitary fn f(q:Q<Unit>)->Q<Bits<0>>{basis q as () {std::classical::empty_bits()}}
```

The checker rejects this program. The derived `id` requires its static
argument, as in `id[type(Bit)]`, and the selected-entry route reports
`static`:

```qli
observe fn main() -> Bit { measure_z(id(init0())) }
```

`tests/frontend_types.rs` and `tests/shared_resolution/prelude.rs` check
these sources. `tests/common_authoring_diagnostics.rs` checks the codes of
both routes for a retired name.

> **Implementation note.** `retired_name_hint` in `src/frontend/primitive.rs`
> holds the guidance for the 27 names. The resolver in
> `src/frontend/resolve.rs` rejects such an import or qualified call before it
> looks up the module.

## Source retention and resources

These rules state what a call retains from its source and what a resource
claim requires.

Rules:

- An ordinary call retains its original definition, its caller instance, its
  static arguments, its public effect and its complete source and dependency
  identity.
- A checked Meaning override retains the exact original Raw witness, the
  checked leaf, the matrix, both ports and the reference receipts. An endpoint
  of the same width or a digest alone is not source correspondence.
- An original zero-repeat child keeps its checking obligations. A dormant
  repeat-zero witness is not an equation between an arbitrary hierarchy and a
  finite implementation.
- The ordinary preparation `std::state::init0` uses the Raw `LiftBasis`
  0-to-1 table `[0]`. A finite target export must inspect that table and the
  mapping of the fresh wire and owner. It must not replace an arbitrary
  rectangular map by an initialization.
- A structural singleton map retains its complete Unit or Bits<0> tree and
  its original root under composition, repeat, control and adjoint, wherever
  the concrete profile supports them. Explicit cleanup and the rejected
  observation, phase and width cases are part of that profile.
- Source recognition alone enables none of these emitters.
- Semantic ownership, clean and dirty scratch, and target workspace are
  separate.
- The Unit owner in the definition of `std::gate::t` has zero physical wires.
  It promises no zero target T cost.
- The three ordinary CNOT calls of `std::gate::swap` differ from the
  structural output routing of `permute_axes`, even when a fixed-coordinate
  matrix agrees.
- A representation sharing count, a logical instruction count or a
  checker-work budget is not quantitative Resource Safety.
- Every target or resource claim needs its own artifact, model, units and
  evidence.
- Exact cleanup must hold for every permitted input and reference.
  Approximation never excuses dirty scratch.

## Core forms and independent meaning

A **Raw constructor** is one variant of the public Rust type `RawOp` in
`src/ir.rs`. `RawOp` has 22 constructors.

| Family | Constructors |
| --- | --- |
| Preparation and fixed gates | `Init0`, `Gate`, `Cnot`, `Toffoli` |
| Explicit ownership packaging | `PackUnit`, `UnpackUnit`, `Split`, `Join` |
| Finite action and basis isometry | `ApplyUnitary`, `LiftBasis` |
| Coherent selection | `QuantumIf` |
| Checked computed/cleanup scopes | `CertifiedCompute`, `ComputeUseUncompute`, `StructuralCompute` |
| Observation | `MeasureZ`, `Reset`, `Discard` |
| Classical values and branching | `ClassicalConst`, `ClassicalNot`, `ClassicalXor`, `ClassicalAnd`, `ClassicalBranch` |

Rules:

- A Raw constructor is untrusted data. It is not an accepted handle, and the
  22 constructors are not 22 library functions.
- The table is not the entire semantic vocabulary. `SingleGate`,
  `CircuitAction`, protected operations and hierarchy constructors have their
  own explicit inventories and obligations.
- An added Raw constructor must pass admission. Calling it an implementation
  detail does not bypass admission.
- A source alias does not imply a Raw constructor.
- `RawOp` has no free-standing `Release0`. Clean removal is part of the
  explicitly checked scope.
- A reference definition requires human specification review.
- Lean proves stated relationships to the reference definitions. It does not
  decide that a chosen formula is the intended gate, instrument or resource
  model.

The meaning of the core forms comes from these layers:

| Layer | Source and scope |
| --- | --- |
| Data and interfaces | `src/ir.rs`; `lean-kernel/QleisliKernel/Semantics/{Raw,Observation,Finite}.lean`. These expose the original operations, ports, finite actions and effects. Data construction is untrusted. |
| Pure reference meaning | `lean/Qleisli/Semantics/Finite.lean` supplies literal gate amplitudes, controlled and monomial actions, and encoded equations. `Semantics/Raw.lean` retains the original events, ordered axes, full complex composition and clean-scope meanings. These references do not define meaning as successful checking. |
| Instrument reference meaning | `lean/Qleisli/Semantics/RawInstrument.lean` retains all erasure outcomes, classical values, hidden histories and unnormalized operators. Reset is erasure followed by fresh-zero preparation. The reference does not select only a successful sampled branch. |
| Hierarchy operator specification | `lean/Qleisli/HierarchicalOperators.lean` specifies positive dyadic phase, ordered wiring, control and composition. This specification is separate from a complete theorem from production hierarchy acceptance to an operator. |
| Executable acceptance | `lean-kernel/QleisliKernel/Raw/{Structure,Pure,Observation}.lean`, the finite and QIRF checks and the dedicated hierarchy checks validate the IR fields, the owners and effects, and the enabled evidence. The source catalog is not their authority. |
| Production composition and proof limits | `Protocol.Validity`, `Protocol.NativeContract` and their bridges `Qleisli.NativeValidity` and `Qleisli.NativeContract` keep their precise artifact and request scopes. Dedicated hierarchy components have separate bridges. The [production boundary](production-boundary.md) records their exact coverage. |

## Ordinary library and module resolution

The **bundled library** is the set of eight ordinary source modules that the
compiler embeds under `std::`. It has 26 public definitions, six transparent
prelude reexports and five private helpers. The helpers serve reflection,
scalar phase, parameterized phase, packed CNOT and fixed Bit identity.

| Module and source | Public definitions | Contract provenance |
| --- | --- | --- |
| `std::basis`, `stdlib/src/basis.qli` | `xor2`, `and2` | Total finite ordinary maps of basis labels. Neither is injective over its two-input domain. A coherent enclosing construction must meet its own obligations. |
| `std::transform`, `stdlib/src/transform.qli` | `hadamard2`, `qft2`, `qft3` | Ordered H tensor H. Positive finite Fourier phase, first leaf least significant, output reversal included, no auxiliary and no promise about the input state. The Fourier interfaces have fixed width. |
| `std::reflection`, `stdlib/src/reflection.qli` | `reflect_uniform2` | Phase-fixed reflection about the uniform state, with exact cleanup of the computed auxiliary. The private `nonzero2` is a normal basis helper. Hadamard comes from ordinary transform source. |
| `std::gate`, `stdlib/src/gate.qli` | `id`, `t`, `s`, `sdg`, `tdg`, `z`, `x`, `controlled_phase`, `cnot`, `toffoli`, `swap` | Ordinary phase-fixed gates. T controls a scalar phase on a zero-width Unit owner. The phase, Pauli and controlled gates derive through ordinary providers. The Bit SWAP uses three CNOTs. No library definition grants primitive authority or a target-cost guarantee. |
| `std::state`, `stdlib/src/state.qli` | `init0`, `reset` | Ordinary explicit singleton-to-Bit preparation, and observing discard followed by preparation. The original owner, the phase and the complete reference instrument are retained. |
| `std::structure`, `stdlib/src/structure.qli` | `permute_axes`, `transpose_axes`, `empty`, `consume_empty` | The structural two-axis map `[1,0]` and statically indexed register transpositions, with exact phase +1 and no physical gate instructions. Explicit introduction and elimination of a zero-width Bits owner use singleton basis maps. |
| `std::measurement`, `stdlib/src/measurement.qli` | `measure_x`, `measure_z2`, `parity_zz` | Complete destructive X and Z instruments and a nondestructive data-parity measurement, with their original owner and result trees and their reference behavior. |
| `std::prelude`, `stdlib/src/prelude.qli` | Reexports `id`, `x`, `z`, `t`, `cnot`, `init0` | The original ordinary declarations. The reexports add no body, primitive, effect or evidence authority. |

`reflect_uniform2` is the reflection `2|s><s| - I`, where `|s>` is the uniform
state of two Bits. The [semantic namespace Reference](stdlib.md) gives the
admission rule, the exact public interfaces and the migration mapping of every
mathematical module.

A **loader** collects the source modules of a program. The **finite loader**
loads a project from its source root. The **selected loader** loads explicitly
supplied modules.

Rules:

- A bundled module receives the common declaration, type, owner, access,
  dependency and effect checks. It has no compiler-import exception.
- Concrete materialization and native checking occur under the scope of the
  consumer. Selected source checking alone does not natively certify every
  bundled specialization.
- A local module must not have the name `std` or a name that begins with
  `std::`. Both loaders reserve those names for the bundled library.
- `ModuleOrigin::Bundled` gives no ambient source replacement and no checking
  exemption.
- An unknown path is an error.
- The resolver registers complete interfaces. It resolves an explicit import
  with the ordinary visibility and collision rules.
- A cycle that consists of imports alone is allowed.
- A self-import is an error. It collides with the declaration of the same
  module (`name`).
- A mutual dependency through a body, a provider, a Basis or a Meaning is an
  error (`cycle`). Only a checked decreasing runtime self-call is permitted.
- A private declaration is available to lookup in its own module. An import
  from another module and a host entry require a public declaration.
- An import spelling supplies no runtime initialization and no evidence.
- The [prelude contract](prelude.md) admits transparent public reexports. It
  admits no `as`, glob or relative import.
- Resolution, original source identity, concrete materialization and
  independent acceptance are separate duties.
- `std::routines` and `std::transforms` are retired without aliases.
- The three fixed arithmetic definitions A001–A003 are ordinary local source
  in `examples/order_finding/arithmetic.qli`. They preserve amplitude +1,
  modular overflow, the addend and the full-space value-15 extension. They
  have no canonical std export.
- `std::arithmetic` is reserved for parameterized arithmetic and number
  theory. A reserved family name promises no callable API.
- The English source contracts and `STDLIB.md` state intended meanings and
  conventions. Their presence alone does not prove implementation conformance.
- Until version 0.5.0, an algorithm addition ordinarily belongs in the
  approved corpus, not in an expansion of stdlib. This chapter adopts no
  library algorithm.

The project route reports every import that fails to resolve with the code
`project`. The selected-entry route reports the class that the rule names.

> **Implementation note.** `src/frontend/source.rs::BundledRegistry` embeds
> the eight sources and their fixed manifest. Both loaders retain the complete
> original sources, their provenance and their original ASTs. Each loader
> checks the bundled bytes under its own byte policy before it parses or
> copies them.

## Generic acceptance and library-owned algorithms

A **role** is a responsibility of a production path. Each path below has five
roles: producer, independent acceptance, specification and proof, execution or
emission, and compatibility. A role is not a claim that every required proof
exists. The
[production boundary](production-boundary.md#entrypoints-and-actual-checked-representations)
records the predicates, the native modes and the theorem limits of each path.

| Path and source | Producer | Independent acceptance | Specification and proof | Execution or emission | Compatibility responsibility |
| --- | --- | --- | --- | --- | --- |
| Project and qrate source: `frontend::project`, `frontend::check`, `frontend::compile` | Loads original sources and produces typed and lowered proposals. | Fresh ordinary native checking of every materialized concrete ordinary function root and of its retained obligations. | Reviewed source rules and library meanings. Source preservation is a separate obligation. | Simulates or exports the privately retained accepted artifact. | Preserve source selection, diagnostics, unused declarations and complete interfaces through explicit versioned changes. |
| Explicit module-map source: `frontend::compile::ParsedProgram`, internal `frontend::specialize` | Closes explicit bindings, retains original source identities and selects a concrete profile before checking. The Fourier and QPE recognizers discover candidates only. | Ordinary Raw checking, or the required dedicated hierarchy or request gate. A failed check cannot select another route. | Source-step comparisons and finite contract lemmas, each within its bounded scope. | Runs the checked selected root. `emit-proposal` emits untrusted data. | Retain the module, entry and binding identity and the supported finite and hierarchical contracts. The retired public sized namespace is not restored. |
| Flat Raw IR and QIRF: `ir::RawProgram`, `interchange::{native,codec}` | Constructs original operations, evidence DAGs and versioned bytes. | `Kernel` checks the submitted root and dependencies and, for execution, the complete retained QLV3/QDV1 view. | Independent Raw and Observation meanings and the ordinary native bridge theorems. | Consumes the exact checked graph. Output validity alone is not translation preservation. | Retain the published flat IR and the QIRF profiles `finite-v0` and `finite-meaning-v1`, or publish an explicit versioned mapping before changing them. |
| Finite contracts and leaves: `contract`, `finite_leaf`, `pure_leaf` | Constructs independent requested equations and untrusted implementation candidates. | The native contract gate binds the original bodies, complete interfaces, encodings and exact equations. | Library and operator equations and arbitrary-reference lemmas, under their stated premises. | A private checked contract is usable only for its retained artifacts and capabilities. | Preserve the distinctions between a square leaf, a rectangular pure leaf, and an encoded or control contract. No substitution by equal width or by effect. |
| Hierarchy inspection: `interchange::hierarchical::Kernel::inspect_native` | Produces the hierarchy and the finite obligations. | `--hierarchy-pending` checks the conditional structure and the required finite leaves. | Structural and finite bridges. The complete analytic operator composition is a separate obligation. | Inspection alone grants no execution. Running requires a fresh comparison of the execution-scope view. | Preserve this distinct request-free scope and its original root and dependency identity. |
| Hierarchy composition request: `check_against_native` | Proposes a graph and a separately supplied composition request. | `--hierarchy-request-pending` checks the root, the leaves and the requested pairs. | Generic composition equations under stated premises. Producer consistency is not source preservation. | Retains and executes the same pair of graph and request. | Preserve the request grammar, the ordered ports and the finite obligations. |
| Hierarchy control request: internal `check_against_native_with_controls`, for selected pure source with `ctrl` calls | Replays the original `ctrl` calls. Proposes the graph, the composition request and, for each call, its node index, ordered basis forest and control roles. | `--hierarchy-control-pending` checks the root, the leaves, the requested pairs and the control obligations in one invocation. It requires an execution view. | `ControlAccess.check_bound` binds the native sector predicate to the executable action of the selected node. Source occurrence replay and the general source and resource correspondence have separate scopes. | Retains and executes the same graph and request with the same control obligations. | No decision records a compatibility responsibility for this path. |
| Hierarchy Fourier request: the Fourier branch of `check_against_native` | Rust and Python factoring proposes the original trace and the Fourier request. | `--hierarchy-fourier-pending` checks the root, the leaves and the Hadamard obligations. | Fourier mathematics belongs to the library and proof role. The specialized bridges stay in the build. | Uses the retained checked graph. It grants no QFT primitive. | Preserve the exact phase, the axes and the profile limits until a reviewed generic replacement exists. |
| Hierarchy instrument: `check_instrument_native` | Proposes preparation, evolution, readout and the request. | `--instrument-pending` checks all stages, leaves and pairs. | Complete instrument and reference specifications and the stated component results. | Retains all permitted branches and the ordered public results. | Preserve observation, initialization, zero-width owners and boundary identity. |
| Named-QPE instrument: `check_qpe_instrument_native` | Discovers the provider, routing and power components and a candidate binding. | `--qpe-instrument-pending` checks the original request, the candidate, all stages and the finite and Hadamard obligations. | The provider, Fourier and QPE semantic theorems are separate from recognition. | Executes the same checked instrument, not a replacement selected by name. | Preserve all original provider, root, dependency, phase and readout bindings. |
| Component protocols: readout, preparation, phase and layout, and their DAGs | Propose bounded component descriptions. | Their dedicated independent component checks. | A component lemma does not certify an enclosing program automatically. | No component success alone constructs a complete program handle. | Retain the version, scope, capacities and caller obligations of each component. |
| Python client and foreign adapters: `python/qleisli`, `interop` | Translate host and foreign inputs and propose IR or target text. | Production imports reach the same native gate. No Python or foreign receipt confers acceptance. | Translation preservation and runtime preservation are distinct proof duties. | Export consumes an accepted input. Target correctness requires its own correspondence. | Preserve public host contracts, supported foreign subsets and explicit refusals of unsupported formats. |
| Python sized producers and oracles: `scripts/compile_sized_corpus.py`, `compile_sized_instrument.py` | Construct proposals and small-system comparison results independently. | No producer or numerical oracle issues production acceptance. | Differential results are tests, not generic checker soundness. | A proposal is usable only after the applicable production gate. | Retain the historical inputs and the comparison role. Do not revive their grammar as a production frontend. |
| Research: `research/semantic-kernel` | Explores symbolic contracts and proof candidates. | Its research DAG result has no production authority. Raw input requires native checking. | Research rules and bounded comparison evidence are explicitly experimental. | No research receipt grants execution, cleanup or device authority. | Keep the independent comparison and its notices and tests. Production migration requires separate review. |
| Executable package: `lean-kernel/` | Decodes untrusted bytes and computes the enabled checks. | Mathlib-free total executable definitions implement production acceptance. | Soundness of the executable definitions themselves is proved separately. The implementation language is not a proof of the pipeline. | Native IO, compilation and runtime assumptions are explicit. | Retain dispatch and profile compatibility, the source policy, the compiled audit and the fixed capacities. |
| Specification and proof package: `lean/` | Formalizes independent meanings and constructs checked proofs. | Does not replace the native executable and issues no host accepted handle. | Mathlib-backed specifications, bridge theorems, semantic transport and proof audits. | No theorem name alone authorizes execution or a target artifact. | Keep the applicable VM-22–VM-29 proofs and the protected guarantee bindings up to date during migration. |
| Engineering comparisons: `engineering_{pure,instrument,pure_tensor,openqasm,openqasm_gate}` | Propose actual and ideal artifacts, closed budgets and, where supported, target bytes. | Separate fresh native inequality checks bind the complete submitted request and the retained view. | Engineering bounds keep their exact metric, domain and reference premises. | A private report confers only its stated engineering claim. | Preserve distinct claim kinds. Epsilon zero cannot grant exact Meaning, control, cleanup, PR or quantitative RS. |

### Required generic-contract bindings

A generic rule must bind all of the following data, independently of QFT, QPE
or any other algorithm name. The list is a contract for the planned migration
to generic rules. It enables no serialized schema and claims no generic
completeness.

1. **Original implementation.** Retain the original artifact bytes, the
   complete operation bodies, the selected root, and the checked dependency
   graph and its order. Bind the called providers, the shared nodes, and the
   zero-count or otherwise unused obligations that the profile requires. A
   stale index, an equal name, a matching digest without correspondence, or a
   native-valid replacement is insufficient.
2. **Complete interfaces.** Retain separate domain and codomain type trees,
   classical result trees, ordered quantum ports, owner identities, wire
   coordinates, and explicit input and output encodings. Unit, Bit, atomic
   Bits and product trees are distinct even at equal width. State and check
   the encoding dimensions, the isometry premises and the entry and exit
   compatibility. Composition matches the complete intermediate contract, not
   only its bit count.
3. **Actual semantic action.** Check the actual gates, the exact coefficients
   and phase, the axis order, the controls, the ownership and effect
   transitions, and the permitted branches. For an instrument, retain every
   unnormalized hidden history and the ordered public projection. State the
   premises on arbitrary inputs and references. Distinct owners are not
   evidence of separability.
4. **Independent expected meaning.** Fix the requested library, operator or
   instrument meaning before candidate search. Retain its original
   definition, its request bytes, its source and specification identity, and
   its dependencies. The match of a recognizer cannot define it, and neither
   can a probability table derived from the implementation. Review the
   intended mathematical meaning separately from the proof of conformance.
5. **Capabilities and workspace.** Bind forward, adjoint and control access
   separately from semantic unitarity. Bind them together with the owners,
   the effects, the clean and dirty workspace, and the exact restoration
   premises. A body that observes, resets or discards cannot obtain a pure
   label by hiding those operations. A resource claim must additionally bind
   its target, cost model, workspace and artifact.
6. **Actual checking execution.** Identify the protocol, schema, profile and
   checker compatibility separately from the edition and the product version.
   Retain the original byte decoding, the requested root, the derived
   obligations and continuous checking states. Compare the complete retained
   host execution representation independently where it crosses the Lean
   boundary. A serialized success flag or an old receipt cannot replace a
   fresh decision.
7. **Consumed or emitted artifact.** Bind a checked conclusion to the
   immutable object that execution or emission consumes. A claim about
   source, runtime or targets requires its own preservation link. Accepting
   both endpoints independently does not prove a correspondence between them.
8. **Declared domain and failure.** State every finite, coefficient and phase
   limit, every depth and work limit, and every interface limit. A
   generalization of the phase domain requires its own specification, proof
   and profile migration. Reject unsupported forms, changed contracts and
   exhausted budgets without an authority fallback.

Rules:

- The generic checker may establish a reusable composition or contract rule.
- The Fourier sum, the QPE distribution and other algorithm-specific
  mathematical results belong to the library, specification and proof modules
  that instantiate those rules.
- Adding an algorithm must not require granting its name a trusted semantic
  rule.
- An intended definition must stay independent of acceptance.
- `QleisliKernel.Qft`, `Qpe`, the hierarchy Fourier and QPE checks, and their
  `lean/Qleisli` bridge proofs are implemented, specialized components. The
  role assignment does not move or delete them.
- The supported checks, the exact finite contracts, the VM-22–VM-29 authority
  gates and the existing proof coverage must stay until reviewed replacements
  cover them.

## Admission and replacement process

The adopted interpretations require an explicit review before any addition of
semantic authority. The decision is recorded in an Issue, and this chapter
keeps no second backlog. The account of a proposal must contain all of the
following:

1. **Identify the addition.** Specify whether it changes semantic rules,
   exposes an existing rule under a source name, derives checked source, or
   implements an existing meaning as an intrinsic. List the affected source
   and Core forms, checker predicates, reference definitions and production
   paths.
2. **Justify irreducibility.** Explain why each of these is insufficient:
   ordinary checked source, bounded elaboration, a verified transformation, a
   capability or evidence object, a qrate definition, and target lowering.
   Performance, popularity, backend availability and implementation
   difficulty alone do not qualify.
3. **State the independent contract.** Give the exact whole-input map or the
   complete instrument. Give the type and tuple tree, the encodings, the
   finite domain, the phase, the ordered axes, the owners, the effects, the
   capabilities and the failure behavior. Include arbitrary permitted inputs
   and references. A gate name or a probability table is not the contract.
   State the premises, and do not assume separability.
4. **State workspace and realization obligations.** Distinguish semantic
   data, clean and dirty scratch, and backend workspace. Require exact
   permitted cleanup and reference restoration. State the target and gate
   assumptions and the realization correspondence that PR requires. The
   contract implies no unspecified target schema, no projective quotient and
   no approximate cleanup.
5. **Analyze QS, PR and RS.** Identify the existing binding interpretations
   and ledger scopes, the changed dependencies and assumptions, and the
   acceptance and artifact bindings as implemented. State the quantitative
   measures and the preservation obligations under RS. Ownership checks and
   checker work budgets do not substitute for them.
6. **Provide production evidence.** Check the actual executable definitions,
   the transport and decoding, and the interface and request binding. Add
   bounded independent positive and negative cases, as applicable, for phase,
   axis order, references, wrong effects, duplicate or dropped owners,
   workspace and stale identities. Build and audit the changed proofs, and
   retain the explicit source, runtime and target gaps.
7. **Record the decision and migration.** Follow the authority hierarchy for
   specification review, for any constitutional interpretation beyond the
   adopted ones, and for guarantee admission. An ordinary alias or an
   implementation choice that the existing interpretations cover does not
   require a separate Guardian ruling for each edit. Update the reviewed
   inventories, the compatibility mapping and the applicable proofs before
   enabling the changed boundary. A manifest edit does not grant approval.

Rules:

- Project axioms, unsafe or partial executable definitions, and runtime
  overrides are forbidden.
- A reviewed physical or semantic assumption must be explicit in the
  contract. It is not permission to declare a Lean project axiom, and it is
  not permission to accept an unchecked assertion of a producer.
- A replacement of an implementation, or the exposure of an equivalent
  derived definition, must retain the old intended meaning and the applicable
  guarantees through explicit correspondence.
- A semantic change must not hide under an unchanged name.
- Release compatibility and migration are recorded separately from the
  constitutional edition. Not every primitive edit changes the constitutional
  regime.
- A needed constitutional amendment follows the edition procedure of the
  Constitution.
- Historical artifacts and records are retained. They must not be rewritten
  to match the replacement.

Example: a proposal seals `qft2` solely because a backend executes it faster.
The proposal fails the irreducibility justification, because the ordinary
checked `std::transform::qft2` expresses its phase-fixed finite contract. An
optimization or a target intrinsic can instead propose a realization of that
same meaning and supply the required independent checks.

This example assesses the stated rationale. It does not claim that a
historical proposal was formally rejected, and it does not claim that the
optimization is verified.

### Edition-aware deprecation and replacement

These rules govern the deprecation and the replacement of a primitive within
an edition and across editions.

Rules:

- A proposal must distinguish the retirement of a spelling or an
  implementation from a change of the meaning of the primitive.
- It must record the exact source and Core forms before and after the change,
  the semantic contracts, the profile and API mapping, the release
  compatibility, and the proof and guarantee dependencies.
- An equivalent derived replacement needs checked correspondence for the full
  recorded domain, including phase, references, owners and effects, and
  workspace. A few matching examples are insufficient.
- Each historical primitive set must stay recoverable from its exact Git
  revision and its reviewed inventories, with its original edition, its
  profile and its applicable meaning.
- Old manifests and adoption records must not be rewritten to describe a
  replacement.
- A later edition may deprecate source access under its explicit migration
  policy. It must not erase or weaken an accumulated guarantee for its
  historical scope.
- Within edition 2026, implementation evolution preserves the old intended
  meaning. An incompatible source removal requires the ordinary
  breaking-release process, even when it preserves the safety implication.
- A changed constitutional regime follows the amendment procedure of the
  Constitution.
- Neither an edition increment nor another primitive name waives
  non-weakening.

## Guardrails

These checks detect drift of the inventories of this chapter.

| Check | What it fixes or rejects |
| --- | --- |
| `scripts/check_verification_inventory.py` | Freezes the source identities, including the common and concrete catalogs, and the public constructor families of the Raw, finite and hierarchy forms with their fields. Pins the typed source identity and the concrete adapter sources. Discovers unlisted production checking sources and added checking files. |
| The typed inventory guard of that script | Fixes the `PrimitiveId` members, their `ALL` order, the canonical bare spellings and the unbound-only lookup body. |
| The mutation suite of that script | Rejects an added Raw constructor even when its source digest is refreshed. Its calibration separately exercises typed source growth and an unhandled selected adapter. |
| `scripts/check_production_coverage.py` | Checks the classified public routes and the native dispatch, and binds them independently. |
| The Lean source and dependency policy and `lean-kernel/Audit.lean` | Reject unauthorized project axioms, unsafe executable declarations and forbidden runtime replacement paths. |
| `lean/Audit.lean` | Checks the axiom closure of the proof package. |
| The import policy of the reference modules | Keeps mathematical semantics separate from acceptance and transport. |

Rules:

- A refresh of the metadata of these checks is not primitive admission and
  not proof.
- An added source identity cannot pass by a refreshed file digest or by an
  inserted row of an internal selected emitter.
- The mutation calibration is a drift and coverage check. It is not a
  judgment of irreducibility or admission.
- A change must be reviewed together with the source, the catalog and
  constructor inventory, and the affected acceptance and proof contracts.
  Updated hashes cannot supply human specification review or a constitutional
  judgment.
- These checks and the guarantee-continuity machinery keep their stated
  scopes. They do not mechanically judge specification intent or
  irreducibility, they do not authenticate a human ruling, and they do not
  complete every gate of the admission review.

The regression sources include:

- the source-signature checks of `tests/review_v021.rs`;
- `tests/sized_source.rs::primitive_signatures_agree_through_symbolic_and_concrete_preparation`
  and `concrete_phase_and_repeat_limits_check_zero_and_unused_providers`;
- `tests/project.rs::std_prefix_and_invalid_module_names_cannot_shadow_bundled_modules`,
  the refusal checks of the retired foundation paths,
  `semantic_stdlib_modules_are_bundled_source_with_private_helpers` and
  `import_only_cycles_load_but_call_cycles_and_name_collisions_reject`;
- `tests/semantic_contracts.rs::primitive_evidence_preserves_exact_phase`,
  `unit_has_scalar_phase_and_a_distinct_owned_type` and
  `tensor_proofs_keep_low_order_axes_and_allow_a_correlated_reference`.

## Status and limits

All 13 identities have common source typing. Each concrete profile has its own
capacities. A code in the table is the code that the adapter reports.

| Form | Finite adapter | Selected adapter |
| --- | --- | --- |
| `phase[j,k]` | `k<=8` (`unsupported`) and `j<2^k` (`contract`). The Raw R8 phase lowering also requires an integral eighth-root exponent (`unsupported`). | `k<=8` and `j<2^k` (`limit`), with the symbolic-word profile of dyadic hierarchy preparation. |
| `take_bit[n,k]`, `put_bit[n,k]` | `k<n<=12` (`limit`) | `k<n<=8` (`size`) |
| `prepend_bit[n]` | `n<12` (`limit`). The bound is `n<8` where the finite adapter lowers a selected typed root. | `n<8` (`limit`) |
| `join` | A joined register of at most 12 bits (`limit`) | A joined owner of at most 8 bits (`limit`) |
| `discard` | Supported | Unsupported (`unsupported`) |
| `std::state::reset` | Supported | Unsupported, because its body calls `discard`. A move into std gives a definition no selected support. |

- The finite adapter rejects an unsupported phase coefficient. It never
  rounds.
- The selected adapter refuses instrument initialization after observation
  (`unsupported`).
- The sufficient checks of the selected phase profile are not a complete
  semantic normal form.
- The symbolic phase-word model has modulus 256. Its exact sufficient checks
  are not a complete semantic normal form or a general phase-domain theorem.
- The common checker rejects a `join` whose product basis has more than 4096
  type nodes or more than 64 levels (`limit`).
- Aggregate type, width, depth, work and native limits also apply.
- A refusal of an adapter never retries through a retired route.
- The selected loader reserves all eight bundled module slots and counts
  their bytes toward its aggregate limit. The finite loader has separate
  bounded and explicit legacy byte policies and local limits on filesystem
  discovery.
- Generic QFT completion and the correspondence between fixed and generic
  forms are outside all of v0.3.0 and the current goal. The role assignment
  adds no generic QFT to the 0.3.0 scope and claims no completed independent
  library decomposition.
- The consolidation of the specialized Fourier and QPE components, a generic
  prototype and the migration of the compatibility paths are planned work.
  The common frontend of 0.3.0 and its specified namespace migration are
  separate from that work.

The project separates code, tests, proof, preservation and specification
review:

| Kind | Status |
| --- | --- |
| Code | The common checker types the 13 identities. The finite adapter lowers all 13, and the selected adapter lowers every one except `discard`. Acceptance is solely by the native Lean checker in `lean-kernel/`. |
| Tests | The regression sources of [Guardrails](#guardrails) exercise the inventory. Listing a regression in this chapter does not report a test run. A successful test is not admission. |
| Proof | An ordinary accepted root has the two admitted scoped guarantees `QS-QLV1-OWNERSHIP-2026-01` and `QS-QLV1-SCOPE-2026-01`, for ownership and classical scope. They are protected. The general QS, PR, quantitative RS and EXACT duties are binding and pending. An optional finite request or leaf contract establishes an additional result only within its premises. `PathSum.compile_sound` proves the correspondence of individual path states. Alone it proves neither the complete complex sum nor a Fourier or QPE specification, source preservation, completeness, control or observation integration. No theorem establishes the complete analytic operator composition of a hierarchy. The inventory is not a mathematical proof of global minimality: retaining a rule records the semantic interface that the implementation needs. The audit does not prove that no alternative algebraic derivation of `global_phase_eighth` exists. |
| Preservation | The contracts of the inventory are intended contracts. They do not claim completed general preservation proofs. The bounded engineering source checks of [Source retention and resources](#source-retention-and-resources) claim no general source-preservation theorem. This chapter asserts no general source or runtime, CPTP, clean-release, target-realization or quantitative resource theorem. |
| Specification review | A reference definition and any added sealed semantics require human specification review. No hash, guardrail or test supplies that review. The inventory has no human adoption as a minimal generating set. |

The [authority hierarchy](authority.md) records the adoption and the proof
status of the constitutional obligations.

> **Implementation note.** `src/frontend/compile/lower/` enforces the bounds
> of the finite adapter, and `src/frontend/specialize/elaborate.rs` enforces
> the bounds of the selected adapter.

## History

- Release `0.3.0-beta` is the release that this chapter describes.
- [#369](https://github.com/MGYamada/Qleisli/issues/369) and
  [#167](https://github.com/MGYamada/Qleisli/issues/167) made the cutover from
  the qualified compiler namespaces to bare primitives and ordinary library
  definitions. The cutover changed source access and ordinary definitions. It
  did not change the meaning of the Raw constructors or the native acceptance
  authority.
- [#131](https://github.com/MGYamada/Qleisli/issues/131) is the 0.3.0
  architectural contract that assigns the five roles to each path.
- [#273](https://github.com/MGYamada/Qleisli/issues/273) tracks the migration
  to generic rules: the consolidation of the specialized components, a generic
  prototype and the later migration of the compatibility paths. The required
  generic-contract bindings are the contract for that migration.
- [#154](https://github.com/MGYamada/Qleisli/issues/154) defines the gates of
  the primitive admission review. The guardrails do not complete every gate
  of that Issue.

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
