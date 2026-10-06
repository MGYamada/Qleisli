# Ordinary types, quantum owners and equality

This chapter specifies the **0.3.0 target contract** under the adopted
[#22](https://github.com/MGYamada/Qleisli/issues/22) /
[#27](https://github.com/MGYamada/Qleisli/issues/27) type boundary and the
[authority hierarchy](authority.md). The current alpha frontend uses the
canonical ordinary `Unit`, `Bit`, `Bits<n>` and `0`/`1` spellings described
below. Both paths use one mandatory judgment over every complete original
declaration and body before concrete eligibility, retaining exact type trees,
owners, static premises, access and principal effects. The selected-source path
implements bounded opaque Basis specialization; concrete emitter convergence,
Meaning evidence integration and general source preservation remain in progress. The
[foundation packet](../design/type-foundation.md) preserves the original
experiments; their historical failures are not current acceptance results.

## One finite type universe

The initial ordinary finite types are `Unit`, `Bit`, `Bits<n>` and ordered
tuples of finite types. `n` is a checked static natural. `Basis` is the static
kind of such finite type trees; it is not a second copy of ordinary values.
Finite ADTs join this universe when their own specified constructors and
checking rules are implemented.

`Q<A>` is linear quantum ownership over the finite value space `A`. A basis
argument to `Q` cannot itself contain a quantum owner. Ordinary tuples may mix
ordinary fields and quantum owners, but each quantum-containing field retains
its linear obligations. There is no `C<A>` constructor.

| Type | Value and ownership |
| --- | --- |
| `Unit` | Ordinary singleton, with value `()` |
| `Bit` | Ordinary finite bit, with values `0` and `1` |
| `Bits<n>` | Ordinary sequence of exactly `n` bits, retaining ordered positions |
| `(A,B)` | One ordered product value, retaining its immediate arity and nesting |
| `Q<A>` | One linear quantum owner with basis `A` |
| `(Q<A>,Q<B>)` | Two linear owners, without any assumption of state separability |

The Bit literal spelling is `0` / `1` in both ordinary and basis
computations. `false` / `true` migrate explicitly to `0` / `1`. A numeral in a
static-Nat position instead denotes a natural; this stage/category distinction
does not inspect quantum data. No literal creates a quantum owner. Other Bit
numerals reject, and expected typing cannot implicitly prepare or measure data.

Typing keeps ordinary bindings, static bindings, linear owners and semantic
effects distinct. Ordinary values may be copied or dropped. Every quantum owner
must be moved, returned or explicitly consumed according to an admitted rule.
An ordinary binding operation on `Q<A>` does not require a `qlet` spelling.
Effects cannot be inferred from ownership alone, and an annotation cannot
downgrade the effect of its body.

The conceptual typing judgment is `Γ ; Δ ⊢ e : T ! ε`. Here `Γ` contains
ordinary values and the separately classified static environment; `Δ` contains
live linear quantum ownership, including quantum fields of ordinary products.
`ε` is the semantic effect computed from the complete body and its callees.
The implementation may store ordinary and linear bindings in one table, but
it checks their different reuse rules from the exact type and tracks moves by
binding identity. Moving a value removes its linear ownership from subsequent
use; copying an ordinary value neither creates nor consumes a quantum owner.
Static bindings cannot be used as runtime values. The judgment describes the
source contract; it is not a claim that a general source-soundness theorem has
been discharged.

The surface follows three distinct roles. A `q` construct, such as `qif` or
`qfor`, explicitly supplies coherent control or a quantum-owner fold. `Q<A>`
marks quantum ownership even in ordinary syntax such as `let`, a function
argument or an explicit call. Unmarked constructs operate according to their
ordinary/static rules: an ordinary `if` requires `Bit`, not `Q<Bit>`, and a
static fold cannot inspect quantum state. A prefix alone grants no operation
access, effect or evidence. The conceptual `match`/`qmatch` distinction follows
the same rule, but does not admit pattern forms before their own specification
and implementation. Supported folds are specified in [static control](static-language.md).

## Structural equality, coherence and physical maps

Definitional type equality compares constructor tags, evaluated static sizes,
immediate tuple arity, nesting and ordered leaves. In this 0.3.0 contract:

- `Bit` and `Bits<1>` are distinct.
- `Unit` and `Bits<0>` are distinct.
- `((A,B),C)`, `(A,(B,C))` and `(A,B,C)` are distinct.
- `Q<(A,B)>` and `(Q<A>,Q<B>)` are distinct ownership interfaces.

Equal width, cardinality or Hilbert-space dimension is insufficient. For
symbolic sizes, the bounded static solver must establish equality under the
same explicit premises; failure to find a counterexample is not equality.

Canonical coherence is a separately justified structural map, not definitional
equality. Its admitted action must preserve ownership and ordered axes with
exact phase `+1`, including extension by an arbitrary reference system. No
implicit coherence is introduced by this foundation. Existing split/join and
any subsequent reassociation or unit map remain explicit and independently
checked. The catalogue of future implicit conveniences remains in
[#197](https://github.com/MGYamada/Qleisli/issues/197).

A physical map, including SWAP, preparation, observation, reset, discard or
nontrivial phase, is never inserted as ordinary type coercion. Rearranging
bindings is not permission to rearrange axes. Pattern destructuring of a tuple
does not implicitly split a quantum owner whose basis is a tuple.

## Predicate domains and argument lists

A predicate used by either form of `with_computed` takes **one** ordinary basis
parameter of the source register's exact basis type and returns `Bit`. An
argument list is not implicitly folded into a tuple. This is the same exact
single-domain convention already required of a `Meaning` function.

For example, a register of basis `((Bit,Bit),Bit)` may use
`classical fn p(((a,b),c): ((Bit,Bit),Bit)) -> Bit { a and c }`.
A flat `(Bit,Bit,Bit)` or right-nested `(Bit,(Bit,Bit))` register requires a
parameter with that precise tree. A predicate on `Q<Unit>` takes `u: Unit` or
`_: Unit`; a nullary function is not an implicit Unit-domain predicate.

Classical function calls continue to use their declared argument-list arity.
`f(a,b)` and `f((a,b))` are distinct, and ordinary nullary calls remain nullary.
When migrating a predicate used in both roles, update its ordinary callers or
write a separate unary wrapper with an explicit product pattern. No implicit
packing, reassociation or physical conversion repairs a mismatch.

Predicates must be total but need not be injective. Constant and AND predicates
remain valid; their computed auxiliary must still satisfy the applicable exact
cleanup rule. Coherent basis lifting retains its separate injectivity check.
Truth-table leaf order, retained phase, external reference correlations and the
original owner's exact type are unchanged. This rule removes the historical
left-folding behavior tracked in [#25](https://github.com/MGYamada/Qleisli/issues/25);
implementation and migration evidence are recorded there.

## Unit owners retain phase

`H(Unit)` is one-dimensional, not zero-dimensional. `Q<Unit>` remains a linear
owner despite having zero physical wires. So does `Q<Bits<0>>`. Copying,
silently dropping or reviving either owner rejects.

The scalar operator `[-1]` cannot be erased: under coherent control it becomes
the nontrivial relative phase `diag(1,-1)`. Structural simplification must retain
that action and the owner/evidence interface. A pure introduction or elimination
map for a Unit owner needs its own explicit checked rule; ordinary `()` supplies
neither such a map nor an implicit `Q<A> -> A` conversion.

Common source checking retains `Q<Unit>` and `Op<Unit>` alongside `Q<Bit>`,
`Q<Bits<n>>` and complete packaged Basis trees. Helpers and operation providers
retain the exact basis and linear owner even with an empty physical axis list.
`std::quantum::phase_eighth(q)` consumes one `Q<A>` owner for any Basis tree A
and returns its exact type with scalar action `exp(i*pi/4) I`. Its sole argument
evaluates once; it takes no static arguments and has Unitary effect. An ordinary
value or a tuple of separate owners is not a valid argument. The selected
concrete scalar path currently supports the Unit/Bit/Bits atoms; checking a
packaged tuple does not add that concrete emitter capability. This scalar is
distinct from `phase[1,3]`, whose Bit action is `diag(1, exp(i*pi/4))`.

Hierarchy lowering retains that scalar through explicit checked Unit structure
and a finite scalar leaf, tensored with the original owner's identity. The
internal Unit owner adds no physical wire and does not change the source
basis. Adjoint conjugates the scalar, eight repetitions give identity, and
coherent control of four repetitions gives Z on the control. Removing a Unit
factor cannot remove the scalar.

The common selected-source hierarchy path exposes two explicit structural maps:

- `std::quantum::unit(u)` takes exactly one ordinary `Unit` argument and returns
  one fresh `Q<Unit>` owner.
- `std::quantum::finish(q)` consumes exactly one `Q<Unit>` owner and returns
  ordinary `Unit`.

Both take no static arguments and have Unitary quantum action with exact
coefficient `+1`. They lower to the existing checked `pack_unit` and
`unpack_unit` constructors. Neither allocates a physical wire, measures, discards
or converts another basis implicitly. `unit()` is an arity error; write
`unit(())`. Bit, Bits<0> and their quantum owners are not substitutes for the
specified argument types.

Both arguments evaluate completely, once, before their map. In particular,
`finish(phase_eighth(unit(())))` has scalar coefficient `exp(i*pi/4)`;
its ordinary Unit result does not erase that computation. Reintroducing a
Unit owner after finishing it gives a fresh owner, never revives the consumed
binding, and preserves the phase and any retained reference. An observing
argument still makes its caller observing.

These maps can form explicit left/right maps on separate-owner products, such
as `(Q<Unit>, Q<Bit>)` to `Q<Bit>`. Both names belong to the common source catalog, but finite concrete lowering
does not materialize them and the shared Raw profile rejects these structural
map operations; it supports retained Unit owners and scalar phases. No observing discard or retry after native failure supplies a
substitute.

The selected hierarchy also admits packaged quantum bases built recursively
from `Unit`, `Bit`, `Bits<n>` and ordered tuples, including `Op<A>` for those
bases. `Q<(A,B)>` is one owner; `(Q<A>,Q<B>)` is two. Ordinary tuple patterns
cannot unpack the former. The two explicit maps are:

- `split(q): Q<(A,B)> -> (Q<A>,Q<B>)`, consuming one owner and returning two
  fresh owners in left/right order;
- `join(a,b): (Q<A>,Q<B>) -> Q<(A,B)>`, consuming two distinct owners and
  returning one fresh owner with the complete ordered basis tree.

Both names are in `std::quantum`, take no static arguments, and have Unitary
action with coefficient `+1`. `split` has one argument and requires an immediate
binary basis tuple; `join` has two arguments, not one ordinary tuple argument.
Their arguments evaluate completely, once, from left to right. Nested trees,
zero-axis factors, correlations with retained owners and physical axis order
are preserved. Neither map asserts separability, flattens a tuple, changes a
basis tag, measures or silently discards an owner. They use the existing native
`split_tuple` and `join_tuple` rules; native support for other arities does not
widen this source signature.

An explicit left unitor on `Q<(Unit,A)>` is `split` followed by `finish` on its
Unit owner; its inverse is `join(unit(()), a)`. The right unitor uses the other
factor. The coefficient is exactly `+1` on every basis value and retained
reference. Scalar work already performed on an eliminated Unit factor remains
in the composition. These maps are never inserted by implicit coercion.
The common source signature of `phase_eighth` also permits this packaged basis,
but its selected concrete preparation still requires a Unit/Bit/Bits atom.
Applying it directly to a packaged tuple therefore fails that concrete
eligibility check; successful source typing supplies no missing emitter.

Ordinary `Unit` has no quantum owner identity. Its value may be copied, dropped
or matched by the empty pattern `()`, including inside an ordinary tuple.
That pattern matches only ordinary `Unit`, not an empty tuple, `Bits<0>`,
`Q<Unit>` or `Q<Bits<0>>`. Nonempty tuple patterns preserve the same immediate
arity and recursively match each child's exact shape. Ordinary function
parameters, `let` bindings, classical function parameters and coherent basis lifts
use this same pattern shape rule. A typed parameter remains one argument:
`unitary fn f((a, b): (Bit, Bit), (): Unit) -> Bit { a xor b }` takes two
arguments. Matching its first
argument does not flatten the calling convention. Parameter names must be
unique across the complete parameter list and distinct from static parameters.
An ordinary wildcard may ignore unrestricted data; it cannot discard a quantum
owner, including one nested inside an ordinary product or having zero width.

Rest patterns such as `..` are not part of the current source grammar. If a
future pattern form elides components, every omitted component must be proven
unrestricted or already explicitly consumed under a separate language rule.
Rest syntax never implies discard, reset, release or measurement. Rejection of
an elided live quantum component must identify that field or component,
including nested and zero-width owners. This is an intentional divergence from
ordinary Rust pattern ergonomics, required by the
[#35 pattern contract](https://github.com/MGYamada/Qleisli/issues/35); it does not
admit rest syntax or promise those diagnostics before that syntax is implemented.

The pattern in `basis q as () { () }` describes the ordinary Unit basis of its
quantum input. The [coherent basis map](coherent-basis.md) consumes and returns
a `Q<Unit>` owner with coefficient `+1`, retaining any scalar already present
on its input; it is not runtime `let () = q` or an implicit owner elimination.
This source rule does not supply the selected concrete projection with
CoherentLift support, or remove the finite profile's existing quantum Unit
limitations. Sized lowering omits
ordinary Unit value ports while retaining the exact source interface and all
executed operations. A computation returning Unit can still consume owners or
perform observable work; omitting its result port does not omit its body.

## Inference and generic responsibilities

The [static language](static-language.md) specifies natural expressions,
guarded arithmetic, termination and the current specialization capacities.

Infer only uniquely determined static structure under specified rules. Reject
ambiguous type substitutions, callable categories and provider choices. No
search for a convenient implementation, numerical coincidence or matching name
may manufacture meaning, an inverse, coherent control or semantic evidence.

For a fixed source, dependency set and selected toolchain, preparation is
deterministic and terminates under its published static work, storage and depth
limits. An unresolved constraint rejects; exhaustion of a checking budget is
not a successful inference or a proof of impossibility. Trait/capability
resolution cannot use cyclic guessing or absence of contradiction as evidence,
and callable resolution must establish a unique declared category before
ordinary checking. An effect annotation cannot downgrade the body's meaning.

The current conservative profile requires complete explicit closed Nat and Op
bindings. A mismatch reports the selected entry, the binding category, and
missing and unexpected names in lexical order. A provider's missing Nat
binding also identifies the affected Op binding and resolved provider. Source
call arity errors identify the resolved declaration, its ordered static
parameter names/categories and the supplied count. These diagnostics do not
choose missing values or providers; even an unused static parameter must be
bound. Natural-binding errors precede operation-binding errors as before.
Basis bindings precede naturals when the declaration introduces Basis parameters;
Nat/Op-only declarations retain their previous diagnostic priority.
The concrete catalogue of future inference/coherence conveniences remains in
[#197](https://github.com/MGYamada/Qleisli/issues/197).

An abstract `A : Basis` is opaque. A body may move and return `Q<A>` and apply
explicit providers justified by its constraints. It cannot inspect the type as
a tuple, assume a width or prepare a state merely because `A` is finite.
Static parameters are explicit and ordered; a parameter kind may refer only to
earlier parameters. Runtime values never determine static sizes or providers.

The mandatory common source judgment covers every original declaration,
owner/effect rule, capability, dependency and static branch, including private
and unused declarations, both arms, zero-iteration bodies and all four ordinary
bundled modules. A source-semantic error precedes concrete profile eligibility.
Specialization then checks closed substitutions, exact type trees, provider
identity, premises and aggregate work. Specialization keys retain those inputs
and source/dependency identity; width alone is not a key. Instance success is
not a proof about every member of a generic family.

An endomorphic `Op<A>` formal starts with no executable access. Each
`requires Apply(U)`, `Adjoint(U)` or `Controlled(U)` grants only that named
generic assumption, and must refer to an operation parameter of the same
declaration. Repeating the same requirement rejects; granting one access
does not grant the other two. The body and any forwarded call must satisfy
their own required access even when unused or inside a zero-iteration fold.
A mathematical Meaning refinement or Unitary effect is not an access grant.
Concrete providers still require their checked implementation paths; a
generic assumption is not evidence for an arbitrary external provider.

### Direct runtime transforms and opaque operations

A direct `adjoint`/`controlled` target given by an ordinary function name, its
explicit static specialization or a transparent `repeat_op` wrapper has a
runtime target type T. With one runtime parameter, T is its complete input type;
with more, T is the exact ordered tuple
of complete input types. Arity zero rejects. T must be a nonempty tree of quantum
owner leaves and equal the checked result under the actual substitutions and
caller premises. `Q<Unit>` and `Q<Bits<0>>` are valid leaves with their ownership
and scalar phase intact. Ordinary Unit/Bit/Bits, empty tuples and mixed
classical/quantum trees reject; equal width cannot repair a different tree.

Direct `adjoint` evaluates its input once and returns T. Direct `controlled`
evaluates control then target once and returns `(Q<Bit>,T)`. Each original
owner is consumed and returned exactly once; no implicit split, join, packing or
reassociation occurs. The named body must have principal Unitary effect and
the required implementation path. Transparent Repeat checks its count and
child even at zero. Only a directly transformed runtime self-call to the same
DefId may use the actual checked Nat decrease; this permits neither recursive
opaque providers nor mutual dependency cycles. A located RuntimeGroupProvider
obligation retains the original provider DefId, complete runtime interface and
principal effect. Its source association is not transformed-operator equality,
provider correspondence or a source-preservation proof.

This runtime-group rule does not widen an opaque `Op<A>`, static/host provider,
Meaning refinement, certified logical operation or FunctionEquality contract.
Opaque `Op<A>`, static/host provider and certified logical-operation interfaces
keep one input `Q<A> -> Q<A>`. FunctionEquality keeps that interface for its
checked implementation and any ordinary specification function. A declared
Meaning remains a semantic object, not a runtime function. `tensor_op` describes
a packed quantum basis.
Transparent specialization derives access conservatively from every actual Op
argument, including unused ones: inverse access requires each argument's Apply
and Adjoint paths, and controlled access additionally requires Controlled.
A body annotation or mathematical Unitary property grants none of those paths.
The direct-group distinction is recorded in the
[ordinary #32 clarification](https://github.com/MGYamada/Qleisli/issues/32#issuecomment-6005081767).
Concrete transform/evidence and native checking remain separate obligations.

`apply_contract` evaluates its input first and retains one exact quantum owner.
Its implementation and ordinary specification are closed principal-Unitary
`Q<A> -> Q<A>` declarations; a declared finite Meaning may supply the
specification instead. The common checker records a located FunctionEquality
obligation binding both exact original DefIds, interface/category/effect and
source span. Meaning/provider identity binding is not matrix equality,
injectivity, all-input clean return, provider correspondence or source
preservation. Those properties remain pending until the existing independent
concrete evidence gates discharge them. A selected projection of a declared
Meaning or meaning-refined Op remains explicitly unsupported when requested;
checking the original source never substitutes another specification or route.

Selected preparation additionally evaluates every declared finite Meaning from
its original classical body and resolved dependencies, including unused targets.
Permutation targets must be total bijections; phase targets return the exact
three-Bit product for powers of zeta_8, including scalar phase on Unit. These
bounded checks retain Unit/Bit/Bits/product tags and leaf order and share the
common work budget. The immutable preparation retains these tables under the
original resolved Meaning definition IDs, with the complete basis tree and
permutation or phase rows. Closed operation binding checks that same requested
basis, rather than substituting another same-width target. Tables remain
untrusted requested data: they do not establish
provider equality, enable Meaning-refined selected operations or authorize
execution. Existing projection refusals remain until artifact-bound native
comparison is connected.

The Rust preparation API `ParsedProgram::finite_meaning_target` resolves one
original Meaning into an untrusted `FiniteMeaning` request. It selects no
provider and issues no accepted handle. The legacy finite signature can describe
exact Unit, Bit and ordered product trees; it cannot describe the distinct Bits
tag, so this conversion rejects Bits instead of replacing it by a same-width
type. The existing native finite-leaf gate can compare this request with actual
provider bytes. Callers must still bind that result to the source instance and
dependencies; requesting a target alone does not enable a refined operation.

### Opaque Basis specialization in the selected profile

The common grammar admits `static A: Basis`, `Q<A>` and `Op<A>`. A's identity
is its resolved declaration binder, not its spelling or an inferred width.
An abstract ordinary A may be copied; its quantum owner may only be moved and
returned or passed to operations justified by explicit access constraints.
Abstract decomposition, reflection, quantum preparation and favorable-instance
rescue of an invalid generic body are unavailable. Kinds refer only to preceding
parameters. All supplied declarations, branches and zero-iteration fold bodies
are checked before any selected type/provider binding is considered.

Source calls forward a resolved opaque parameter by name. An explicit concrete
static argument is `type(T)`:

```qli
inner[A,U](q)
inner[type(Bit),identity_bit](q)
```

This description creates no runtime type
value or quantum owner. A runtime function named `type` remains an ordinary
function; existing contextual static Nat names such as Bit retain their category.
No argument is inferred from expected width, type or an available provider.

The Rust API uses `BasisBinding::parse`, `instantiate_with_types` and
`OperationBinding::with_types`. The existing `instantiate` and provider `new`
methods supply empty type maps. Entry types use `--type=A=Bit` or an exact
closed ordinary product in the common CLI. A provider binds its own declaration's
types separately with `--operation-type=U.B=Bit`. Missing, extra and wrong-category
bindings reject; a provider does not inherit the caller's parameters by name.
`--basis=N` retains its distinct hierarchy runtime-input role.

Closed descriptions use the same type grammar, require EOF and reject unknown
names, quantum owners, unresolved sizes and invalid bounded arithmetic. This
selected profile retains eight total basis bits, 4096 type nodes and depth 64.
Substitution expansion is checked before copied trees are allocated, and retained
type bindings and cache data count against the existing 100000-cell preparation
budget. The existing 1024 calls/folds, call depth 16 and 10000 steps remain.
These preparation limits are not a discharged quantitative RS theorem.

Before specialization, both paths enforce the common 1,000,000-work budget
with charges before source visits, copied/allocated type and lexical cells,
normalization and solver work. Per-value type capacity is 4096 cells/depth 64;
selected retained runtime scopes additionally have a 16,384-cell limit. The
finite path retains its own aggregate/type/snapshot limits. These are separate
from the concrete limits above and from native/evidence work. Capacity refusal
is not a proof of a semantic impossibility or a quantitative RS certificate.

Each specialization keeps exact constructor tags, tuple order/nesting, selected
type/Nat/provider bindings, original source/dependencies and local identities.
Width alone never selects a cache entry or conversion. Concrete instances lower
to the existing native representation and receive a fresh Lean decision; no new
native primitive or accepted-handle constructor is introduced. Concrete Meaning
evidence, emitter/projection convergence and source-preservation proofs remain
their separately recorded obligations. A selected native success certifies only
its actual checked artifact/contract under the disclosed boundary.

## Migration and native boundary

| Previous surface | Target mapping |
| --- | --- |
| `CBit` / `CBits<n>` | `Bit` / `Bits<n>` |
| Ordinary `false` / `true` | `0` / `1` |
| Sized result-type `()` | `Unit`; the value remains `()` |
| A same-width value of a different tree | Explicit specified conversion or rejection; no implicit cast |

The retired type and literal spellings reject with migration diagnostics; they
are not accepted aliases. Empty parentheses remain value and pattern syntax,
and an empty argument list remains nullary. In a type position, write `Unit`.

The public sized `SourceType` view uses `kind() == "unit"`, `"bit"` or `"bits"` for an
ordinary or quantum leaf. Callers must use `is_quantum()` to distinguish their
ownership; the kind string alone is insufficient. Ordinary Unit and `Q<Unit>`
both have kind `"unit"`, width zero and no tuple fields, but only the latter
has a quantum owner. A packaged quantum tuple has kind `"tuple"` but no ordinary
destructuring fields. `quantum_basis()` exposes its exact read-only basis tree;
`FramePort::basis()` retains the same whole tree on a quantum port. Code must
not infer ownership, arity or equality from width or kind alone. The hierarchy's Unit owner port, Bits(0) owner port and
empty quantum-port list are three distinct interfaces. Native classical port tags are
unchanged by this source/API migration.

Measurement explicitly consumes a supported `Q<A>` and produces ordinary data
with Observe semantics. An ordinary `if` consumes an ordinary Bit condition;
it cannot read a `Q<Bit>`. Coherent control has its separate rule.

The finite QIRF basis representation currently has Unit/Bit/Pair/Tuple but no
Bits atom. Hierarchy distinguishes Unit/Bit/Bits/tuple. The common frontend must
retain the full source tree and use an explicit representation mapping or
reject an unsupported lowering profile. It must not silently map `Bits<1>` to
Bit or `Bits<0>` to Unit to obtain evidence.

The current finite profile supports ordinary Unit/Bit values and products, but
does not yet lower Bits atoms. Both profiles use the same exact Bit judgment
and eager, left-to-right operand evaluation for `0`, `1`, `not`, `and` and `xor`.
Both operands of `and` evaluate even when its left value is zero. Quantum
operands, `Bits<1>`, static naturals and products are not coerced to Bit.

The sized Rust API's `ElaboratedProgram::lower_raw` produces an untrusted finite
proposal for `Unit`/`Bit`/`Q<Unit>`/`Q<Bit>`/products, including specialized ordinary helper
calls and static folds. Its `source()` retains whole parameter/result trees and
the original source instance. Native `Kernel::accept` must check `proposal()`
before execution. `validate_source_steps` separately compares the exact accepted
Raw instructions with the retained source-step graph; it does not prove the
preceding source elaboration or grant native acceptance. Ordinary open inputs
are represented and checked, but `sim::run_closed` still requires a closed
artifact. A closed source wrapper is a distinct specialization of an open
function, not execution of that original open artifact.

`Q<Unit>` inputs and returns retain distinct linear owners with empty wire
lists through ordinary calls and exact products. Ordinary `Unit` supplies no
owner. Independent source-step comparison checks the ordered owner result;
native validity alone cannot establish that a source returned the intended
zero-width owner. Exact unary `Q<Unit>` and `Q<Bit>` endomorphisms retain their
source-derived finite root interface so a separate native finite request can
bind the same artifact to an independently supplied matrix. No width-based
conversion to a different basis is inferred.

Finite and sized Raw emission share quantum registers, fresh identities and the
actual init0/H/X/CNOT/measurement transitions. A measurement consumes its owner
and produces an ordinary Bit that may be used by Boolean operations. Physical
state spans pending arguments and suspended callers; separate ownership never
implies that those subsystems are separable. Each call gets its own source-ID
environment while global token, wire and classical supplies remain fresh.

The Raw adapter supports `phase[j,k]` only when its exact angle is an integral
multiple of an eighth turn: the existing source domain requires `k <= 8` and
`j < 2^k`, and `8*j / 2^k` must be an integer. That many T gates implement the
phase, including zero gates for the identity. Smaller angles are not rounded.
For example, `phase[1,3]` and `phase[2,4]` are exactly T, while `phase[1,4]`
requires the existing hierarchy phase target. This is a target capability
distinction, not a source type or edition distinction. The adapter enforces the
existing 16-live-wire bound across whole call frames, before allocation.

`phase_eighth(q)` uses the existing zero-axis monomial to multiply the complete
`Q<Unit>` or `Q<Bit>` owner by exactly `exp(i*pi/4)`. On Bit this is a scalar
times identity on both basis labels, not T on one axis. It consumes the original
token and returns a fresh token with the same shape and wires. Raw source-step
comparison independently checks the scalar opcode, exact phase, empty controls
and axes, and the intended owner; fresh native validity is still mandatory.
Preceding argument work and subsequent observation stay in source order.

This Raw adapter still rejects Bits values, other quantum basis shapes,
controlled-phase primitives and operation providers. Checked open runtime
invocation and runtime branches remain unfinished. The existing
hierarchy `lower()` path retains its quantum and ordered-readout contracts and
rejects Boolean steps at their source locations; a failed native hierarchy
decision is never retried as weaker Raw validity. Total `classical fn` bodies
are reusable as ordinary runtime computations: supported Unit/Bit/product calls
use the same checked expression nodes and eager ordinary operations in both
consumers. Runtime argument effects remain in the caller, and an ordinary call
does not grant coherent injectivity or Meaning evidence. Bits runtime lowering,
selected coherent lifting and concrete Meaning-refined Basis materialization
retain their explicit profile limitations. All original declarations and bodies
are nevertheless checked by the common source judgment. Packaged hierarchy bases retain the
selected-source concrete width limits and charge every basis-tree node,
including zero-width factors, to preparation storage/depth limits before
materializing copied trees.
Successful generic checking does not imply successful concrete lowering.
These limits do not establish separate type universes or close the remaining
[#27](https://github.com/MGYamada/Qleisli/issues/27) work.

### Selected-source execution

The ordinary `check`, `run`, `sample` and `emit-proposal` commands accept an
explicit `--entry=module::function` and repeated `--module=name=PATH` bindings,
with explicit `--type`, `--nat`, `--operation`, `--operation-type` and
`--operation-nat` forms. The legacy
`sized` prefix delegates to the same selected-source execution plan. This is
an adapter transition; it does not complete the final grammar/CLI migration.
Directory/qrate and explicit-module inputs retain their loader/provenance and
concrete consumer differences, but both first check every complete original
and the four bundled ordinary sources through the same judgment. Finite then
requires its concrete declarations to fit its profile; selected input seeks
native acceptance only for the requested concrete specialization. Native
results distinguish those scopes and do not certify every possible
specialization or establish general source preservation.
Finite directory execution still requires an ordinary zero-argument `fn main`
with a closed classical result. Selected execution may name a public
`classical fn` as its ordinary root, subject to its existing input and profile restrictions.
Selected commands return a JSON result object; `--format=json` uses the common
`qleisli.result` envelope for success and diagnostics. Without that flag,
errors remain text on stderr, as in the legacy selected-input command.

`--ir-profile=auto|raw|hierarchy` selects an IR/checker route, not a physical
target model. Auto uses the hierarchy for its supported root signature,
effect and source-step profile; an explicit capability mismatch selects Raw.
Generic errors and capacity failures are not profile selectors. A caller
request or named-QPE provider fixes the hierarchy route; combining one with
explicit Raw rejects before native checking. After a route is selected, its
lowering or native failure propagates without retrying a weaker route.

The selected hierarchy admits a principal Iso root with quantum entry values
and quantum results, optionally accompanied by one ordinary `Bits<0>` result.
Ordinary Unit result ports remain omitted as described above. The body must
fit the existing preparation and pure-operation profile: fresh zero
initialization, followed by checked unitary hierarchy operations, with no
observation. Lowering uses the existing initialization/evolution/readout
transport with zero measurements. Its single empty outcome is a transport
carrier; it introduces no source Observe effect, measurement or conversion
between `Unit` and `Bits<0>`. The source effect remains Iso even when an
optional prefix asserts the broader Observe bound.

Iso `check` reports the `sized-isometry` profile. Iso `run` returns the residual
quantum width and the single branch's unnormalized complex coefficients,
without removing scalar phase. A retained `Q<Unit>` owner, explicit
`unit`/`finish` work and every live caller frame retain their original
ownership and phase obligations. `sample` and named-QPE selection require a
principal Observe entry; a broader annotation does not turn Iso into Observe.
This adapter introduces no native primitive or new theorem. Raw supports
retained quantum Unit inputs/returns and exact `phase_eighth`, but still rejects
the structural Unit introduction/elimination maps; selecting Raw does not
supply a second implementation of these maps. The existing source, native
and execution proof limits continue to apply.

Raw checking retains the original source signature. Raw `run` and `sample`
require zero declared runtime parameters and no quantum result. A Unit
parameter is still an argument, even though it has zero physical width.
Any explicit `--basis`, including zero, rejects on Raw; it remains a quantum
input selector for hierarchy execution. Native acceptance precedes the
independent source-step comparison and actual Raw execution. The result
reports native validity, no caller request, the step comparison and
`source_meaning_verified: false`. Hierarchy results retain their separate
producer-consistency, caller-composition or named-QPE scope and do not claim
the Raw step comparison.

Selected inputs accept `--lean-kernel` (`--kernel` is an alias) or an explicitly
configured `QLEISLI_KERNEL`; duplicate aliases reject. No download or alternate
checker fallback occurs. Selected sampling retains its 1024-shot capacity;
project sampling retains its separate 1,000,000-shot capacity. These are
current adapter limits, not quantitative resource certificates.
`emit-proposal` writes untrusted transport without invoking a kernel. It is
distinct from project `emit-ir`, which freshly verifies its emitted artifact.

All frontend output remains an untrusted proposal. Existing native root,
request, contract, hierarchy and finite-leaf gates remain mandatory. The
[two admitted scoped guarantees](../design/initial-guarantees.md) do not by
themselves prove source type-tree preservation. Required conformance includes
same-width different-tree substitution, tuple arity, zero-owner loss/duplication,
controlled scalar phase and runtime-to-static leakage. These requirements
remain open until their implementations and actual results are recorded in the
linked Issues; this chapter does not discharge QS, PR or quantitative RS.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
