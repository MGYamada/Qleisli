# Ordinary types, quantum owners and equality

This chapter specifies the **0.3.0 target contract** under the adopted
[#22](https://github.com/MGYamada/Qleisli/issues/22) /
[#27](https://github.com/MGYamada/Qleisli/issues/27) type boundary and the
[authority hierarchy](authority.md). The current alpha frontend uses the
canonical ordinary `Unit`, `Bit`, `Bits<n>` and `0`/`1` spellings described
below. Both checking profiles classify the common source type tree and retain
its exact ownership boundaries. General basis polymorphism and convergence of
the execution profiles remain in progress. The
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
`basis fn p(((a,b),c): ((Bit,Bit),Bit)) -> Bit { a and c }`.
A flat `(Bit,Bit,Bit)` or right-nested `(Bit,(Bit,Bit))` register requires a
parameter with that precise tree. A predicate on `Q<Unit>` takes `u: Unit` or
`_: Unit`; a nullary function is not an implicit Unit-domain predicate.

Ordinary basis calls continue to use their declared argument-list arity.
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

Ordinary `Unit` has no quantum owner identity. Its value may be copied, dropped
or matched by the empty pattern `()`, including inside an ordinary tuple.
That pattern matches only ordinary `Unit`, not an empty tuple, `Bits<0>`,
`Q<Unit>` or `Q<Bits<0>>`. Nonempty tuple patterns preserve the same immediate
arity and recursively match each child's exact shape. Ordinary function
parameters, `let` bindings, basis function parameters and coherent basis lifts
use this same pattern shape rule. A typed parameter remains one argument:
`unitary fn f((a, b): (Bit, Bit), (): Unit) -> Bit { a xor b }` takes two
arguments. Matching its first
argument does not flatten the calling convention. Parameter names must be
unique across the complete parameter list and distinct from static parameters.
An ordinary wildcard may ignore unrestricted data; it cannot discard a quantum
owner, including one nested inside an ordinary product or having zero width.

The binder in `do () <- q; pure ()` describes the ordinary Unit basis of its
quantum input. The existing coherent lift still consumes and returns a
`Q<Unit>` owner and retains its scalar action; it is not runtime `let () = q`
or an implicit owner elimination. Sized lowering omits
ordinary Unit value ports while retaining the exact source interface and all
executed operations. A computation returning Unit can still consume owners or
perform observable work; omitting its result port does not omit its body.

## Inference and generic responsibilities

Infer only uniquely determined static structure under specified rules. Reject
ambiguous type substitutions, callable categories and provider choices. No
search for a convenient implementation, numerical coincidence or matching name
may manufacture meaning, an inverse, coherent control or semantic evidence.

An abstract `A : Basis` is opaque. A body may move and return `Q<A>` and apply
explicit providers justified by its constraints. It cannot inspect the type as
a tuple, assume a width or prepare a state merely because `A` is finite.
Static parameters are explicit and ordered; a parameter kind may refer only to
earlier parameters. Runtime values never determine static sizes or providers.

Generic checking covers every declaration, owner/effect rule, capability and
static branch, including unused declarations and zero-iteration bodies.
Specialization then checks closed substitutions, exact type trees, provider
identity, premises and aggregate work. Specialization keys retain those inputs
and source/dependency identity; width alone is not a key. Instance success is
not a proof about every member of a generic family.

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

The public sized `SourceType` view uses `kind() == "bit"` or `"bits"` for an
ordinary or quantum leaf. Callers must use `is_quantum()` to distinguish their
ownership; the kind string alone is insufficient. Ordinary Unit has kind
`"unit"`, width zero and no tuple fields. Native classical port tags are
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
proposal for Unit/Bit/Q<Bit>/products, including specialized ordinary helper
calls and static folds. Its `source()` retains whole parameter/result trees and
the original source instance. Native `Kernel::accept` must check `proposal()`
before execution. `validate_source_steps` separately compares the exact accepted
Raw instructions with the retained source-step graph; it does not prove the
preceding source elaboration or grant native acceptance. Ordinary open inputs
are represented and checked, but `sim::run_closed` still requires a closed
artifact. A closed source wrapper is a distinct specialization of an open
function, not execution of that original open artifact.

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

This Raw adapter still rejects Bits values, other quantum basis shapes,
controlled-phase primitives and operation providers. Explicit runtime invocation,
runtime branches and CLI integration remain unfinished. The existing
hierarchy `lower()` path retains its quantum and ordered-readout contracts and
rejects Boolean steps at their source locations; a failed native hierarchy
decision is never retried as weaker Raw validity. General product and `Q<Unit>`
bases, reusing basis functions as runtime computations and full common checking
also remain unfinished profile obligations.
Successful generic checking does not imply successful concrete lowering.
These limits do not establish separate type universes or close the remaining
[#27](https://github.com/MGYamada/Qleisli/issues/27) work.

All frontend output remains an untrusted proposal. Existing native root,
request, contract, hierarchy and finite-leaf gates remain mandatory. The
[two admitted scoped guarantees](../design/initial-guarantees.md) do not by
themselves prove source type-tree preservation. Required conformance includes
same-width different-tree substitution, tuple arity, zero-owner loss/duplication,
controlled scalar phase and runtime-to-static leakage. These requirements
remain open until their implementations and actual results are recorded in the
linked Issues; this chapter does not discharge QS, PR or quantitative RS.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
