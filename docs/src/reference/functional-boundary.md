# Functional abstraction and the quantum boundary

This chapter is normative for the current `0.3.0-alpha` callable and abstraction
boundary in constitutional edition 2026. It follows the
[ordinary decision in #80](https://github.com/MGYamada/Qleisli/issues/80#issuecomment-6009479668)
and is subordinate to the [authority hierarchy](authority.md). Rust and Haskell
are design influences, not independent semantic authorities. Familiar notation,
an annotation, a compiler result or the project's name cannot establish a
mathematical law or constitutional certification.

Qleisli admits functional construction where it preserves exact interfaces,
linear owners, physical effects, phase, ordered axes and the actual independent
checking boundary. It does not import the unrestricted duplication, closure,
laziness or partiality assumptions of ordinary Haskell values into quantum
ownership. This chapter specifies existing forms and their refusals; it adds
no language feature, primitive, trusted assumption, interpretation or guarantee.

## Runtime calls and static descriptions

An ordinary function is a declaration called with its complete ordered static
and runtime arguments. Runtime calls are first-order. There is no general
runtime function or closure value, currying or partial application. A missing
argument is an arity error, not construction of a callable waiting for the rest.
A local runtime value is not callable; failed local lookup cannot fall back to a global
function with the same name. Returning or packaging a live owner does not make
that package a reusable function.

The parser recognizes bounded closure-shaped expressions only to diagnose
unsupported input; it does not admit a callable value. For `|| body`,
`|pattern, ...| body` and their contextual `move` forms, common checking uses
resolved lexical identities and the enclosing checked types to identify a
captured live quantum owner at its actual use. Products containing an owner,
`Q<Unit>` and `Q<Bits<0>>` are linear too. A previously consumed owner retains
its ownership error. Parameter or body-local shadowing is distinct from a
capture; a name or closure type annotation cannot supply quantum type evidence.
Checking remains bounded by the existing parser and source-work limits.

When no live quantum capture is found, the expression still rejects as an
unsupported runtime closure. Ordinary classical captures do not grant a
callable implementation in this profile. Both source lowering paths explicitly
refuse these diagnostic forms, so no hidden environment can reach an accepted
artifact. A future linear, one-shot or higher-order quantum callable requires
its own specified type, usage, effect and access contracts; this refusal does
not infer such a type. Existing bounded static operation composition below
remains available without storing live owners.

Runtime arguments and right-hand sides evaluate completely, once, from left
to right before binding. Effects of argument evaluation remain part of the
caller even when an ordinary result is ignored. Function bodies, unused
declarations, both branch arms and zero-iteration fold bodies undergo the
common source judgment. Checking both arms does not mean executing both arms.
The [source rules](source-text.md#ordinary-function-effects-and-assertions)
specify principal effects and assertion checking.

Total finite `classical fn` declarations also have ordinary runtime calls.
Their restricted pure expression bodies use the same ordered ordinary argument
and exact type rules. Argument observation remains an effect of the caller;
a live `Q<A>` cannot become ordinary `A` by calling a classical function.
The same definition may be used in a static Meaning or coherent basis body,
where the existing finite-domain and injectivity checks still apply.
Noninjective ordinary computation grants neither coherent access nor inverse
or control evidence. See [classical declarations](source-text.md#total-classical-declarations)
for the grammar, migration and concrete profile limits.

`Q<A>` is one live linear quantum owner. A tuple containing such an owner is
also linear, including an owner of zero physical width. Ordinary `Unit`, `Bit`,
`Bits<n>` and products containing only ordinary fields may be copied or dropped;
an owner must be
moved, returned or explicitly consumed under an admitted rule. Separate owners
do not imply separable quantum states. Exact shape, phase and reference
correlations remain obligations, not information inferred from variable names.

An `Op<A>` is a static endomorphic operation description, used through explicit
static parameters and arguments. It is not an ordinary runtime value and
contains no live quantum owner. Reusing a description does not duplicate its
input. For example, this existing form applies one static operation twice:

```qli
unitary fn twice[const U: Op<Bit>](q: Q<Bit>) -> Q<Bit>
requires Applicable(U) {
    U(U(q))
}
```

The inner application consumes q and returns the input for the outer one.
Writing two uses of the original q instead would violate ownership. This
fragment states a generic contract, not a closed CLI entry or proof about an
arbitrary supplied implementation.

Closed operation arguments can be materialized through ordinary helper calls
in the bounded finite Meaning adapter. Forward, adjoint and controlled access
retain the actual provider definition, exact argument tree and original Meaning
requests. Adjoint reverses the actual pure circuit and its exact phases;
controlled access retains conditional scalar phase even for `Q<Unit>`.
Structural split/join routing preserves ordered logical coordinates. Independent
source replay checks callee bindings, ordered actions and suspended caller owners.
Nested repetitions retain their child obligations even at zero count.

This path uses the existing exact pure Raw circuit profile and unchanged work,
depth, storage and wire bounds. Finer-than-eighth-turn phases, other unsupported
primitive forms and opaque provider assertions retain explicit target refusals.
The common source access requirements remain mandatory; neither a Unitary label
nor a Meaning annotation grants a missing capability. The selected route checks
every original request with the native checker before emitting a hierarchy
artifact. This is not a general source-preservation theorem or a full QS/PR/RS
or EXACT discharge.

### Admitted operation construction

The table gives the existing endomorphic common-source rules; the
[general pure-arrow rules](type-model.md#general-pure-operation-arrows) specify
separate ports and their current selected hierarchy implementation. Concrete
lowering eligibility still depends on the profile and retained evidence.
Finite provider materialization retains its refusal of explicit specialization
through this path. Selected hierarchy projection and bounded pure Raw
materialization retain ordered constructor trees and both exact ports. Finite
endomorphic Meaning requests apply to the whole tree and every annotated child,
including children under zero repetitions. Each request checks the actual Raw
artifact with Lean, then independently replays its source steps. Adjoint reverses
both ports; packed control and repetition still require endomorphisms. Unsupported
Raw primitives and rectangular Meaning equations remain separate profile limits.
A successful common judgment cannot replace the independent evidence required
by a profile.

| Form | Required interface and access |
| --- | --- |
| Resolved provider or explicit specialization | A permitted principal-Unitary `Q<A> -> Q<A>` provider with its checked static bindings and access; no runtime capture. |
| `then_op(U,V)` | The same exact basis A on both descriptions; sequential application on one owner. |
| `tensor_op(U,V)` | An ordered packed basis `(A,B)`; no implicit join of separate owners. |
| `adjoint(U)` | Requires Adjointable(U) to construct the description, then exchanges its Applicable/Adjointable availability; execution requires the transferred access. Mathematical unitarity alone supplies no API. |
| `controlled(U)` | Constructs a packed `(Bit,A)` description whose access derives from U's Controllable availability; use still needs the corresponding path and retains phase. |
| `power(U,n)` | A checked supported static count and the child's obligations, including when n is zero. |
| `conjugate_op(C,U)` | Exact common basis; access derives from C's Applicable and Adjointable availability together with the corresponding access to U. |
| `checked_op(implementation, Meaning)` | The existing declaration-identifier form and exact Meaning obligation described below. |

Composition compares full basis trees and static premises, not just bit widths.
Tensor order, Unit nodes and `Bit` versus `Bits<1>` remain distinct. Existing
Meaning refinements such as `Op<A,M>` keep their current Meaning slot; the
second slot is not a general codomain. This chapter admits no `Op<A,B>` arrow
extension or general user-defined static builder.

`then_op`, `tensor_op`, `adjoint`, `controlled`, `power` and
`conjugate_op` currently drop an attached Meaning refinement in the common
description judgment rather than prove automatic refinement transport.
Constructing a description is distinct from obtaining executable access to it.
Pending semantic obligations and concrete evidence remain separate; the spelling
of a composition cannot manufacture an exact refinement or its discharge.
`checked_op` retains its own explicit attachment/checking boundary.

An Op formal starts without executable access. `requires Applicable(U)`,
`Adjointable(U)` and `Controllable(U)` provide separate assumptions for checking that
generic declaration. One requirement grants neither of the others. Calls and
forwarded providers must satisfy their actual requirements; concrete bindings
still need their independently checked implementation paths. A runtime local,
spent value or quantum owner cannot become a static provider. Ordinary runtime
data cannot select a static size, provider or Meaning.

For the enabled endomorphic descriptions, write A(U), D(U) and C(U) for
`Applicable(U)`, `Adjointable(U)` and `Controllable(U)`. The following rules
derive available paths; constructing a description does not itself execute it.
An application or forwarded actual argument must establish the requested path.
An `adjoint(U)` description is well-formed only when D(U) is available. This
construction premise is checked before deriving the paths below, even inside
another description, an unused static actual, a dead source arm or a zero
power. It also applies to zero-width bases. A double adjoint therefore requires
both the original D(U) path and the A(U) path used as D of the inner adjoint.

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

These rules apply at count zero and on zero-width bases. For example, C(U)
alone permits application of the constructed `controlled(U)` description;
it does not permit the bare `U(q)`. The adjoint of a controlled implementation
and another control are built from its retained exact circuit, with phase
preserved. A black-box channel-equality assertion supplies no such circuit.
The adjoint of `controlled(U)` can use that constructed description's D path;
constructing `controlled(adjoint(U))` additionally requires the original D(U)
path. Outer control does not waive the bare adjoint's construction premise.
Composition currently drops the attached Meaning refinement in the common
judgment as specified above; the table does not infer a new refinement law.

A transparent ordinary provider must have an independently checked body with
principal Unitary effect and the required exact interface. Its Applicable path is
available after all declared actual-argument requirements are checked. Its
Adjointable path additionally requires both A and D for **every** actual Op
argument, including unused ones; its Controllable path requires all three
paths for every such argument. With no Op arguments these conjunctions are
empty, but body/effect/interface/materialization checks still apply. These are
conservative derivations, not a claim of maximal inference from arbitrary bodies.

Sealed gates retain their existing direct runtime interfaces. For direct
adjoint/control and `qif` targets, the common sealed profile permits
`std::quantum::{h,x,z,t,s,sdg,tdg,id,phase_eighth}` with all three paths. The first
seven require Bit; `id` and `phase_eighth` retain the actual target basis.
Other sealed primitives reject as direct transformed targets. A gate name
cannot be passed as a general static/host Op provider. An ordinary checked
wrapper supplies that provider interface; concrete lowering limits still apply.
Opaque/certified external providers remain unsupported in this
profile; a Unitary annotation or a Meaning alone cannot grant their paths.
Closed source Meaning evidence retains its actual provider, ordered interface,
source dependencies and independently checked implementation; replacement or
stale evidence cannot stand in for that binding. QPE controlled powers use
these same rules and the same phase-sensitive checking boundary.

[Checked operations](checked-operations.md) separates the common judgment's
pending Meaning-equality obligation from finite materialization. The latter
requires closed principal-Unitary declarations, retains source dependencies,
exact basis and ordered ports, and checks the implementation against the exact
finite Meaning through the selected native checker. An abstract formal cannot
bypass the closed-declaration refusal. Equal probabilities or equality up to
global phase do not establish that exact equation. Attaching a Meaning does
not grant inverse or controlled access.

Supported finite construction materializes explicit circuit/operation proposals
and retained evidence; the independent native gate checks the bound artifact.
Selected-source specialization has its own concrete eligibility rules.
Closed `checked_op` and Meaning-refined bindings use the all-binding native
gate described in the [type model](type-model.md#direct-runtime-transforms-and-opaque-operations).
Exact Unit/Bit/Bits/product quantum interfaces are retained; unsupported
constructors and ordinary runtime Bits materialization retain explicit refusals.
A successful common judgment
or pending obligation does not supply a missing emitter or an accepted handle.
The [type model](type-model.md#direct-runtime-transforms-and-opaque-operations)
also distinguishes existing direct runtime-group transforms from opaque
single-owner `Q<A> -> Q<A>` operations; this chapter does not merge them.

## Patterns, observation and Unit

Ordinary tuple and Unit patterns inspect the shape of an ordinary value. A
pattern over an ordinary product containing owners moves those fields under
the ownership rules; a wildcard cannot silently drop a quantum field.
Destructuring one `Q<(A,B)>` instead requires explicit `split`, and constructing
it from two owners requires explicit `join`. These structural maps preserve
ordered factors and reference correlations without observation or a
separability claim. Ordinary patterns do not inspect an unmeasured quantum
label.

[Coherent basis maps](coherent-basis.md) use
`basis input as pattern { expression }`. Their labels are ordinary basis data
in an isolated total computation. The injective map has coefficient `+1` on
each basis transition and acts linearly, including on entangled inputs. Copying
a label inside that map can create correlations; it does not copy an arbitrary
quantum state. The body is one restricted basis expression, not an ordinary
statement block, closure or measurement. Outer runtime captures reject.
Selected CoherentLift projection and finite quantum Unit limitations remain;
the source contract grants no unsupported emitter.

Physical information is obtained through an explicit observing operation such
as `measure_z`, which consumes its logical owner. Ordinary `if` requires an
ordinary `Bit` condition; coherent quantum control has its separate owner,
phase and access rules. Classical pattern matching, structural ownership maps
and physical observation cannot substitute for one another. General classical
ADTs and their match syntax are not currently implemented by this unit, and
they do not implicitly establish coherent quantum sum semantics.

Ordinary Unit is unrestricted singleton data. `Q<Unit>` is a linear owner of a
one-dimensional quantum system and can retain nontrivial scalar phase despite
having zero wires. Explicit `unit`, `finish`, structural maps and their profile
limits are specified in [Unit owners retain phase](type-model.md#unit-owners-retain-phase).
Returning ordinary Unit or omitting its transported result port cannot omit
argument/body work or erase scalar action already performed. Ordinary `()` is
neither implicit state preparation nor implicit quantum-owner elimination.

## Scoped bodies, finite elaboration and effects

`with_computed`, certified-computed and static-fold bodies are scoped compiler
constructs. Their binders do not create reusable callable values. Their checks
retain the live caller frame, linear use, inferred effects and applicable exact
cleanup obligations. This boundary does not prohibit those existing bodies or
weaken them into unrestricted closure capture.

The source admits its documented Nat-decreasing runtime self-calls, including
the specified direct runtime transforms. Every natural parameter must satisfy
the nonincrease requirement and at least one must strictly decrease under the
checked premises. Mutual dependency cycles, recursive opaque providers and
unproved decreases reject. Closed specialization and supported finite folds
elaborate under the existing work/storage limits. Zero-count construction does
not hide an invalid body or dependency. There is no general runtime lazy thunk,
bottom primitive or unrestricted recursive execution in accepted Core.

Names such as `Monad`, `Either`, `IO`, `bottom` and `undefined` supply no built-in
monad, sum, host effect or partial-value semantics. Where the ordinary lexical
and category rules permit, they can be ordinary user identifiers. An ordinary
function called `undefined`, for example, still needs a valid declaration and
body; its name grants no bottom semantics.
Symbolic descriptions and shared circuit structure do not imply lazy physical
execution. Exhausting a checking or elaboration budget rejects and establishes
neither a quantitative resource guarantee nor impossibility of the requested
mathematical property. Instance success is not a proof of an entire family.

Quantum effects remain `Unitary <= Isometry <= Observe`, with body/callee/argument
effects retained. An annotation cannot downgrade observation, reset or discard.
There is no generic quantum-core Monad interface or accepted `do/pure` syntax.
The Kleisli origin of the name does not supply one. Host filesystem, network,
device orchestration and other I/O remain outside this three-effect quantum
language; host tooling does not extend its effect lattice by implication.

## Boundary classification

These rules classify the fourteen boundary concerns of #80. They are language
contracts and stated implementation limits, not a declaration that its
acceptance checks or the broader feature Issues are complete.

| Concern | Current admitted boundary |
| --- | --- |
| Functional influence | Explicit contracts subordinate to the authority hierarchy; Rust/Haskell slogans are mnemonics. |
| Descriptions and owners | Static descriptions contain no live Q; each application retains linear ownership. |
| Higher-order abstraction | Existing endomorphic static formals, specialization and constructors with explicit access; broader arrows/builders remain candidates. |
| Closure capture | No general runtime closure/function value; scoped compiler bodies keep their own checks. |
| Pattern meanings | Ordinary patterns, explicit quantum structural maps and physical observation remain distinct. |
| Algebraic sums | No general ADT or coherent-sum admission here; future classical ADTs cannot silently define quantum sums. |
| Unit | Ordinary singleton versus zero-width quantum owner, with exact scalar phase retained. |
| Traits and laws | Current capability requirements and concrete evidence are separate; general trait/class syntax is not introduced. |
| Laziness, bottom and recursion | Eager calls, explicit finite Core and documented checked Nat decrease; no hidden deferred quantum work. |
| Currying and partial application | Full call arity; no reusable callable obtained by capturing an argument or owner. |
| Monad and effects | No general quantum Monad/do; principal Unitary/Isometry/Observe boundaries stay explicit. |
| Host I/O | Outside the current quantum effect lattice and accepted source surface. |
| False friends | Actual Qleisli diagnostics plus the explanations below; external qlippy integration is excluded. |
| Surface convenience | Finite explicit proposals, retained identity and actual independent checking; no fallback acceptance. |

## False friends and diagnostics

The removed `do p <- q; pure e` migrates to `basis q as p { e }`. `pure` does
not prepare a state, and the basis form is not monadic bind. The removed
`bind_op(implementation, Meaning)` migrates to the same arguments in
`checked_op`. The old spelling is not an alias, and the new one does not confer
constitutional certification. Both removals have actual located Qleisli
library/CLI diagnostics with text and JSON output.

Other refusals must retain their real stage: missing arguments fail arity,
local runtime values fail callable/provider category, consumed owners fail
ownership, exact type trees fail compatibility, missing operation access fails
capability checking, and false effect assertions fail semantic checking.
Unsupported concrete forms fail eligibility instead of gaining a weaker
route. A parser refusal for an unimplemented closure or ADT form does not prove
a later capture, match or semantic rule. This chapter explains the boundary;
it does not promise a specialized diagnostic for every absent grammar form.

In particular, ordinary classical matching does not measure Q, a zero-width
owner is not disposable ordinary Unit, probability agreement does not supply
exact phase equality, and an operation's Unitary label does not provide inverse
or controlled access. Diagnostic suggestions must not imply any of those
substitutions. External qargo/qlippy diagnostic integration is omitted under
the maintainer's explicit authorization. This chapter reports no updated
consumer support; actual Qleisli diagnostics remain required.

## Evidence identity and proof limits

Retained source and dependency snapshots, static bindings, provider/Meaning
identities and ordered ports remain part of evidence binding. A source rewrite
can therefore change artifact identity while preserving an intended exact
meaning. Reconstruct and independently check current evidence; do not remove
source bindings or reuse stale receipts to force byte equality. Historical
sources, counterexamples and real observations remain unchanged beside explicit
current derivatives.

The [operations design candidate](../design/operations.md), general builders,
broader arrow/capability systems, ADTs and linear closures remain under their
separate decisions and implementation work. This chapter adopts none of those
proposed extensions. The [production boundary](production-boundary.md)
distinguishes source judgment, concrete lowering, native acceptance and runtime
or emitted-artifact correspondence. Valid proposed IR alone is not a general
proof of source preservation.

QS, PR, quantitative RS and EXACT broader duties remain pending. The two
protected ordinary QLV1 decoded-root ownership/classical-scope guarantees
retain their exact recorded scopes, premises and current evidence obligations;
they are not enlarged into a guarantee of functional source abstraction.
This ordinary boundary decision changes neither those statuses nor edition
2026, and creates no release approval or proof discharge.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
