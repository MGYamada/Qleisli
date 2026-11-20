# Surface-to-core elaboration

An **elaboration** is the expansion of one surface form of a `.qli` program
into operations of an existing core representation. A surface form is a
construct as the program writes it, such as a call, a pattern or a fold.

This chapter specifies the convenience elaborations that edition 2026
permits. It gives a contract for each one. A contract names the surface form
and the target of the expansion. It states the evaluation order, the owners,
the exact phase and the source spans. It lists the refusals, and it lists the
obligations that the expansion leaves open. The chapter is subordinate to the
[authority hierarchy](authority.md).

The chapter introduces no syntax, no primitive, no implicit conversion, no
evidence authority and no supported emitter.

Rules:

- An elaboration may insert only the uniquely determined operations that its
  section describes.
- An elaboration must preserve five things: the evaluation order, the
  complete type trees, the logical owners, the exact phase and the original
  source attribution.
- An elaboration must not infer an arbitrary isomorphism, a permutation,
  cleanup, operator equality or an unavailable capability.

## Source and acceptance boundary

This section names the check that comes before elaboration and the check
that decides acceptance after it.

The **common checker** applies the [common source judgment](source-text.md)
to the complete original AST of a program. Elaboration comes after this
judgment.

A **target** is an existing representation that an expansion produces. Three
targets exist, and they are distinct:

| Target | Proposals that it produces |
| --- | --- |
| **Finite project** | Finite Raw and QIRF proposals |
| **Selected Raw** | Selected-source Raw proposals |
| **Selected hierarchy** | Selected hierarchy and finite-leaf proposals |

The Target field of a contract identifies an existing representation on one
or more of these targets. It does not claim that one canonical typed Core or
one converged emitter has replaced them. Each target supports a bounded
**profile** of programs.

The **native checker** is the checker executable that `lean-kernel/` builds.
It decides whether a proposal is accepted. It decides this independently of
the component that produced the proposal.

Rules:

- The common checker checks every declaration, both arms of every branch and
  the body of a fold with zero iterations.
- Static bindings and immutable facts are inputs to concrete elaboration. They
  are not accepted handles of the native checker.
- A supported surface form may have an unsupported projection or target. A
  failure must not select a weaker checker.
- Every resulting artifact, dependency and independent request must pass the
  [production gate](production-boundary.md) that applies to it.
- Handwritten IR and generated IR have the same requirements for independent
  acceptance.
- Four activities confer no acceptance: Rust normalization, source checking,
  source-step comparison and proposal generation.
- Valid output alone does not prove source preservation.

> **Implementation note.** The common checker is `src/frontend/check.rs` with
> the modules under `src/frontend/check/`. The Rust frontend parses, reports
> diagnostics and generates proposals. It issues no acceptance.

## Whitelist

The whitelist names every surface form that has an elaboration contract in
this chapter. Literal values, sealed operations and explicit structural maps
keep their separate [type](type-model.md) and
[primitive](primitive-boundary.md) contracts. An implementation detail or an
Issue candidate does not enlarge the whitelist.

| Surface form | Permitted expansion | Section |
| --- | --- | --- |
| Runtime products, patterns and ordinary calls | Binding of the exact value tree, and expansion of the checked body of the callee | [Runtime products, patterns and calls](#runtime-products-patterns-and-calls) |
| Whole-owner `excl` calls | One checked consuming call. The same lexical binders retain the returned values. | [Whole-owner exclusive calls](#whole-owner-exclusive-calls) |
| Static indexed access and slice access | An ordered partition, one checked call, and reconstruction from the updated selected owners | [Static ordered-axis places](#static-ordered-axis-places) |
| Ordinary Boolean expressions and `classical fn` calls | Eager operations on ordinary values | [Ordinary expressions and classical functions](#ordinary-expressions-and-classical-functions) |
| Enum values, record values and `value.field` | Ordinary values that keep their nominal type | [Nominal values](#nominal-values) |
| Runtime classical `if` | Classical branches, with complete joins of the result and the frame | [Runtime classical branches](#runtime-classical-branches) |
| Ordinary `match` | Classical branches on the enum tag, with complete joins of the result and the frame | [Ordinary match](#ordinary-match) |
| Static naturals, aliases and bounded helpers | Exact checked substitution, with no runtime instruction | [Static natural computation](#static-natural-computation) |
| Bracket specialization and `if static` | Closed checked instances and the selected arm | [Specialization and static selection](#specialization-and-static-selection) |
| `for static` and `qfor static` | Explicit threading of the carry over a closed finite range | [Finite folds](#finite-folds) |
| Static operation descriptions and application | Operations bound to their providers, and checked transformation proposals | [Operation descriptions and application](#operation-descriptions-and-application) |
| `controlled(U)(c,q)` and two-arm `qif` | The exact controlled action, which retains the inactive identity action | [Coherent control](#coherent-control) |
| `qmatch(s,q) { label => arm, ... }` | The exact selected action on the target, with one arm for each selector label | [Exact-label coherent selection](#exact-label-coherent-selection) |
| `basis q as p { e }` | The specified coherent lift with the coefficient `+1` | [Coherent basis maps](#coherent-basis-maps) |
| Existing `with_computed` forms | The checked construction of compute, use and uncompute | [Computed workspace](#computed-workspace) |
| `apply_contract(F, S, q)` | One application of the implementation `F`, with a checked obligation of function equality against `S` | [Function contracts](#function-contracts) |

The whitelist is not a list of every accepted surface form.
[Status and limits](#status-and-limits) names the accepted forms that this
chapter does not specify.

Each entry has one section. The section gives a description, a contract table
and examples. Every contract table has the same eight fields:

| Field | Content |
| --- | --- |
| Source | The surface form that the entry covers |
| Target | The representation that the expansion produces |
| Evaluation order | When each part of the form evaluates |
| Owners | The quantum owners that the form consumes and returns |
| Exact phase | The action, with its phase, that the expansion must keep |
| Source spans | The original locations that the expansion retains |
| Refusal | The programs that the form rejects |
| Open obligations | The requirements that the expansion leaves to independent checks |

The last field states requirements. It discharges no guarantee and adds no
ledger entry. The linked Reference sections specify the detailed grammar, the
capabilities and the profile limits.

Each example says which check accepts or rejects the program.
[Diagnostics and recovery](diagnostics.md#routes) defines the project route,
the selected-entry route and the [codes](diagnostics.md#codes) of each. An
example that names the common checker gives the class of the failure in that
checker.

## Runtime products, patterns and calls

A runtime product is an ordered tuple of runtime values. A `let` pattern or a
parameter pattern binds the leaves of such a value. An ordinary call binds its
arguments to the parameters of a resolved function and expands the checked
body of that function.

| Field | Contract |
| --- | --- |
| Source | Ordered runtime products, `let` patterns and parameter patterns, and resolved calls of ordinary functions |
| Target | Bindings of the exact value tree and the checked body of the callee, as Raw operations or as supported selected source steps |
| Evaluation order | Each right-hand side and each argument evaluates completely, once, from left to right, before binding. An argument list is not one automatically packed tuple. |
| Owners | Each quantum leaf moves once. Destructuring `(Q<A>,Q<B>)` never splits `Q<(A,B)>`. The expansion preserves pending arguments and the suspended owners of the caller. Ordinary leaves may be copied or ignored. |
| Exact phase | Binding, grouping and call expansion insert no gate and no phase. The expansion preserves the action of the callee and its ordered interface. |
| Source spans | The expansion keeps the original spans of the parameter, the right-hand side and the call. A failure of an argument identifies the argument or the call. Emitted operations of the callee retain their origins in its original body. |
| Refusal | A mismatch of the exact arity or tree; duplicate names within one pattern or parameter list; a wildcard, an implicit drop or a reuse of a live quantum owner; an unresolved callee; an invalid body; an unsupported projection. Ordinary runtime shadowing keeps its lexical rules. |
| Open obligations | The emitted ownership, scope and effect rules and the dependencies need an independent check. Call expansion needs correspondence with the original body. The validity of fresh IR alone does not supply it. |

See [exact trees](type-model.md#structural-equality-coherence-and-physical-maps)
and [functional abstraction](functional-boundary.md).

The project route rejects this function. `split(q)` returns
`(Q<(Bit,Bit)>,Q<Bit>)`, and the pattern `(a,b)` does not split the owner
`Q<(Bit,Bit)>`:

```qli
unitary fn run(q:Q<((Bit,Bit),Bit)>)->Q<((Bit,Bit),Bit)>{ let ((a,b),c)=split(q); join(join(a,b),c) }
```

The project route accepts the function with a second explicit `split`:

```qli
unitary fn run(q:Q<((Bit,Bit),Bit)>)->Q<((Bit,Bit),Bit)>{ let (ab,c)=split(q); let (a,b)=split(ab); join(join(a,b),c) }
```

## Evaluation and owner lifetime boundaries

This section states when the parts of an expression evaluate and where the
lifetime of a quantum owner may end.

An **access call** is a call that marks at least one argument with `excl` or
`ctrl`. A **place** is such a marked argument. It is a whole lexical owner,
or a static selection of the axes of one.

### Evaluation order

Statements, arguments and tuple fields evaluate in the order in which the
source writes them.

Rules:

- For every supported expression form, statements execute in source order.
- A call evaluates its arguments completely, once, from left to right, before
  it enters the callee.
- Tuple fields follow the same rule. A nested expression evaluates before the
  operation that encloses it.
- An ordinary Unit result does not suppress the effects of an argument.
  `(h(excl q), z(excl q));` finishes H before it starts Z, just as
  `h(excl q); z(excl q);` does.
- Ignoring a product of ordinary Unit values inserts no quantum destruction.

### Owner lifetime

The rules below say when a temporary owns a quantum value, and what the end
of a scope does to a live owner.

Rules:

- A temporary may own a quantum value while that value flows to an explicit
  consumer, a binding or a result. `measure_z(h(init0()))` is such a chain.
- The end of an expression statement, a wildcard binding, a shadowed binding
  or a local block must not silently destroy a live quantum owner. The
  checker rejects an unreturned local owner at its binding. It rejects a
  discarded quantum expression at that expression. Both routes report the
  code `ownership`.
- Ordinary Bit, Unit and product values may be ignored.
- The language has no observable classical destructor and no quantum drop
  glue.
- The exit from a scope cannot choose measurement, discard, reset or clean
  discharge for the programmer.

### Places and access calls

The rules below say what a place is and when the caller can use its owners
again after an access call.

Rules:

- A place is formed by its call. It is not a reference value with an inferred
  lifetime.
- An access call supplies its owners in argument order and executes the callee
  once.
- The call restores the lexical operation rights only after it retains the
  returned values and completes any reassembly of a selected parent. This
  happens before the next argument, tuple field or statement starts.
- A call inside the body of the callee completes before the enclosing call
  returns.
- The end of a surrounding block preserves the updated outer owner. It does
  not restore an earlier state.
- Four forms are unsupported: stored or escaping views, nested place
  projections, implicit method autoref and arbitrary reference lifetimes.
- A static axis selector uses the original resolved static context and has no
  runtime effect.
- A shorter lifetime grants no control capability, restores no dirty
  workspace and proves no clean release. The distinct obligations for
  effect, sector and exact workspace apply. These rules supply no workspace
  syntax and no evidence.

### Order of operations

The rules below say what elaboration retains of the written order, and what
a reordering needs.

Rules:

- Elaboration retains the ordered source steps, the call boundaries, the
  original owners and the source locations. Raw instructions retain the
  ordered edges of their owner tokens.
- Scheduling convenience does not permit a reorder of operations that do not
  commute. Neither do names that appear to be separate.
- A proposed reordering needs a separately justified transformation that
  preserves exact phase, reference behavior and all applicable contracts.
- Source evaluation follows the written order. A transformation of executable
  code requires its own evidence for the changed owner flow and for the other
  contracts.

> **Implementation note.** Independent source replay rejects an altered gate
> chain even when the type, effect and ownership interface of that chain is
> native-valid.

### Examples

The Finite project target and the Selected Raw target accept this program.
Each target emits the same Raw program as it emits with `h(excl q); z(excl q);`
in place of the tuple statement. `main` returns 1 with probability one:

```qli
use std::state::init0;
use std::gate::x; use std::gate::cnot; use std::gate::z;
fn done(a:Unit,b:Unit)->Unit{()}
unitary fn pair(q:Q<Bit>)->Q<Bit>{h(excl q);z(excl q);q}
pub observe fn main()->Bit{let q=init0();(h(excl q), z(excl q));h(excl q);measure_z(q)}
```

The project route rejects the next program with the code `ownership`. The
binder `q` holds a live owner at the end of the block:

```qli
use std::state::init0;  use std::gate::x; use std::gate::z;
observe fn main() -> Unit { let q = init0(); () }
```

## Whole-owner exclusive calls

A whole-owner exclusive call lets a program transform an owner and keep its
name. A call such as `h(excl q)` supplies the live lexical owner `q` to one
consuming call. The same binder then retains the returned quantum value.

| Field | Contract |
| --- | --- |
| Source | `U(excl q)`, or a call whose arguments all mark distinct whole lexical `Q<A>` owners. A retained concrete `ctrl` call is admitted after a fresh native sector check, on the targets that [Status and limits](#status-and-limits) names. |
| Target | The consuming call. After it, the value of each argument binder is replaced by its exact ordered returned owner. The access expression returns ordinary Unit. |
| Evaluation order | The expansion resolves the original source occurrences. It supplies the owners once, in argument order, and the callee executes once. A copied AST occurrence acquires no second lexical identity. |
| Owners | The same lexical owner identities hold the returned values. The form requires three things: a checked Unitary effect that the caller can see, an independent check of the body, and the exact original owner interface. A later consuming call makes its binder spent. A shadow cannot restore it. |
| Exact phase | The expansion preserves the complete action of the callee, including entanglement, ordered axes and zero-width phase. It inserts no inverse and no cleanup. |
| Source spans | The expansion retains the original identifiers of the callee and of the arguments, their byte spans and the origins in the body of the callee. The span of a contextual marker does not replace the span of an owner identifier. |
| Refusal | Overlap; a spent, hidden or nonquantum argument; a changed owner partition or tree; a nonunitary body; mixed arguments outside the [checked profile](#ordinary-unit-arguments-in-access-calls); an escaping access; a failed native check of the control sectors; an unavailable concrete projection. Static selections follow [their own rule](#static-ordered-axis-places). Checker-free `ctrl`, which is `ctrl` in a lowering that runs without the native checker, is unsupported. An original control obligation without a concrete interval in each retained specialization rejects. |
| Open obligations | Emitted artifacts and requests need independent checks. The lookup-level scope-update model has premises on finite maps, type embedding and update provenance. It is not a proof of source preservation and not a quantitative resource certificate. General footprints, lifetimes and access declarations are pending. |

See [whole-owner exclusive calls](rust-boundary.md#whole-owner-exclusive-calls).

The effect of the callee follows the
[public-effect rule](source-text.md#ordinary-function-effects-and-assertions).
The effect that counts depends on the module that contains the call.

Rules:

- Outside the original module of the callee, the checked public contract
  counts. Inside that module, internal inference counts.
- A body can have a sharper effect than its public contract. Specialization,
  inlining and cache reuse cannot turn that sharper effect into eligibility
  for external source.

> **Implementation note.** Native-checked Selected Raw lowering also checks
> unused closed functions that lead to control obligations. It invents no
> static bindings.

The project route rejects this program with the code `contract`. `h` does
not preserve the computational-basis sectors of `q`, and the check covers
`bad` although no function calls it:

```qli
use std::state::init0;
use std::gate::x; use std::gate::cnot;
unitary fn bad(q:Q<Bit>)->Q<Bit>{h(ctrl q);q} pub observe fn main()->Bit{0}
```

### Ordinary Unit arguments in access calls

An access call can take ordinary arguments beside its marked places. A
checked mixed call passes `()` or a lexical `Unit` value beside its marked
places.

Rules:

- The call evaluates the original arguments once, in their written order. It
  reserves a marked owner when it reaches that argument.
- A later argument must not use a reserved owner as an ordinary value.
- A quantum owner such as `Q<Unit>` needs an access marker and an ownership
  check, like every other owner.
- The named callee receives the complete ordered value list, including each
  `Unit` at its source position.
- The independently checked Raw interface carries only the marked quantum
  ports.
- The callee returns those owner types in their original relative order. The
  call restores them to their original places and returns ordinary `Unit`.
- The checked operation retains its exact phase and the same interface to
  untouched owners.
- An exclusive named call may also take ordinary `Bit` arguments when the
  selected callee lowers to a single checked ordinary branch.

The selected-entry route with the native checker accepts `update`:

```qli
unitary fn turn(tag: Unit, data: Q<Bit>) -> Q<Bit> { h(data) }

pub unitary fn update(data: Q<Bit>) -> Q<Bit> {
    turn((), excl data);
    data
}
```

> **Implementation note.** The native source-body check validates the named
> call, the returned owners, the Raw interval and any extraction and
> reinsertion. For an access body without selection, basis or Meaning
> evidence, it requires an original access receipt and complete coverage of
> the selected invocation; see
> [the native scope](production-boundary.md#version-5-source-body-requests). For
> ordinary `Bit` arguments, it uses the original condition and both Raw arms.
> It verifies each parked owner in both arms and at the checked branch
> return, and it preserves port order and zero-width owners. The dormant
> checker admits a mixed `ctrl` call from a closed nongeneric body after the
> native source check covers that exact original occurrence. It checks the
> marked quantum sectors of the callee again.

### Declared access parameters

A function can write the access marker in its own signature. A finite
function with a closed selected specialization may declare a marked owner
slot, as in `target: excl Q<Bit>`, and write a `Unit` result.

Rules:

- The call must supply the exact marker at that argument position.
- The body must check as Unitary and must leave each marked owner live on its
  original binder.
- The ordinary result is `Unit` at the written call. The body may return `()`
  or a value of type `Unit`, including a parameter.
- The returned quantum owners carry the updated state, including its exact
  phase.
- A declared access requires the finite check of the original body. For
  every `ctrl` slot it also requires the applicable exact sector check.

The selected-entry route with the native checker accepts `update`:

```qli
pub unitary fn flip(target: excl Q<Bit>) -> Unit {
    h(excl target);
    ()
}

pub unitary fn update(target: Q<Bit>) -> Q<Bit> {
    flip(excl target);
    target
}
```

> **Implementation note.** The native call boundary reads the marked owners in
> parameter order and verifies the returned Raw ports. The production source
> check retains the declaration and the marked call as original occurrences.
> When it checks a specialization, it also retains explicit static arguments
> such as `type(Bit)`.

## Static ordered-axis places

A static ordered-axis place lets an access call act on selected axes of a
register. It selects axes of a live `Q<Bits<N>>` owner as an argument of the
call. That owner is the **parent**. `excl q[i]` and `ctrl q[i]` select one
axis. `excl q[a..b]` and `ctrl q[a..b]` select the explicit half-open range
`q[a..b]`.

| Field | Contract |
| --- | --- |
| Source | `excl q[i]`, `ctrl q[i]`, `excl q[a..b]` and `ctrl q[a..b]` as arguments of an access call, where `q` is a live lexical `Q<Bits<N>>` parent. An index selects `Q<Bit>`. A range selects `Q<Bits<b-a>>`. The two interfaces are distinct even at width one. |
| Target | Three steps. The expansion partitions the parent, in order, into selected owners and remainder owners. It calls the callee once with all selected arguments. It reconstructs the parent from the updated returned values, in the reverse of the extraction order. Existing Split/Join instructions perform the partition on the Finite project and Selected Raw targets. The Selected hierarchy target uses its operations for bit extraction, reinsertion and empty owners. |
| Evaluation order | A selector uses the original resolved static context and has no runtime effect. The callee executes once. The parent is reassembled before the next argument, tuple field or statement starts. |
| Owners | The parent is live after the call, and the access expression has ordinary Unit type. The callee has a Unitary effect and returns the exact ordered selected interface. Empty selected owners and empty remainder owners retain their logical identities. An empty range selects no axes. A whole-owner access overlaps every other access on that parent, including an empty range. |
| Exact phase | The partition inserts no physical SWAP, preparation, measurement or cleanup. Empty owners retain their scalar phase. The expansion preserves the action of the callee on the ordered selected interface. |
| Source spans | Each selection retains its parent-owner occurrence, its static selector, its access role and the original byte spans. |
| Refusal | A parent that is not a live lexical `Q<Bits<N>>`; a bound that the common checker cannot prove, `0 <= a <= b <= N` for a range or `0 <= i < N` for an index, under the original static context; two selections on the same parent that are not provably disjoint; a runtime index; arithmetic overflow; budget exhaustion; a callee without a Unitary effect; a callee that does not return the exact ordered selected interface; bare indexing as a value or as an ownership-extraction operation; a `ctrl` selection without its sector check; checker-free control emission. Each failure occurs at compile time. No runtime bounds panic exists. |
| Open obligations | The emitted program needs native Raw checking. A `ctrl` selection needs a fresh native sector check of the concrete callee on its ordered selected ports. General source preservation and quantitative resource correspondence are proof obligations. |

Rules:

- Different parent names alone are not evidence of different axes. The checks
  use resolved binding identities.
- `ctrl` keeps its separate original sector obligation. The annotation grants
  no permission.
- The common checker checks every original declaration, both branch bodies
  and the body of every fold.
- The premises of static branches and of loops take part in the arithmetic
  proof. This includes impossible contexts, as for other static obligations.
- The checks of names, types, effects and ownership cover unexecuted code as
  well.

> **Implementation note.** The common AST represents each selection as a
> parent-owner occurrence and a static selector. The project compiler submits
> its emitted program to native Raw checking. The selected path also replays
> source steps against the partitions and the reassembly. A dormant action
> with closed ports can be checked without evaluating the register extraction
> of an inactive branch. On the Selected hierarchy target, source replay
> checks the original ordered ports of each partition and the phase-free graph
> interval. For supported pure `ctrl` calls, replay binds the original ordered
> call interval in that same graph. Lean checks the sectors of the exact
> action during the invocation that checks the executable hierarchy.

The [bounded resource correspondence](realization.md#exclusive-access-and-generated-work)
counts the live wires of the indexed Raw access and its reassembly. The
selected operation and any emitted physical implementation have their own
resource checks.

The common checker accepts this function:

```qli
use std::gate::cnot;pub unitary fn f(q:Q<Bits<2>>)->Q<Bits<2>>{cnot(ctrl q[0],excl q[1]);q}
```

The selected-entry route rejects the next program with the code `size`. Index
2 is outside `Q<Bits<2>>`, and the check covers `unused` although no function
calls it:

```qli
unitary fn unused(q:Q<Bits<2>>)->Q<Bits<2>>{h(excl q[2]);q}pub unitary fn f(q:Q<Bit>)->Q<Bit>{q}
```

## Ordinary expressions and classical functions

This section covers the classical computation of a program. An ordinary
expression computes a Unit, Bit or product value. A `classical fn` is a total
function on ordinary values.

| Field | Contract |
| --- | --- |
| Source | Ordinary expressions of Unit, Bit or product type, the eager operators `not`, `and` and `xor`, and supported calls of a `classical fn` |
| Target | Ordinary evaluation and Raw classical operations, including selected Raw register transport where the target supports it. No truth table is substituted at runtime. |
| Evaluation order | Operands and complete arguments evaluate once, in source order. `and` is eager, including its right operand. |
| Owners | An ordinary result has no quantum owner. Input expressions keep their effects and their quantum consumption. Ignoring a result cannot omit its measurement. |
| Exact phase | Ordinary Boolean evaluation inserts no quantum action. Input expressions keep their complete action or instrument. |
| Source spans | The expansion keeps the original byte spans of the operand, the call, the parameter and the definition. |
| Refusal | Wrong exact types or arity; a forbidden capture; an invalid classical body or dependency; unavailable transport. A live `Q<A>` is not an ordinary `A` argument. |
| Open obligations | Lexical use, complete phi inputs and value operations need a check. The original computation and the surrounding instrument must be preserved. Coherent use needs the separate lift obligation in addition. |

See [classical declarations](source-text.md#total-classical-declarations)
and [ordinary Bits transport](type-model.md).

The Finite project target and the Selected Raw target accept this program.
Both measurements run in source order, although `left` ignores `b`:

```qli
use std::state::init0; use std::gate::x;
classical fn left(a: Bit, b: Bit) -> Bit { a }
pub observe fn main() -> Bit { left(measure_z(x(init0())),measure_z(init0())) }
```

## Nominal values

A nominal value is an ordinary value of a declared `enum` or `struct` type.
`Type::Variant` names a fieldless enum variant.
`Type { field: expression, ... }` constructs a record. `value.field` projects
one field of an ordinary record.

| Field | Contract |
| --- | --- |
| Source | Fieldless `Type::Variant`, explicit `Type { field: expression, ... }` and ordinary `value.field`, in runtime blocks and in classical bodies |
| Target | Ordinary values that keep their nominal type. A variant becomes one Raw classical constant for each tag coordinate. A record keeps its field values in declaration order. A projection selects the stored field. |
| Evaluation order | Record initializers evaluate in written order. The record type keeps declaration order. A projection evaluates its receiver once. |
| Owners | Every field has an ordinary finite type. `Q<Record>` is one owner, with no implicit decomposition or observation. Initializer calls keep their ownership transitions. |
| Exact phase | Construction and projection are ordinary computation and insert no quantum action. Initializer calls keep their effects and dependencies, so observation cannot hide behind a Unitary or Isometry annotation. |
| Source spans | Type references use the original occurrence table, including public reexports and local shadowing. Member names and diagnostics retain their original source spans. |
| Refusal | A missing or repeated field; a field value of another type; a private field outside its declaring module; a projection from a value that is not an ordinary record; a local Basis name or runtime name in place of a global type with the same spelling; a payload variant; an imported bare variant; shorthand, record update and method forms. |
| Open obligations | Common preparation supplies no accepted handle. Execution requires a typed native route. That gate does not prove original AST lowering, the decoder and native compiler, or numerical runtime preservation. |

The [type model](type-model.md#opaque-basis-specialization-in-the-selected-profile)
specifies these forms and their routes.

The project route accepts this program. The initializers of `Result` are
written in an order other than the declaration order:

```qli
enum Tri { Zero, One, Other }
struct Empty {}
struct Result { choice: Tri, flag: Bit, empty: Empty }

pub observe fn main() -> Result {
    let q = basis unit(()) as _ { 0 };
    let bit = measure_z(h(q));
    let tag = if bit { Tri::One } else { Tri::Zero };
    let flag = match tag { Tri::Zero => 0, Tri::One => 1, Tri::Other => 0 };
    Result { empty: Empty {}, flag: flag, choice: tag }
}
```

With `pub unitary fn main` in place of `pub observe fn main`, the project
route rejects that program with the code `effect`.

## Runtime classical branches

A runtime classical branch selects one of two arms by an ordinary Bit, such
as a measurement result. Runtime selection is distinct from coherent control
and from static selection.

| Field | Contract |
| --- | --- |
| Source | `if condition { ... } else { ... }` with an ordinary Bit condition |
| Target | Raw `ClassicalBranch` with both operation lists and simultaneous classical and quantum phis, or the supported selected branch representation |
| Evaluation order | The condition evaluates once. Runtime executes the selected arm. Source checking visits both arms. |
| Owners | Both arms agree on the exact returned trees and on outer consumption. The join merges the returned leaves and the complete surviving frame of the caller and of pending arguments. IDs are globally fresh across arms. Phi renaming prepares no state and loses no reference correlation. |
| Exact phase | The expansion preserves the action and the unnormalized outcome weight of each arm. It inserts no coherent superposition and no branch normalization. |
| Source spans | The operations of an arm retain their original spans and their nested branch-index paths. An inserted join uses the span of the branch. |
| Refusal | A quantum condition; different types or owner frames; lost branch-local owners; invalid phis or an invalid body; an unsupported target. |
| Open obligations | Both arms, the scope, the ownership and the simultaneous phis need a native check. The complete source instrument must be preserved, with external references and the correlations of the caller frame. |

The Finite project target accepts this program, and `main` returns 1. The
selected-entry route rejects it with the code `unsupported`: the form is
valid, and its selected projection is outside the profile.

```qli
use std::state::init0;
use std::gate::x; use std::gate::cnot;
pub observe fn main()->Bit{
let q=init0();let u=if 1{x(excl q);()}else{()};measure_z(q)}
```

The project route rejects the next program with the code `type_mismatch`. The
condition is a quantum owner:

```qli
use std::state::init0;  use std::gate::x; use std::gate::z;
observe fn main() -> Unit { let q = init0(); if q { () } else { () } }
```

## Ordinary match

An ordinary `match` selects one arm by the variant of an ordinary enum value.

| Field | Contract |
| --- | --- |
| Source | `match value { Type::A => expression, ... }` on an ordinary enum value. Every declared variant occurs exactly once, as an exact qualified label. A runtime arm is an expression or a block. A classical arm is an ordinary expression. |
| Target | Ordinary comparisons of the tag coordinates, and nested Raw `ClassicalBranch` operations with their joins |
| Evaluation order | The scrutinee evaluates once. Runtime executes the arm of its variant. The common checker checks every arm, including the arms of a constant constructor in an unused function. |
| Owners | The scrutinee is an ordinary enum value. All arms return the same complete type tree and preserve the same outer owner frame, including zero-width owners. |
| Exact phase | The tag comparison is ordinary computation and inserts no quantum action. Each arm keeps its dependencies and effects. A constant scrutinee cannot hide an observing arm behind a pure public label. |
| Source spans | Labels resolve through their original type declarations and visibility. Member names and diagnostics retain their original source spans. |
| Refusal | A scrutinee that is not an ordinary enum, including a live `Q<T>`; a missing or repeated variant; a label of a foreign enum, even with equal spelling, width or cardinality; a wildcard, payload or complement pattern; more than 64 arms; arms with different type trees or owner frames; an unsupported target. |
| Open obligations | The source judgment provides no accepted handle. Execution requires a typed native route. Neither route provides implicit measurement or a source-preservation theorem. |

The [type model](type-model.md#opaque-basis-specialization-in-the-selected-profile)
specifies the form. Parenthesize a record literal in a scrutinee, so that its
braces differ from the arm list.

The project route accepts this program, and `main` returns 1:

```qli
enum Tri { A, B, C }
classical fn flag() -> Bit {
    match Tri::C { Tri::A => 0, Tri::B => 0, Tri::C => 1 }
}
fn main() -> Bit { flag() }
```

The project route rejects the next program with the code `type_mismatch`. The
`match` omits two variants, and the check covers `unused` although no
function calls it:

```qli
enum Tri { A, B, C } classical fn unused() -> Bit { match Tri::A { Tri::A => 0 } } fn main() -> Bit { 0 }
```

## Static natural computation

Static natural computation evaluates natural expressions during checking. A
program uses it for values such as a width or a repetition count. A static
binding is not a runtime value.

| Field | Contract |
| --- | --- |
| Source | Supported natural expressions, `static let`, and Nat helpers that are provisional, bounded and acyclic |
| Target | Exact affine templates, substitution and closed checked naturals. A checked unused alias inserts no runtime instruction. |
| Evaluation order | Ordered static binders and helper arguments resolve in their static context. Substitution is simultaneous. The names of a callee cannot rewrite the binders of its caller. |
| Owners | None. The static environment contains no live quantum owner and no runtime input. |
| Exact phase | Normalization inserts no phase. A result that an explicit phase operation uses is the exact specified parameter of that operation. |
| Source spans | The expansion keeps the original spans of the arithmetic, the argument, the premise and the binder. It never keeps spans of generated replacement text. |
| Refusal | A value that depends on a runtime value; a forward kind dependency; a duplicate or shadowing binding; nonlinear arithmetic; an unproved subtraction or premise; a cycle; overflow; work exhaustion. Acyclic forward references to helpers keep normal declaration resolution. |
| Open obligations | Closed values and their uses need a check under exact constraints. The work counters of the compiler do not certify the resources of a program. |

See [static arithmetic and helpers](static-language.md).

The Finite project target accepts this program. The alias `width` is checked
and erased, and `main` returns 0:

```qli
pub observe fn main()->Bit{static let width=2+1;0}
```

Both routes reject the next program. The static alias `n` depends on the
runtime value `a`:

```qli
pub observe fn main()->Bit{let a=1;static let n=a+1;0}
```

## Specialization and static selection

Bracket specialization closes a declaration by supplying its complete static
arguments, as in `run[2]`. `if static` selects one arm by a static
comparison.

| Field | Contract |
| --- | --- |
| Source | Ordered `const` parameters, complete bracket arguments and `if static comparison` |
| Target | A supported closed instance and the selected static arm, after the complete check of the original source |
| Evaluation order | Explicit static bindings and provider identities resolve before runtime application. Static selection evaluates no runtime condition. |
| Owners | The expansion preserves the exact interface and the owners of the runtime instance. A dead source arm is checked. |
| Exact phase | The substitution of parameters does not quotient phase and does not change axis order. The expansion retains the selected action. |
| Source spans | The expansion keeps the spans of the definition, the argument, the comparison and the arm. |
| Refusal | Incomplete or wrong bindings; unproved constraints or access; an invalid dead arm; non-decreasing dependencies; an unsupported instance. No inference from width and no fallback exists. |
| Open obligations | The closed artifact and the provider evidence need a native check. General preservation under specialization and resource bounds for a family are separate obligations. |

The [static rules](static-language.md) specify termination and capacities.
Helper spellings are provisional where those rules say so.

The project route accepts this program. `run[0]` selects the `else` arm and
`run[2]` selects the first arm, so `main` returns `(0,1)`:

```qli
use std::state::init0; use std::gate::x;
unitary fn flip[const n:Nat](q:Q<Bit>)->Q<Bit>{qfor static i in 0..n carry q=q{yield x(q);}}
unitary fn apply[const V:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(V){V(q)}
unitary fn run[const n:Nat](q:Q<Bit>)->Q<Bit>{
  if static n>=1 {apply[flip[n-1]](q)} else {q}
}
pub observe fn main()->(Bit,Bit){(measure_z(run[0](init0())),measure_z(run[2](init0())))}
```

The selected-entry route rejects the next function with the code `name`. The
dead arm calls an unknown function:

```qli
pub unitary fn f(q: Q<Bit>) -> Q<Bit> { if static 0 == 0 { q } else { missing(q) } }
```

## Finite folds

A finite fold repeats its body over a closed static range and threads a
carry from each iteration to the next. `for static` carries ordinary values.
`qfor static` carries quantum owners.

| Field | Contract |
| --- | --- |
| Source | `for static` for ordinary values or `qfor static` for quantum owners, with an explicit range, carry pattern, initializer and `yield` |
| Target | Closed finite iteration of existing fold and source steps, then a supported Raw or hierarchy proposal |
| Evaluation order | The initializer evaluates once. The carry threads in increasing index order over `[start,end)`. Zero iterations return the evaluated initial value. |
| Owners | The expansion preserves the exact carry tree. `qfor` carries a quantum owner, including empty-width owners. An owner outside the carry cannot be a hidden capture. The expansion inserts no discard at exit and no reassembly. |
| Exact phase | Serial composition retains the phase of every iteration. An empty iteration sequence is the identity on the retained carry. |
| Source spans | The expansion keeps the spans of the bound, the carry, the body and the yield in every instance. |
| Refusal | An invalid range or a runtime bound; the wrong fold category; a carry-tree mismatch; a missing `yield`; a hidden capture; an invalid zero-count body. A limit failure keeps its category. |
| Open obligations | The complete composition, the owners and the dependencies need a check. Finite unrolling proves neither a general family theorem nor a quantitative bound. |

See [fold rules](static-language.md#static-branches-folds-and-termination).

The selected-entry route accepts this function for `n` from 0 to 3. At
`n = 0` the function acts as the identity:

```qli
use std::gate::x; pub unitary fn f[const n:Nat](q:Q<Bit>)->Q<Bit>{qfor static i in 0..n carry a=q{yield x(a);}}
```

The selected-entry route rejects the next function with the code `type`. An
ordinary fold cannot carry a quantum owner:

```qli
pub unitary fn f(q:Q<Bit>)->Q<Bit>{for static i in 0..0 carry a=q{yield a;}}
```

## Operation descriptions and application

A static operation description names an operation that is bound to its
provider. A constructor builds a description from other descriptions, such
as the adjoint of an operation or a power of it. An application applies a
description to runtime owners.

| Field | Contract |
| --- | --- |
| Source | `adjoint`, `power`, `then_op`, `tensor_op`, `conjugate_op`, `controlled` and `checked_op`, in the specified positions of a static description and of an application |
| Target | Descriptions bound to their providers, and existing untrusted transformation proposals for a circuit, a finite contract or a hierarchy. No runtime closure exists. |
| Evaluation order | The complete description is checked before application. Runtime arguments evaluate once in source order, including at power zero. Adjoint reverses the operation order and conjugates the action. |
| Owners | The exact basis tree and the runtime group are retained. A tensor description uses its packed basis. It does not implicitly join separate owners. |
| Exact phase | Adjoint conjugates phase. Power repeats the complete action. Serial, tensor and conjugate descriptions retain the ordered action. Meaning is a separate obligation, never an access grant. |
| Source spans | The expansion keeps the original spans of the constructor, the operand, the count, the Meaning and the input through nested descriptions. |
| Refusal | Missing access; a wrong basis, interface or Meaning; an unsupported provider, transform or count; an unresolved obligation; a capacity failure. These reject in unused and zero-count contexts as well. Constructing `adjoint(U)` itself requires `Adjointable(U)`. |
| Open obligations | Providers, retained bodies, exact transformations and requested Meanings need an independent binding to the emitted artifacts. A valid unbound circuit is insufficient. |

See [access derivations](functional-boundary.md),
[repetition](static-language.md#operation-repetition-and-access) and
[checked operations](checked-operations.md).

The same eight fields apply to each constructor below. The constructors are
the existing endomorphic description actions. They do not admit the adjoint
of an isometry in general. An arrow gives the order of execution at runtime.
A matrix product acts right to left.

| Description | Exact expansion/action |
| --- | --- |
| Resolved provider/specialization | Retain the closed body, the bindings and the dependency evidence. No operation-name substitution occurs. |
| `adjoint(U)` | The justified adjoint action of U. On the supported circuit path, reverse and conjugate the retained steps. |
| `power(U,n)` | n serial copies of U, with the identity at zero. All original provider and access obligations are retained. |
| `then_op(U,V)` | Execute U, then V, on the same exact basis. The matrix action is `V U`. |
| `tensor_op(U,V)` | Apply U to the first basis block and V to the second ordered block. Retain one shared outer control when controlled. |
| `controlled(U)` | Retain the control, the identity on zero and the exact U on one, including the scalar phase of U. |
| `conjugate_op(C,U)` | The ordering `C† → U → C`, with matrix action `C U C†`. Do not silently substitute `C† U C`. |
| `checked_op(U,M)` | Retain the implementation of U and attach the independent exact M obligation. This inserts no runtime gate and no capability. |

Composing descriptions does not automatically transport an attached
`Op<A,M>` refinement.
[Functional abstraction](functional-boundary.md#admitted-operation-construction)
specifies the refinement rules and the obligation rules of the common
judgment, and the concrete independent checks.

The project route accepts this program. `power(eighth_phase,4)` is four
serial copies of T, and both `checked_op` descriptions carry the same exact
Meaning:

```qli
//! Two implementations of one phase-fixed meaning share an unchanged client.
use std::state::init0;

use std::gate::z;
use std::gate::t;

classical fn z_phase(b: Bit) -> (Bit,(Bit,Bit)) { (0,(0,b)) }
meaning ZMeaning: Bit = phase_by(z_phase);

unitary fn direct(q: Q<Bit>) -> Q<Bit> { z(q) }
unitary fn eighth_phase(q: Q<Bit>) -> Q<Bit> { t(q) }
unitary fn decomposed(q: Q<Bit>) -> Q<Bit> { power(eighth_phase,4)(q) }

/// The caller supplies evidence for the same exact Z operator.
unitary fn client[const U: Op<Bit,ZMeaning>](q: Q<Bit>) -> Q<Bit>
requires Applicable(U) { U(q) }

observe fn main() -> (Bit,Bit) {
    let a = client[checked_op(direct,ZMeaning)](h(init0()));
    let b = client[checked_op(decomposed,ZMeaning)](h(init0()));
    (measure_z(h(a)),measure_z(h(b)))
}
```

The selected-entry route rejects the next function with the code `access`.
`f` applies `controlled(power(U,0))` and declares no `Controllable(U)`. The
check covers the body although the fold has zero iterations:

```qli
pub unitary fn f[const n: Nat, const U: Op<Bits<n>>](c: Q<Bit>, q: Q<Bits<n>>) -> (Q<Bit>,Q<Bits<n>>) { qfor static k in 0..0 carry pair = (c,q) { let (c,q) = pair; yield controlled(power(U,0))(c,q); } }
```

## Coherent control

Coherent control applies an operation to a target owner under a `Q<Bit>`
control, without measuring the control. `controlled(U)(c,q)` applies `U` when
the control is one. `qif(c,q) { 0 => F, 1 => G }` applies `F` when the
control is zero and `G` when it is one.

| Field | Contract |
| --- | --- |
| Source | `controlled(U)(c,q)`, or `qif(c,q) { 0 => F, 1 => G }` with both arms in that order. A `qif` arm is a named operation or an inline block `{ ... }`. |
| Target | Finite `Join → ApplyUnitary → Split` over the ordered `(Bit,A)`, with the bound controlled circuit and its evidence; otherwise the supported hierarchy construction. Controlled U retains the inactive identity. `qif` retains its specified zero and one actions. |
| Evaluation order | The control evaluates, then the target, each completely and once. The control is not measured and is not used as a classical condition. |
| Owners | The form consumes two inputs, packages them temporarily for the finite controlled action and returns `(Q<Bit>,Q<A>)` in order, even for zero-width A. The complete target tree and the reference frame are retained. Packaging prepares no state. A block arm binds the written target name and returns one owner of the exact target type. Other runtime owners of the enclosing scope are unavailable in the block. |
| Exact phase | The control is the first low axis. The inactive identity has coefficient +1. The active phase is retained, including scalar Unit phase and kickback. |
| Source spans | The expansion keeps the control argument, the target argument and the names of the provider or of the arms. Generated control structure retains the origin of the expression. |
| Refusal | A missing Controllable capability; wrong owners or arity; aliases; an invalid arm; an omitted or reordered arm; a block arm whose target is not a name, whose body is not Unitary, or that does not return the target owner; an unsupported interface. Unitarity grants no control access. |
| Open obligations | The provider or body identity, the exact action, the axes and the owners need an independent check. Probabilities, or tests on known inputs, do not discharge coherent correspondence or reference correspondence. |

The inactive identity belongs to the specified controlled meaning. No
rewrite of a `qif` with an omitted arm is admitted.
[Exact-label coherent selection](source-text.md#exact-label-coherent-selection)
specifies the block arms that `qif` shares with `qmatch`.

The selected-entry route with the native checker accepts this function. Its
second arm is an inline block:

```qli
#![no_implicit_prelude]
pub unitary fn route(s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){
    qif(s,q){0=>h,1=>{let r=h(q);phase[1,1](r)}}
}
```

The common checker rejects the next program with the class `ownership`. The
block arm uses the control `s`, which is unavailable in the block:

```qli
unitary fn keep(q:Q<Bit>)->Q<Bit>{q} pub observe fn f(s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){qif(s,q){0=>keep,1=>{ h(s) }}}
```

## Exact-label coherent selection

`qmatch(selector, target) { label => arm, ... }` selects among its arms
coherently. It applies one arm to the target for each basis label of the
selector. It does not measure the selector. On a `Bit` selector it agrees
exactly with `qif`.

| Field | Contract |
| --- | --- |
| Source | `qmatch(selector, target) { label => arm, ... }`. An arm is a resolved static operation or an inline block. The labels cover the logical basis of the selector exactly once, in any order. A label is a canonical decimal ordinal for `Unit`, `Bit` and closed `Bits<n>` with `0 <= n <= 6`, and a qualified variant name for a fieldless enum. |
| Target | A proposed circuit on the selector axes followed by the target axes, emitted in a Raw root. On the route that checks the original source, each selection binds one literal, contiguous Raw interval and its owner frame. |
| Evaluation order | The selector evaluates, then the target, each once. The selector is not measured. The written arm order does not change the action. |
| Owners | The form consumes one `Q<A>` selector and one distinct `Q<B>` target and returns `(Q<A>, Q<B>)` with both complete type trees unchanged. Zero physical width removes neither owner. A block arm binds the written target name and returns one owner of the exact target type. Other runtime owners of the enclosing scope are unavailable in the block. |
| Exact phase | With arm `s` denoting the exact operator `U_s`, the action maps `\|s,y>` to `sum_z U_s[z,y] \|s,z>` and extends linearly, including to inputs entangled with an external reference. All arm phases are exact. Selector axes precede target axes, so `(s,y)` has the coordinate `s + 2^selector_bits * y`. |
| Source spans | Each selection retains its own source position and its ordered arms. On the route that checks the original source, it also retains its literal Raw interval. |
| Refusal | A wildcard, range, payload or guard label; a dynamic arm call; a missing, repeated or out-of-range label; more than 64 arms; a selector that is not one `Q<A>` owner of a supported basis; a target that is not one distinct `Q<B>` owner; an arm with another target interface, without a Unitary effect or without the Controllable capability; an unsupported target. Unitarity alone grants neither control nor inverse access. |
| Open obligations | The proposed circuit needs a fresh native encoded equation against the independently obtained exact block meaning. The emitted Raw root needs ordinary native checking. Three things do not prove preservation of the original source: common enum checks, native acceptance of a proposed circuit, and conformance tests. |

[Source text](source-text.md#exact-label-coherent-selection) specifies the
form, its block arms and its routes.

The common checker accepts this program. The labels are written in an order
other than the ordinal order:

```qli
unitary fn keep(q:Q<Bit>)->Q<Bit>{q} unitary fn f(s:Q<Bits<2>>,q:Q<Bit>)->(Q<Bits<2>>,Q<Bit>){qmatch(s,q){3=>keep,0=>keep,2=>keep,1=>keep}}
```

The common checker rejects the next program with the class `type`. The label
`1` is missing:

```qli
enum E{A,B,C} unitary fn keep(q:Q<Bit>)->Q<Bit>{q} fn f(s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){qmatch(s,q){0=>keep}}
```

## Coherent basis maps

A coherent basis map applies an injective function on basis labels to one
quantum owner. The program writes the function as an expression on a label
pattern.

| Field | Contract |
| --- | --- |
| Source | `basis q as pattern { expression }` |
| Target | Finite or selected Raw `LiftBasis` with a complete supported label map |
| Evaluation order | `q` evaluates once, before the labels are bound. The restricted total expression evaluates in a separate basis scope. |
| Owners | The form consumes one `Q<A>` and returns one `Q<B>`. Label patterns do not split runtime owners. Separate inputs are not implicitly joined. |
| Exact phase | Each transition has coefficient +1, linearly, with the identity on an arbitrary external reference. Amplitudes and ordered output labels are retained. |
| Source spans | The expansion keeps the original spans of the input, the label pattern and the body. |
| Refusal | A wrong owner or tree; an outer capture; an unsupported body or callee; a noninjective complete map; reuse; an unavailable profile. |
| Open obligations | The complete lift, its injectivity and its effects need an independent check. The correspondence of the source to the table is separate from the validity of the table. |

See [coherent basis maps](coherent-basis.md), including Unit and the
difference between label copying and state copying.

The project route accepts this program. `main` returns `(1,0)`:

```qli
use std::state::init0;
classical fn flip(x: Bit) -> Bit { not x }
unitary fn lifted(q: Q<Bit>) -> Q<Bit> { basis q as b { flip(b) } }
pub observe fn main() -> (Bit,Bit) {
    let q = init0(); let reference = init0(); let q = lifted(q);
    (measure_z(q),measure_z(reference))
}
```

Selected elaboration rejects the next function with the code `ownership`. The
constant map is not injective:

```qli
pub unitary fn f(q:Q<Bit>)->Q<Bit>{basis q as a {0}}
```

## Computed workspace

`with_computed` gives a scoped body one temporary ancilla. It computes the
ancilla from a source register by a classical predicate, runs the body, and
uncomputes the ancilla.

| Field | Contract |
| --- | --- |
| Source | The two-argument form `with_computed(source,predicate)`, or the three-argument form with a logical contract |
| Target | Raw `ComputeUseUncompute`, or the certified retained-body construction with finite evidence, within each supported profile |
| Evaluation order | The source evaluates once. The form computes the specified ancilla, executes the checked scoped body and then uncomputes. |
| Owners | The predicate takes one ordinary parameter of the exact tree of the source. The two-argument body returns the ancilla. The three-argument body returns the data and the ancilla. Capture and protection rules are explicit. No standalone Release0 is inserted. |
| Exact phase | The expansion preserves the specified use or logical action. An exact all-input clean return is required. A cleanliness check alone cannot certify the live action or its phase. Approximate cleanup cannot discharge this obligation. |
| Source spans | The expansion keeps the origins of the source, the predicate, the body, the returned owner and the logical contract. |
| Refusal | A wrong predicate arity or tree; an unsupported body; an Observe effect; lost, aliased or protected owners; a failed equality or cleanup; capacity exhaustion. A one-Bit ancilla body outside the canonical empty/Z/T token chain must act as an exact eighth-root diagonal. Non-diagonal or unrepresentable actions reject. No exception that is based on a name supplies evidence. |
| Open obligations | The retained compute, use and uncompute steps and the exact logical and cleanup contract, with references, need an independent check. Syntax and Unitary annotations supply no clean evidence. |

See [scoped bodies](functional-boundary.md#scoped-bodies-finite-elaboration-and-effects)
and [predicate trees](type-model.md#structural-equality-coherence-and-physical-maps).

> **Implementation note.** The two-argument path retains an already canonical
> empty/Z/T token chain through the protected gate. For the other supported
> one-Bit ancilla bodies, the native checker checks a whole-original equation
> and a canonical-witness equation for the same exact eighth-root diagonal,
> before scalar/Z/T normalization. Chunking supplies only an untrusted matrix
> proposal. The graph, dependency, source and shared-work capacities apply.

The project route accepts this program, which uses the two-argument form.
`main` returns `(1,1)` with probability one:

```qli
use std::basis::and2;
use std::basis::xor2;
use std::state::init0;

use std::gate::x;
use std::gate::z;

classical fn predicate((a,b): (Bit,Bit)) -> Bit { xor2(and2(a, b), 0) }
observe fn main() -> (Bit, Bit) {
    let q = join(h(init0()), x(init0()));
    let q = with_computed(q, predicate) { |a| z(a) };
    let (a, b) = split(q);
    (measure_z(h(a)), measure_z(b))
}
```

The project route rejects the next program with the code `unsupported`. The
body `h(a)` is not diagonal:

```qli
use std::state::init0;  use std::gate::x; use std::gate::z;
classical fn p(x: Bit) -> Bit { x } observe fn main() -> Bit { measure_z(with_computed(init0(), p) { |a| h(a) }) }
```

## Function contracts

A function contract pairs an implementation with a specification.
`apply_contract(implementation, specification, input)` applies
`implementation` to one quantum owner. It records the obligation that
`implementation` equals `specification`. The form has two overloads, a pure
one and an observing one.

| Field | Contract |
| --- | --- |
| Source | `apply_contract(implementation, specification, input)`. In the pure overload, both names denote closed functions with the interface `Q<A> -> Q<A>` and a Unitary effect that the caller can see. A declared finite Meaning may supply the specification instead. In the observing overload, both names denote closed ordinary functions with an Observe effect that the caller can see, one `Q<A>` argument and the same complete finite result type. |
| Target | Pure overload on Raw: a circuit `Contract` step that carries the checked receipt. Pure overload on the hierarchy: a checked finite leaf that embeds the complete receipt-bearing wrapper bytes. Observing overload: the emitted call interval of the implementation, with a private native instrument equation. |
| Evaluation order | The input evaluates first, once. A declared Meaning supplies the request and is never projected as a runtime function. The observing overload executes only the implementation. |
| Owners | The form consumes one exact quantum owner and returns the result of the implementation. In the observing overload, the complete result nesting, the ordered quantum and classical projections, zero-width owners, hidden histories and residual states are significant. |
| Exact phase | The function-equality check is an exact equation between the implementation and the specification. A replacement with an equal matrix and different implementation or specification bytes cannot substitute for the original receipt, which is bound to the source. |
| Source spans | The obligation binds both original definitions, the interface, the category, the effect and the source span. Raw emission keeps the original pair, owner, direction and ordered axes for source replay. |
| Refusal | A local value in place of a function name; a `classical fn` or a Meaning as the implementation; a function with static parameters; a function without exactly one `Q<A>` parameter of the input basis; different result types; a failed equation; an observing Meaning; lowering without the native checker. |
| Open obligations | The function-equality obligation is pending until the independent native evidence gate discharges it. Binding the identity of a Meaning or a provider is not matrix equality, injectivity, all-input clean return, provider correspondence or source preservation. Both emitted artifacts need fresh native acceptance. |

The [type model](type-model.md#direct-runtime-transforms-and-opaque-operations)
specifies both overloads.

The project route accepts this program, which uses the observing overload.
`measure_z(h(h(q)))` and `measure_z(q)` are the same instrument:

```qli
use std::state::init0;  use std::gate::x;
use std::gate::z; use std::gate::t; use std::gate::cnot;

classical fn predicate(value: Bit) -> Bit { value }
unitary fn identity(q: Q<Bit>) -> Q<Bit> { q }
unitary fn specified_phase(q: Q<Bit>) -> Q<Bit> { z(q) }

fn reference(q: Q<Bit>) -> Bit { measure_z(q) }
fn implementation(q: Q<Bit>) -> Bit { measure_z(h(h(q))) }
observe fn main() -> Bit { apply_contract(implementation,reference,x(init0())) }
```

The project route rejects the next program with the code `contract`. The
implementation relabels the public outcome of the reference:

```qli
use std::state::init0;  use std::gate::x;
use std::gate::z; use std::gate::t; use std::gate::cnot;

classical fn predicate(value: Bit) -> Bit { value }
unitary fn identity(q: Q<Bit>) -> Q<Bit> { q }
unitary fn specified_phase(q: Q<Bit>) -> Q<Bit> { z(q) }

fn reference(q: Q<Bit>) -> Bit { measure_z(q) }
fn implementation(q: Q<Bit>) -> Bit { not(measure_z(q)) }
observe fn main() -> Bit { apply_contract(implementation,reference,init0()) }
```

## Explicit maps and unsupported candidates

Some maps are explicit operations of the source program. The program writes
them, and no elaboration inserts them. This section also names conveniences
that the language does not admit.

Rules:

- `split`/`join`, Unit insertion and removal, and the register primitives are
  explicit [specified maps](primitive-boundary.md). They keep their original
  ordered interfaces and the coefficient +1.
- An elaboration must not insert such a map to repair an argument tree.
- `Bit`, `Bits<1>`, `Unit` and `Bits<0>` are distinct. Tuples of different
  arity or nesting are distinct. Packed owners are distinct from separate
  owners.
- Canonical reassociation is not definitional equality. It is not an admitted
  implicit elaboration.
- An ordinary literal does not prepare a quantum state.
- `init0` is not a primitive. It is the ordinary
  [standard-library](stdlib.md) function `std::state::init0`, declared
  `pub isometry fn init0() -> Q<Bit>` and defined by
  `basis unit(()) as _ { 0 }`. It keeps its explicit Isometry contract.
- `basis` is a coherent map. It is not sugar for arbitrary state
  preparation.
- Beyond explicit selected-place access, no implicit view partition and no
  implicit reassembly is admitted.
- No insertion of `excl` or `ctrl`, no arbitrary wire permutation and no
  cleanup is admitted.
- A convenience may be added only after its complete contract and its checking
  evidence exist. The candidate list of an Issue is insufficient.

### Register primitives on the Selected Raw target

On the Selected Raw target, the register primitives `take_bit[N,K]` and
`put_bit[N,K]` expand into structural instructions.

Rules:

- Each requires its statically established premise `K < N`.
- Each expands to three existing Split/Join instructions.
- `take_bit` preserves the ordered remainder. `put_bit` inserts the bit at its
  declared axis.
- Empty prefixes, empty suffixes and the `Bits<0>` remainder are logical
  owners through the structural operations.
- The expansion emits no physical SWAP, preparation, measurement or implicit
  discard.

These primitives and the lowering of selected places use the same structural
instructions. Explicit indexed access and slice access connect common
checking to ordered partition and reconstruction under the
[static-place rules](#static-ordered-axis-places). Such access does not
insert a source `take_bit`/`put_bit` call, and it does not infer an access
mode.

> **Implementation note.** Independent source-step replay checks the original
> partition, the intermediate fresh owners and the returned wire order of each
> `take_bit` and `put_bit`. Native validity is a separate fresh decision.

Selected Raw lowering with the native checker accepts this function:

```qli
use std::gate::x; use std::gate::z;
pub unitary fn main(input:Q<(Bits<2>,Bit)>)->Q<(Bits<2>,Bit)>{
    let(q,r)=split(input);
    let(b,rest)=take_bit[2,1](q);
    join(put_bit[2,1](b,rest),r)
}
```

## Original locations and failure

This section states the original location that each emitted operation
retains, and how kinds of failure stay distinct.

Rules:

- A span is a half-open UTF-8 byte interval in the unnormalized original
  source.
- Emitted operations retain their origins in the original expression and
  body. Finite nested branches retain operation and arm-index paths.
- An enclosing expression must not overwrite the origin of a child or of a
  callee.
- An inserted operation without a more specific origin uses the span of its
  expression.
- Unsupported profiles and work limits keep distinct diagnostics. Exhaustion
  is not mathematical invalidity.
- A migration error names the original tokens.

> **Implementation note.** After a finite native rejection, diagnostic mapping
> selects the longest retained operation-path prefix, and otherwise the
> original caller or declaration. This mapping is post-rejection metadata
> only. It cannot change acceptance, manufacture evidence or hide a failure.

## Migration correspondence

Some earlier spellings of these forms are retired. The table below maps each
retired form to its explicit form. A **migration derivative** is a separate
source that uses the explicit form.

Rules:

- Production rejects retired forms. It does not retry a legacy grammar, and it
  applies no compatibility rewrite that accepts them.
- A migration derivative has its own bytes and provenance.
- A migration must preserve the original source, its diagnostics and its
  artifacts, and must validate the complete derivative.
- A migration must not weaken owners, access, effects or Meaning to make a
  rewrite succeed.

| Preserved old form | Explicit form | Preserved contract |
| --- | --- | --- |
| `[static n: Nat, ...]` | `[const n: Nat, ...]` | Ordered explicit kinds and arguments; no inferred specialization |
| `adjoint(U,q)` / earlier `inverse(U)(q)` | `adjoint(U)(q)` | Adjoint action and its access premise |
| `repeat_op(k,U)` / `repeat_static(k,U,q)` | `power(U,k)` / `power(U,k)(q)` | The count, the exact provider and group, and evaluation of the input exactly once |
| `inverse_op(U)` / `controlled_op(U)` | `adjoint(U)` / `controlled(U)` | The identity and the access of the bound description |
| `Apply` / `Adjoint` / `Controlled` predicates | `Applicable` / `Adjointable` / `Controllable` | Provider access; an annotation grants nothing |
| `do p <- q; pure e` | `basis q as p { e }` | The same CoherentLift, coefficient +1 and injectivity |
| `bind_op(U,M)` | `checked_op(U,M)` | The exact interface and Meaning, and the original provider evidence |

The table is not a general automatic rewriter. An unimplemented draft
acquires no claim of historical equivalence. [Types](type-model.md) and
[stdlib](stdlib.md) keep their separate migration contracts.

An artifact that carries source can change its bytes after a source edit.
This can happen even when the operator and the interface meaning are equal.
A migration must never erase identity to force byte equality.

## Status and limits

This section gives the limits of each target, and it keeps apart what tests,
proofs and admitted guarantees establish for the forms of this chapter.

### Accepted forms without a contract in this chapter

The common checker accepts these surface forms. This chapter gives them no
contract table.

| Form | Specified in |
| --- | --- |
| `clean(data, logical) { \|data, scratch\| body }` and `dirty(data, scratch, logical) { \|data, scratch\| body }` workspace scopes | [Rust boundary](rust-boundary.md), section "Explicit clean and dirty scopes" |
| The body of a `classical fn`, including the coordinate read `word[k]` and `empty_bits()` | [Total classical declarations](source-text.md#total-classical-declarations) |
| Literal values, sealed operations and explicit structural maps | [Type model](type-model.md) and [primitive boundary](primitive-boundary.md) |

### Profiles

The table gives the limits that this chapter states for each target. A dash
means that the chapter states no limit for that target.

| Form | Finite project | Selected Raw | Selected hierarchy |
| --- | --- | --- | --- |
| `ctrl` places | Admits a retained concrete `ctrl` call after a fresh native sector check | Admits the same call when lowering runs with the native checker. Checker-free lowering rejects every control obligation. | Supported pure `ctrl` calls only. Each control decision covers at most six physical input bits and uses the exact scalar ring. Three things are outside the profile: control occurrences that are not retained, observing entries and entries bound to a Meaning. |
| Static ordered-axis places | Concrete places within the bounded profile | Concrete places within the bounded profile | `excl` indices and slices on owners of up to eight axes |
| Runtime classical `if` | Raw `ClassicalBranch` | The supported selected branch representation. The selected projection can reject a runtime `if` as unsupported. | — |
| `take_bit[N,K]`, `put_bit[N,K]` | — | Supported within the bounded concrete profile | — |
| `basis q as p { e }` | Finite `LiftBasis` | `LiftBasis` with a complete supported label map | The general bridge is unsupported |

Further limits:

- A mixed access call with a `ctrl` marker is admitted from a closed
  nongeneric body only.
- An exclusive named call takes ordinary `Bit` arguments only when the
  selected callee lowers to a single checked ordinary branch.
- A declared access parameter requires a finite function with a closed
  selected specialization.
- [Coherent basis maps](coherent-basis.md) gives the limits of each profile
  for `basis`.
- Nominal values and ordinary `match` execute through a typed native route.
  They execute in eligible closed ordinary project roots and in nongeneric
  public selected roots. The legacy selected projection rejects them as
  unsupported. General selected integration is unfinished.
- An ordinary `match` and a `qmatch` each have at most 64 arms.
- A built-in `qmatch` selector is `Unit`, `Bit` or a closed `Bits<n>` with
  `0 <= n <= 6`. The legacy hierarchy projection refuses `qmatch`.
  [Source text](source-text.md#exact-label-coherent-selection) gives the
  limits of each `qmatch` route.
- The observing overload of `apply_contract` uses the finite Raw profile in
  selected compilation. Hierarchy lowering and checker-free emission reject
  that overload.
- Raw lowering and hierarchy lowering without the native checker reject a
  program with outstanding function contracts.

### Tests

The examples of this chapter come from sources that these tests check. A test
that needs the native checker runs only where one is configured.

| Sections | Tests |
| --- | --- |
| Runtime products, patterns and calls | `tests/review_v024.rs` |
| Evaluation and owner lifetime | `tests/exclusive_access.rs`, `tests/compile.rs` |
| Whole-owner exclusive calls; static ordered-axis places; explicit maps | `tests/exclusive_access.rs` |
| Ordinary Unit arguments; declared access parameters | `tests/selected_runtime_execution.rs` |
| Ordinary expressions and classical functions; coherent basis maps | `tests/classical_functions.rs`, `tests/selected_coherent_basis.rs` |
| Nominal values; ordinary match | `tests/ordinary_nominal_execution.rs` |
| Runtime classical branches | `tests/exclusive_access.rs`, `tests/compile.rs` |
| Static natural computation; specialization; finite folds | `tests/static_naturals.rs`, `tests/general_static_runtime.rs`, `tests/sized_source.rs`, `tests/qfor.rs` |
| Operation descriptions | `tests/operation_parameters.rs` on `examples/operation_contracts`, and `tests/sized_source.rs` |
| Coherent control | `tests/selected_runtime_execution.rs`, `src/frontend/check/body/quantum_matching/tests.rs` |
| Exact-label coherent selection | `src/frontend/check/body/quantum_matching/tests.rs` |
| Computed workspace | `tests/compile.rs` |
| Function contracts | `tests/function_contracts.rs` |

Two preserved comparisons check the migration table:

- The [operation-application comparison](https://github.com/MGYamada/Qleisli/blob/0a86fe5456bf92553459ffd5ad45d20180b23494/tests/fixtures/frontend_v030/retired-operation-spellings/migration-comparison.json)
  checks a complete two-qubit source in its old spelling and in its explicit
  spelling, on separately identified binaries. Both sources receive fresh
  source checks. The proposed bytes agree, with SHA-256
  `32adb61c4a2b24c77dd89f83d0761b427d7509b85b0c4a3b4f93b313d50b9bd4`.
  Emission is not acceptance, so those separate checks are necessary.
- The [capability-name comparison](https://github.com/MGYamada/Qleisli/blob/0a86fe5456bf92553459ffd5ad45d20180b23494/tests/fixtures/frontend_v030/capability-naming/precommit-validation.json)
  retains 34 equal checked artifacts and one measurement-adjoint refusal. Its
  selector verifies exact predecessors and derivatives without rewriting
  first sources or independent oracles.

The [coherent-basis](coherent-basis.md) and
[checked-operation](checked-operations.md) regressions do not compare bytes.
They retain exact interfaces and independent small complex tests of action
or instrument, phase, axis, provider and reference.

### Proofs

The items below describe the theorems that concern the forms of this
chapter, and what those theorems do not establish.

- The compatible access theorem uses the ordered physical wires of each
  checked call as its footprint. Any wire that both calls use must be `ctrl`
  in both. The exact local reconstruction preserves every shared control bit,
  and the other modified coordinates are disjoint.
- For a checked pair of adjacent calls with a structural return, the theorem
  states an equality of complex amplitudes. The original Raw root and the
  exchanged operator composition agree after the same output permutation, for
  every input and every external reference column. The equality retains
  conditional phase and entanglement.
- A protected-phase theorem exchanges adjacent literal phases in their
  original physical action.
- `Qleisli.SharedControlCommutation` proves exact matrix equality for common
  control sectors that act on disjoint ordered target factors. Its
  single-control bridge concerns the hierarchy definitions of tensor,
  control and sequence. The bridge includes unchanged surrounding operations
  and arbitrary amplitudes of an external reference. Zero-width factors
  retain their scalar phases.
- `Qleisli.RoutedControlCommutation` extends that connection to two original
  hierarchy entry bodies with distinct intermediate routes. Its explicit
  premises bind the original definition records, same-artifact node typing,
  fresh wiring summaries, computed two-sided inverse permutations and provider
  evaluations. Literal coordinate decompositions identify a common control,
  disjoint ordered targets and untouched factors. The resulting exact matrix
  equality preserves arbitrary amplitudes of an external reference.
- Typing alone establishes neither those coordinate decompositions nor
  matching provider meanings. The two commutation results derive no source
  footprint from `ctrl` or `&mut`. They prove no arbitrary routing of owners
  or axes, and they authorize no source reordering. Width premises do not
  discharge `Q<Unit>` ownership. Four obligations are open: source
  footprint, general lowering, acceptance and work preservation.
- Neither commutation proof is a constitutional guarantee or a guarantee
  admission. Their bounded examples and proof records are in
  `tests/fixtures/constitution_v030/shared-control-commutation/` and
  `tests/fixtures/constitution_v030/routed-control-commutation/`. The
  emitted-source examples of the second distinguish the conditional Lean
  theorem from runtime checks and bounded matrix observations. Their zero-axis
  sources use `Q<Bits<0>>`, not an identification with `Q<Unit>`.
- The QPTL theorem `QPTL.FiniteMatrix.scratchMarginal_eq_iff` proves a
  partial-trace equivalence for finite Kraus families on positive
  semidefinite unit-trace inputs. It concerns a finite trace-preserving
  channel whose workspace starts in a fixed pure state.
- The equivalence has two sides. One side is the exact return of the
  workspace marginal on every live input. The other side is factorization
  with the same workspace state for every joint input with an external
  reference.
- In a scratch basis that contains the clean state, the unwanted diagonal
  populations are sums of squared Kraus coefficients. Their vanishing on all
  live basis inputs forces every unwanted coefficient to vanish.
- The live output includes any declared classical outcome register with its
  original probabilities. The live factor is the joint output with scratch
  traced out, and it retains the reference coordinates.
- The exact requested live action, the coherent phase, the dirty-workspace
  identity and the quantitative costs have their own contracts.

### Preservation

- Independent source replay is not a general source-preservation theorem and
  not a proof of an optimizer.
- General source preservation and quantitative resource correspondence are
  proof obligations.
- The bounded migration comparisons are migration evidence. They are not
  universal source preservation, complete QS/PR/RS, a generic QFT
  implementation or release approval.

### Guarantees and specification review

- Two scoped guarantees are admitted: `QS-QLV1-OWNERSHIP-2026-01` for
  ownership and `QS-QLV1-SCOPE-2026-01` for classical scope. Both keep their
  original decoded-root premises.
- Four obligations are pending: the broader source and semantic QS
  obligation, the forward PR obligation, the quantitative RS obligation and
  the EXACT obligation. Their interpretations are QS-2026-01, PR-2026-01,
  RS-2026-01 and EXACT-2026-01.
- The contracts of this chapter are adopted source contracts. A contract
  table discharges no guarantee and adds no ledger entry.

## History

- The chapter consolidates the adopted source contracts that
  [Issue #34](https://github.com/MGYamada/Qleisli/issues/34) tracks.
- The chapter describes release `0.3.0-beta`.
- [Issue #303](https://github.com/MGYamada/Qleisli/issues/303) records the
  compatible access theorem.
- The capability-name comparison was made after the operation-application
  comparison.

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
