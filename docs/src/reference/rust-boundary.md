# Rust familiarity and quantum meaning

Rust supplies a useful vocabulary when its ordinary intuition survives
Qleisli's checking. The governing rule is: **reuse familiar syntax for familiar
semantics; use distinct syntax when that intuition would misdescribe a quantum
operation.** Familiar spelling is not evidence of a physical operation, an
ownership transition or a checked mathematical law.

This chapter specifies the current `0.3.0-alpha` boundary in edition 2026 under
the [authority hierarchy](authority.md). It applies the ordinary
[#68 diagnostics decision](https://github.com/MGYamada/Qleisli/issues/68#issuecomment-6009785277),
the [type model](type-model.md) and the
[functional boundary](functional-boundary.md). It distinguishes implemented
rules from grammar that is still absent. The wider decisions and acceptance
criteria of [#67](https://github.com/MGYamada/Qleisli/issues/67) and
[#68](https://github.com/MGYamada/Qleisli/issues/68) remain open. Broad import of
ordinary Rust surface features belongs to
[#251](https://github.com/MGYamada/Qleisli/issues/251).

## Ordinary data may be ignored

Ordinary `Bit`, `Unit` and products containing only ordinary data are
unrestricted: they may be reused, unused or matched by `_`. Ignoring an ordinary
measurement result does not destroy another live quantum owner. Its earlier
measurement still contributes Observe to the body's principal effect.

These function fragments use ordinary binding, tuple construction and
wildcard matching:

```qli
fn duplicate(b: Bit) -> (Bit, Bit) { (b, b) }

fn ignore(b: Bit) -> Unit {
    let _ = b;
    ()
}
```

There is no requirement to insert a physical `discard` for an unused classical
Bit. Nor does this rule introduce Rust's `Drop`, `Clone`, `Copy` or trait
machinery. Current source has no built-in `drop`, `forget`, `clone`, `copy` or
`default` function. Those identifiers remain ordinary names, resolved using
the same declaration, import and lexical rules as other identifiers.

An unresolved `drop(0)` is therefore a name error about an absent builtin, not
a quantum ownership error. A valid user definition named `drop` remains valid;
its name grants no special permission. In particular, this observing function
fragment explicitly means measurement:

```qli
use std::observe::measure_z;

observe fn drop(q: Q<Bit>) -> Bit {
    measure_z(q)
}
```

The function consumes its quantum input through its checked body. It is not a
quantum destructor or an escape from effect inference.

## Explicit construction instead of Default

For release 0.3.0, a Rust-like `Default` abstraction is unavailable for every
runtime type containing a live quantum owner. This includes `Q<T>`, `Q<Unit>`,
`Q<Bits<0>>` and ordinary products containing any such field. The
[#79 decision](https://github.com/MGYamada/Qleisli/issues/79#issuecomment-6009973288)
does not make ordinary/static basis data quantum resources: `0`, `()` and
explicit ordinary constructors remain ordinary data, without preparation or a
quantum owner. No default conversion is inserted between these types.

The current language has no general trait/impl, associated `Default` call or
generic `Default` bound. Broad ordinary trait ergonomics remain in #251. That
grammar exclusion supplies no proof or implementation of future trait
resolution; any later admitted facility must preserve this construction law.
Current generic Basis bodies undergo the same complete source checks as other
bodies, including declarations that the selected entry does not call.

Preparation is an explicit operation with its individual contract. `init0()`
creates a fresh zero qubit with Isometry action. `unit(())` creates one fresh
zero-axis `Q<Unit>` owner with exact coefficient `+1` and Unitary action;
it allocates no physical wire. `empty()` introduces the separately typed
`Q<Bits<0>>` owner. Neither zero physical width nor an ordinary Unit argument
makes the returned owner unrestricted. Explicit `finish` preserves preceding
scalar phase, and checked scoped cleanup retains its all-input fixed-state
contract. Default construction provides no hidden clean workspace or cleanup.
General clean/dirty facilities and quantitative resource certification retain
their separate pending obligations; a source effect is not a resource bound.

An ordinary function may be named `default`. For example, this checked function
fragment has explicit preparation and principal Isometry effect:

```qli
use std::quantum::init0;

fn default() -> Q<Bit> { init0() }
```

Its caller retains that effect; a false Unitary assertion rejects. Conversely,
a function named `default` that returns ordinary data gains no quantum action
from its spelling. A name, return-type annotation or generic parameter cannot
grant allocation, duplicate a quantum result, or excuse an abandoned owner.

## Quantum owners require an explicit transition

`Q<A>` is linear, including `Q<Unit>` and `Q<Bits<0>>`. A product containing any
quantum owner is also linear, even when that owner is nested among ordinary
fields. Zero physical width does not remove the ownership or scalar-phase
obligation. Such a value cannot be implicitly copied, ignored by `_`, abandoned
as an expression statement, overwritten by shadowing a live binding, or lost
at function or local scope exit.

Ordinary `let` still means binding. `let q = h(q);` is valid when the right-hand
side consumes the preceding owner and returns the replacement before the new
binder is introduced. `let q = init0();` cannot shadow a preceding live `q`.
This distinction does not introduce assignment to places, temporary references
or automatic quantum destruction.

Separate owner names do not imply separate physical states. Observation or
disposal of one subsystem must retain its specified action on an arbitrary
joint state, including correlations with every retained owner and external
reference. A name, lifetime, sampled result or assertion of unitarity cannot
establish cleanliness.

The following signatures are interface descriptions, not first-class arrow
syntax. Common source recognition and requested concrete support remain
distinct; see the [primitive inventory](primitive-boundary.md).

| Explicit operation | Owner, effect and intended physical meaning |
| --- | --- |
| `std::observe::measure_z(q)` | `Q<Bit> -> Bit`; Observe. Consumes the original logical owner and returns the Z outcome. It does not return a quantum owner or silently select one outcome. |
| `std::observe::discard(q)` | One `Q<A> -> Unit`; Observe. Explicitly loses that subsystem's quantum information by the specified partial trace. It is not proof of clean return. The finite lowering supports it; the selected concrete catalog currently does not. |
| `std::observe::reset(q)` | `Q<Bit> -> Q<Bit>`; Observe. Ends the original logical owner and returns a fresh owner prepared in zero. The result remains linear and must itself be returned or explicitly consumed. The finite lowering supports it; the selected concrete catalog currently does not. |
| `with_computed(...) { ... }` | A checked scoped construction with its own exact cleanup premises. It returns the data owner and discharges its private auxiliary only through the admitted compute/use/uncompute rule. |
| `adjoint(U)(q)` | Reverses the specified operation only with the required checked access. The call consumes its input and returns an owner; uncomputation alone does not discharge that returned owner or prove it clean. |
| Scope exit | A lexical boundary requiring complete owner accounting. It performs none of the physical operations above. |

There is no supported standalone `release(q)` and no free-standing `Release0`
IR constructor. Diagnostics must not recommend that invented call. Existing
explicit `finish` for `Q<Unit>` and `consume_empty` for `Q<Bits<0>>` retain their
exact structural contracts; neither is a general clean-release or discard API.
Preceding scalar work remains in the composed meaning.

For example, a finite observing body can choose reset and then explicitly
consume its fresh result:

```qli
use std::observe::reset;
use std::observe::measure_z;

observe fn reset_then_measure(q: Q<Bit>) -> Bit {
    let fresh = reset(q);
    measure_z(fresh)
}
```

Writing `reset(q);` would instead abandon its fresh quantum result. Changing
the spelling to `drop(q)` cannot justify any of these different operations.

## Checked cleanup is a separate contract

The current two-argument `with_computed(source, predicate)` exposes one private
computed auxiliary to a scoped body and protects the source data. The predicate
is a total `classical fn` with one ordinary argument of the data's exact basis
tree and result `Bit`. The body must return the auxiliary owner and satisfy the
Unitary requirement. Current finite concrete lowering restricts its expanded
auxiliary body to identity or the admitted Z/T sequence; it does not synthesize
an inverse for arbitrary source code.

The three-argument form additionally supplies a logical operation and exposes
data/auxiliary binders. It returns both owners in the required order and checks
the bounded exact computed-relation contract. If `E_f` embeds each data basis
value as `|x,f(x)>`, the use circuit `W` must satisfy `W E_f = E_f V` for the
specified logical action `V`, with exact coefficients, phase and ordered axes.
The surrounding compute/uncompute construction then justifies the auxiliary's
return to zero. A Unitary annotation or the binders' names do not supply this
equation.

The underlying clean obligation is exact return to the declared fixed pure
state for every permitted data input. Under the adopted all-input channel
premises, this is equivalent to factorization with that same fixed pure state
for every retained external reference. Separation alone is insufficient: an
auxiliary in a different pure state is separable but has not returned to its
declared state. One known-input test, approximate zero probability or an
unchanged unknown marginal is insufficient. Dirty workspace instead needs
restoration of its arbitrary state
and reference correlations. General `clean`/`dirty` grammar and automatic
cleanup rules remain work in
[#70](https://github.com/MGYamada/Qleisli/issues/70) and
[#72](https://github.com/MGYamada/Qleisli/issues/72); this existing scoped
implementation does not complete those decisions.

## Conditional teaching diagnostics

The source checker adds an explanation only after its existing unresolved-name
or implicit-owner-loss rejection. It preserves the original diagnostic code,
source span, checking order and limits. It does not inspect or evaluate call
arguments to decide whether an unresolved Rust-shaped name deserves a hint.
Consequently `drop(q)` keeps the existing unresolved-name priority, and
`drop(0)` must not be described as destroying a quantum argument. A resolved
user function receives ordinary call checks. A local runtime value named
`drop` retains the earlier not-callable category rather than being reclassified
as an absent builtin.

An ownership explanation states that scope exit is not physical destruction
and distinguishes measurement, discard, reset and checked cleanup. It does not
choose a repair on the programmer's behalf: those operations have different
types, effects and meanings, and a requested concrete profile may not support
all of them. Existing use-after-move, arity, type, effect, access and capacity
failures retain their own categories. Text and JSON diagnostics describe
rejections; neither carries semantic evidence or grants acceptance. External
qlippy integration is outside this work; actual Qleisli diagnostics remain
part of the source interface.

## False-friend audit

The table covers #68's original checklist and its implicit-operation addendum.
"Absent" means there is no such construct in the current source grammar or
builtin catalog. A parser or name refusal for it does not implement its future
ownership law, adopt a pending child design, or forbid an otherwise valid
ordinary user-defined identifier with the same spelling.

| Rust-shaped concern | Current Qleisli boundary and remaining decision |
| --- | --- |
| `drop` | No builtin or generic quantum destruction. Ordinary classical data may be ignored; a resolved user consumer, including one named `drop`, must pass normal checks. |
| Implicit scope destruction | Live quantum owners must escape through the result or an admitted explicit transition. Scope closure emits no hidden physical disposal. |
| `Clone` | No trait or builtin. Duplicating a live owner rejects; reusable static descriptions do not contain that owner. |
| `Copy` | Ordinary data reuse is permitted; quantum-containing products remain linear. No Rust marker trait is imported. |
| `forget` / `mem::forget` | No privileged forget operation. An ordinary resolved function cannot hide a live owner from its body's checks. |
| `ManuallyDrop` | No wrapper type, destructor suspension or owner-accounting exception. |
| Unchecked casts / `transmute` | No unchecked cast or verification bypass. Exact type trees, basis tags and ordered axes remain checked. |
| `as` | The contextual `as` in `basis q as p { e }` names an ordinary basis pattern for a checked coherent map. It is not a Rust value cast or implicit physical layout conversion; general casts are absent. |
| Early `return` | No early-return construct; the tail expression supplies the block result. Exit/path obligations and wider surface classification remain in [#196](https://github.com/MGYamada/Qleisli/issues/196). |
| Panic / unwinding | No source exception or unwinding construct. Host/tool failure is not an admitted path that disposes of owners. See the [verified-core failure model](source-text.md#checking-failures-and-quantum-execution). |
| Destructor-like trait hooks | No trait/impl dispatch or implicit cleanup hook. Checked scoped cleanup has its separate rule. |
| Conflating measure, discard, release, reset or uncompute | Their explicit transitions are distinguished above; no generic spelling or scope exit selects among them. |
| Assignment to initialized places | Quantum-containing places cannot be assigned to, including nested products and zero-width owners. `q = h(q)` is forbidden replacement; `let q = h(q)` consumes the old owner before rebinding. A consumed binding cannot be refilled by assignment. Bare lexical assignments receive a typed refusal before RHS checking; field/index assignment remains unsupported syntax. Ordinary/static assignment is also unsupported in this profile, with a distinct diagnostic. See [#73](https://github.com/MGYamada/Qleisli/issues/73). |
| Indexing / `Index` / `IndexMut` | Explicit `excl q[i]` / `ctrl q[a..b]` select statically bounded, ordered places under the [selector rules](elaboration.md#static-ordered-axis-places). They do not form ordinary values or references, move owners by bare indexing, or use indexing traits/runtime bounds checks. Existing explicit `take_bit[n,k]` / `put_bit[n,k]` consume/return owners with checked static bounds and ordered axes. |
| Method-call autoref/autoderef | No method-call syntax or hidden receiver conversion. Quantum autoref, autoderef, `Deref`/`DerefMut` dispatch, receiver coercion and access-contract overload selection never insert or forward `excl`/`ctrl`. Explicit first-order calls keep their declared argument types and access modes; see [receiver access](#explicit-calls-and-receiver-access). |
| `mem::swap` / exchange / physical SWAP | No builtin swap. Provisional ordinary `std::gate::swap` implements physical two-Bit SWAP; `std::gate::permute_axes` explicitly reorders its two axes with witness `[1,0]`. Neither exchanges live bindings. Matrix equality grants no unchecked routing/cost replacement. General interfaces remain in [#76](https://github.com/MGYamada/Qleisli/issues/76). |
| `mut` | A mutable-binding marker grants no quantum access. `let mut q = ...` rejects for a quantum-containing value; ordinary mutable bindings also remain unsupported, with a separate diagnostic. Gates already change states through consuming calls and explicit returned owners; `excl`/`ctrl` need no marker. The ordinary identifier `mut`, as in `let mut = 0`, retains normal name rules. See [#77](https://github.com/MGYamada/Qleisli/issues/77). |
| Ordinary `for` / `IntoIterator` over quantum data | No ordinary iterator/trait machinery. Bounded `qfor static ... carry ... yield ...` explicitly threads quantum-containing carry and checks its body even for an empty range. `for static` permits only ordinary carry. Neither has hidden quantum capture or runtime iteration; see [Static language](static-language.md). |
| `Default` | Unavailable for live quantum-containing types, including `Q<Unit>` and nested owners. Ordinary/static data construction and explicit quantum preparation retain their distinct contracts above; normal user functions named `default` remain checked calls. |
| Wildcard / rest patterns | `_` may ignore only unrestricted data; every quantum-containing matched field remains linear. Ordinary tuple patterns retain exact immediate shape. Rest patterns are absent; their future omission must not hide owners. |
| `?`, assertions and early failure | No propagation operator, assertion builtin or language unwind path. A user function's name does not supply such behavior. See the [checking and execution boundary](source-text.md#checking-failures-and-quantum-execution). |
| Shared `&` / exclusive `&mut` / `ctrl` | Whole-owner `excl` and finite-project `ctrl` calls have the rules below. Selected Raw checking admits retained concrete control calls after fresh native sector checks, including static indexed/slice arguments; hierarchy and checker-free control emission refuse them. Stored references, escaping views and access parameter declarations remain unsupported. Control may accumulate phase or entanglement. General access remains in [#29](https://github.com/MGYamada/Qleisli/issues/29) / [#69](https://github.com/MGYamada/Qleisli/issues/69). |
| `borrow` versus clean/dirty workspace | `borrow` has no builtin quantum-resource semantics. `excl`/`ctrl` express access; clean/dirty express independent workspace restoration obligations. See the [access vocabulary](#access-vocabulary-and-workspace-contracts). |

## Explicit calls and receiver access

Quantum access is written at an ordinary call site, for example `h(excl q)`
or `controlled(U)(ctrl c, excl q)`. The receiver spellings `q.h()` and
`target.controlled_u(control)` are unsupported. The compiler does not guess
which access contract their author intended. An ordinary wrapper function
must expose its actual interface and pass the same ownership, effect and
access checks; a wrapper name grants no hidden projection or forwarding.
There are no user-defined `Deref`/`DerefMut` hooks or receiver adjustments.

Field/method receiver syntax is currently absent for ordinary classical and
static values as well. Their ordinary first-order calls are unaffected. A
syntax diagnostic therefore reports the unsupported form without guessing
the receiver's type and conditions its `excl`/`ctrl` advice on quantum access.
It does not mechanically rewrite a receiver into either access mode.

Explicit call lowering follows the [access and evaluation rules](elaboration.md)
and the native obligations below. Receiver sugar supplies no alternative
acceptance route or evidence.

## Access vocabulary and workspace contracts

The [#71 decision](https://github.com/MGYamada/Qleisli/issues/71) uses **access**
for public quantum operation authority. `excl` grants temporary exclusive
arbitrary coherent access over its exact footprint; `ctrl` grants the distinct
basis-sector-preserving coherent access. Neither means state restoration,
separability or cleanliness. An `excl` argument does not require a `mut`
binding. Rust `&mut` is not a Qleisli access spelling and is not automatically
converted to either mode.

Clean and dirty describe independent workspace contracts. Clean discharge
requires the specified exact known state; dirty discharge requires exact
restoration for every initial state and external reference. Ending an access
does not discharge either obligation. General clean/dirty source forms remain
unsupported; existing checked `with_computed` has its own bounded contract.
See [checked cleanup](#checked-cleanup-is-a-separate-contract).

`borrow` is not reserved and has no builtin quantum-resource semantics.
Unsupported `borrow q` receives a located syntax diagnostic, without inferring
whether Rust access or dirty workspace was intended. Ordinary declarations,
calls and bindings named `borrow` retain normal checking; their name grants no
access, restoration or ownership permission. Ownership transfer is expressed
by the existing consuming calls and bindings; this terminology does not add a
standalone `move q` form. Internal Rust documentation may still discuss normal
borrowing of compiler data structures.

## Whole-owner exclusive calls

`h(excl q)` temporarily supplies the live lexical owner `q` to the existing
consuming call and retains its returned quantum value on the same binder.
The access call itself has ordinary type `Unit`. A joint call such as
`cnot(excl c, excl t)` requires distinct owners and returns them internally
in argument order. Each argument must name one whole `Q<A>` owner; ordinary
data and tuples containing several owners are not access places.

The callee must have actual inferred `Unitary` effect. An annotation does not
override its body. Its result must have exactly the original owner type for
one argument, or the ordered tuple of those owner types for several arguments.
Exact basis trees and owner partition matter, including `Q<Unit>`; equal bit
width is insufficient. The callee executes once. Access closure inserts no
inverse, reset, discard, release or fresh preparation. Returned values retain
their changed state and phase, even across a nested lexical boundary.

```qli
use std::quantum::init0;
use std::quantum::x;
use std::observe::measure_z;

observe fn main() -> Bit {
    let q = init0();
    x(excl q);
    measure_z(q)
}
```

No mutable-binding marker is required. Consuming `q` after the access makes it
unavailable as usual; access cannot revive a spent or hidden owner. Duplicate
arguments, a changed result interface and measurement through `excl` reject.
Names `excl` and `ctrl` remain ordinary identifiers outside argument markers.
The current call form requires every runtime argument to use an access marker;
mixed ordinary/access arguments, escaping handles and access-parameter
declarations remain unimplemented. Indexed selections have a common AST and
static bounds/disjointness judgment. Selected Raw lowering partitions and
reassembles their updated owners; finite-project and hierarchical lowering
remain unsupported. See [static places](elaboration.md#static-ordered-axis-places).
Selected-source preparation
retains `ctrl` roles as obligations with original source identities and spans.
`ElaboratedProgram::lower_raw_with_kernel` and selected CLI Raw checking require
fresh native decisions for every retained concrete control-bearing definition
and the selected root, sharing one exact-work budget. Each control call is
bound to the actual decoded instruction interval and original ordered owners.
Every original obligation must have a concrete call in **each** retained
specialization of its declaration. The checker also elaborates unused closed
functions whose original resolved dependencies reach a control obligation,
sharing the selected graph's existing call, fold, depth and storage bounds.
It adds no public entry or invented static argument and leaves the execution
root unchanged. Additional bodies retain their Meaning/refinement obligations.
Unclosed generic declarations and missing calls in unselected static branches
or empty loops remain unsupported; a different specialization cannot supply
their evidence. Zero-count providers with retained
bodies are checked independently of their execution count. Symbolic inverse or
controlled transforms containing access obligations remain unsupported.
`lower_raw`, checker-free `emit-proposal`, and hierarchical lowering still
refuse control obligations. Final Raw consumption freshly checks the artifact
and replays its source calls again; no source annotation or earlier native
success substitutes for those checks. Diagnostics retain the original call's
module and location. This limited implementation does not complete the general
access Issues or establish a Lean source-preservation theorem.

Unsupported Rust reference notation receives a syntax explanation: for quantum
access, `excl` grants arbitrary coherent access, while `ctrl` requires the
computational-basis sector condition. The lexer does not infer that the
expression is quantum and does not rewrite `&` into `ctrl`. Native control
refusals explain that control is not read-only, phase kickback is permitted,
and arbitrary coherent access requires `excl`; this guidance does not bypass
effect, alias or interface checks.

### Whole-owner coherent control

The finite project checker/compiler admits `cnot(ctrl c, excl t)` using the
same distinct live-owner, actual Unitary effect and exact returned-interface
rules. It independently submits the actual emitted call interval, original
ordered owner ports, complete basis forest and requested control axes to the
native `control-owners` checker. Success of that fresh decision is required
before retaining the updated owners. The complete generated program also
passes ordinary native acceptance; no annotation or cached decision replaces
either check. Missing, incompatible or failed checkers refuse.

`ctrl` requires computational-basis sector preservation, not an unchanged
quantum state or read-only access. Phase kickback and entanglement are allowed.
H and X on a control owner reject despite being Unitary; CNOT preserves its
control's sectors but not its target's. Exact scalar phase on `Q<Unit>` is
retained. Control axes follow original argument/owner wire order, not sorted
wire identifiers. Each call occurrence is checked, including nested calls and
unused concrete declarations. Access exit neither restores the old state nor
releases workspace. Overlapping arguments still reject.

This path uses the existing bounded exact native profile (at most six physical
input bits for a control decision), with cumulative exact work charged to the
existing compiler budget. It does not establish a general source-preservation
theorem, quantitative resource correspondence or scheduling permission.
General access lifetimes, stored views and declared access interfaces remain
unfinished. The supported call-formed exit points follow the
[evaluation and owner lifetime rules](elaboration.md#evaluation-and-owner-lifetime-boundaries).

## Acceptance and evidence

The common original-source checker verifies complete declarations and bodies
before concrete eligibility. Diagnostics do not alter those judgments, issue
accepted handles or replace the independent native Lean gate. The
[production boundary](production-boundary.md) and
[functional boundary](functional-boundary.md) retain their current source,
concrete-profile and preservation limits.

These rules preserve the adopted QS, PR, quantitative RS and EXACT obligations
and the two scoped ordinary QLV1 ownership/classical-scope guarantees. They
establish no broader discharge, new primitive admission, resource theorem or
release approval. In particular, the absence of implicit owner loss is not a
proof of a quantitative resource bound or completed source preservation.
