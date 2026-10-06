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
creates a fresh zero qubit with Iso action. `unit(())` creates one fresh
zero-axis `Q<Unit>` owner with exact coefficient `+1` and Unitary action;
it allocates no physical wire. `empty()` introduces the separately typed
`Q<Bits<0>>` owner. Neither zero physical width nor an ordinary Unit argument
makes the returned owner unrestricted. Explicit `finish` preserves preceding
scalar phase, and checked scoped cleanup retains its all-input fixed-state
contract. Default construction provides no hidden clean workspace or cleanup.
General clean/dirty facilities and quantitative resource certification retain
their separate pending obligations; a source effect is not a resource bound.

An ordinary function may be named `default`. For example, this checked function
fragment has explicit preparation and principal Iso effect:

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
| `adjoint(...)` or an admitted inverse construction | Reverses the specified operation only with the required checked access. The call consumes its input and returns an owner; uncomputation alone does not discharge that returned owner or prove it clean. |
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
| Panic / unwinding | No source exception or unwinding construct. Host/tool failure is not an admitted path that disposes of owners. The complete failure model remains in [#86](https://github.com/MGYamada/Qleisli/issues/86). |
| Destructor-like trait hooks | No trait/impl dispatch or implicit cleanup hook. Checked scoped cleanup has its separate rule. |
| Conflating measure, discard, release, reset or uncompute | Their explicit transitions are distinguished above; no generic spelling or scope exit selects among them. |
| Assignment to initialized places | Place assignment is absent. Checked RHS-first `let` rebinding is supported; shadowing a still-live owner rejects. Refill, definite initialization and aggregate-place rules remain in [#73](https://github.com/MGYamada/Qleisli/issues/73). |
| Indexing / `Index` / `IndexMut` | No runtime place indexing or indexing traits. Existing explicit `take_bit[n,k]` / `put_bit[n,k]` consume/return owners with checked static bounds and ordered axes. Place/view/access decisions remain in [#74](https://github.com/MGYamada/Qleisli/issues/74). |
| Method-call autoref/autoderef | No method-call syntax or hidden reference conversion. Explicit first-order calls keep their declared argument types; future access-mode inference is tracked in [#75](https://github.com/MGYamada/Qleisli/issues/75). |
| `mem::swap` / exchange / physical SWAP | No builtin swap. Binding routing, an ordered axis map and a quantum gate are distinct contracts; tuple spelling grants no physical interchange. Their public boundary remains in [#76](https://github.com/MGYamada/Qleisli/issues/76). |
| `mut` | No mutable-binding or place-assignment construct. Quantum gates already change states through consuming calls and explicit returned owners. Future binding mutability is tracked in [#77](https://github.com/MGYamada/Qleisli/issues/77). |
| Ordinary `for` / `IntoIterator` over quantum data | No ordinary iterator/trait machinery. Bounded `qfor static ... carry ... yield ...` explicitly threads quantum-containing carry and checks its body even for an empty range. `for static` permits only ordinary carry. Neither has hidden quantum capture or runtime iteration; see [Static language](static-language.md). |
| `Default` | Unavailable for live quantum-containing types, including `Q<Unit>` and nested owners. Ordinary/static data construction and explicit quantum preparation retain their distinct contracts above; normal user functions named `default` remain checked calls. |
| Wildcard / rest patterns | `_` may ignore only unrestricted data; every quantum-containing matched field remains linear. Ordinary tuple patterns retain exact immediate shape. Rest patterns are absent; their future omission must not hide owners. |
| `?`, assertions and early failure | No propagation operator, assertion builtin or language unwind path. A user function's name does not supply such behavior. Complete failure/path semantics remain in #86. |
| Shared `&` / exclusive `&mut` / `ctrl` | Reference/access-expression syntax is absent. Existing controlled operations are explicit and retain their owners; control may accumulate phase or entanglement. Temporary exclusive access and basis-preserving coherent access remain in [#29](https://github.com/MGYamada/Qleisli/issues/29) / [#69](https://github.com/MGYamada/Qleisli/issues/69). |
| `borrow` versus clean/dirty workspace | There is no builtin workspace `borrow` form. Access and state-restoration obligations are separate; the public terminology/reserved-word decision remains in [#71](https://github.com/MGYamada/Qleisli/issues/71). |

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
