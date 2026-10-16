# Coherent basis maps

This chapter specifies the coherent basis-map expression adopted for
`0.3.0-beta` in constitutional edition 2026 through
[Issue #81](https://github.com/MGYamada/Qleisli/issues/81). It is subordinate to
the [authority hierarchy](authority.md) and uses the existing
[ordinary types and quantum-owner rules](type-model.md). The syntax changes;
the existing CoherentLift semantic obligation and finite lowering remain.

## Syntax and scope

```text
CoherentBasisExpr ::= "basis" Expr "as" Pattern "{" BasisExpr "}"
```

`Expr` is an existing quantum input expression. It evaluates completely and
once before the pattern is bound. It must produce **one** `Q<A>` owner. A
tuple `(Q<A>,Q<B>)` is not one such owner and is not implicitly joined. The
complete ordinary basis tree A, rather than its width alone, determines the
pattern's type.

`Pattern` uses the existing name, wildcard, Unit and ordered tuple forms.
It binds ordinary labels of A for this basis computation, never runtime
quantum owners. Exact arity and nesting remain mandatory. An ordinary tuple
pattern over A does not perform runtime quantum `split`. Duplicate names and
static-name collisions retain the ordinary pattern checks.

The braces contain exactly one existing `BasisExpr`, not an ordinary block.
The admitted forms are bound labels, `()`, `0`/`1`, grouping, ordered tuples,
`not`, `and`, `xor`, calls to declared `classical fn` functions with their exact
argument-list arity and types, and the existing nullary ordinary
`empty_bits()` constructor imported from `std::classical`. The constructor produces the exact
`Bits<0>` label; it introduces no quantum owner. Its resolved primitive identity
and checked signature are required, so an ordinary same-spelled function gains
no special permission. Other sealed quantum calls remain excluded. There is no `let`, statement sequence, semicolon,
measurement, ordinary runtime call or nested coherent map in this body.
`classical fn` declares total ordinary computations. Its body can also be called
on ordinary runtime values, including measured Bits, under the
[classical declaration rules](source-text.md#total-classical-declarations).

The body's runtime-value context consists only of its pattern's ordinary
labels. It cannot capture an outer ordinary value or quantum owner, even if
that value is immutable. Declared classical functions and the static premises
needed for their checking retain their normal resolution and dependency
checks. A retained static premise is not an outer runtime-value capture.
The input expression may itself contain an ordinary call or another coherent
map; that input's effects and owner use remain checked before this map.

`basis` is reserved. `as` is contextual at this separator and remains an
identifier elsewhere. `do` and `pure` are retained only as reserved removal
tokens. They have no accepted alias, general monadic bind, injection or state
preparation meaning.

As this concrete consequence of the [Haskell/Qleisli boundary in #80](https://github.com/MGYamada/Qleisli/issues/80),
Qleisli has no general quantum-core `Monad` or `do` syntax. This migration does
not complete that broader boundary audit.

## Meaning, injectivity and effects

For fixed valid static premises, the body denotes a total ordinary function
`f: A -> B`. A coherent map requires f to be injective on the complete domain.
Its exact linear action is

```text
V_f |a> = |f(a)>
V_f (sum_a alpha_a |a>) = sum_a alpha_a |f(a)>
```

Every basis transition has coefficient **`+1`**. The map preserves input
amplitudes and their phase, rather than choosing a phase convention after the
fact. With an arbitrary retained reference R its action is `V_f tensor I_R`;
the input need not be separable from R. B's complete ordered basis tree fixes
the output labels and axis order. No implicit reassociation, flattening,
same-width conversion or axis permutation is inserted.

Injectivity makes this an isometry. A bijection between equal finite domains
is unitary; a map into a larger basis space contributes Isometry effect. The
common source checker records an injectivity obligation and determines its
effect conservatively from the available exact basis/width premises. Equal
width is an effect fact, not injectivity evidence. An unresolved check cannot
be replaced by an annotation, favorable example, runtime test or name.

The finite lowering evaluates every input label in its supported bounded
domain, requires one fixed exact output type, rejects repeated output labels
and constructs the existing `LiftBasis` table. It preserves the existing
ordered wire list and extends it for an admitted larger output basis. The
native checker independently checks the resulting proposal. The expression
consumes the input owner once and returns one `Q<B>` owner; the old binding
cannot be reused. Its total effect also includes every operation performed by
the input expression. It does not discard an input or measure a label.

For example:

```qli
fn invert(q: Q<Bit>) -> Q<Bit> {
    basis q as x { not x }
}

fn correlate(q: Q<Bit>) -> Q<(Bit,Bit)> {
    basis q as x { (x,x) }
}
```

The second function maps `alpha|0> + beta|1>` to
`alpha|00> + beta|11>`. It can create entanglement; it does not produce the
tensor square of an arbitrary quantum state. Copying an ordinary basis label
inside an injective map is therefore distinct from duplicating a quantum
owner. In contrast, `basis q as x { 0 }` on `Q<Bit>` rejects: the two inputs
collide. An ordinary classical `if` or runtime `let` does not inspect an
unmeasured quantum input, and `pure 0` does not prepare one.

The Unit case has the same contract: `basis q as () { () }` has coefficient
`+1` on the one-dimensional basis and returns a `Q<Unit>` owner. It preserves
any scalar phase already on q. That owner cannot disappear because its
physical width is zero.

## Migration and diagnostics

| Removed source | Current source |
| --- | --- |
| `do x <- q; pure not x` | `basis q as x { not x }` |
| `do (x,y) <- q; pure (y,x)` | `basis q as (x,y) { (y,x) }` |
| `do () <- q; pure ()` | `basis q as () { () }` |

Keep the same input expression, pattern and basis expression. A rewrite cannot
repair a noninjective body, outer capture, owner reuse or unsupported concrete
profile. The parser rejects both retired tokens and explains the canonical
`basis q as p { e }` form, coherent basis-map meaning, lack of monadic bind or
measurement, and lack of a `pure` preparation operation. It must not suggest
that an old spelling remains accepted.

Other diagnostics retain their actual stage: an input with the wrong owner
shape is a type error; an isolated body's outer value is unbound; an ordinary
or measuring call is not a classical function; a finite map with colliding labels
fails injectivity; reuse of the consumed input fails ownership. Text and JSON
diagnostics retain original source locations and the frontend's public code
and message. A syntax suggestion must not bypass these semantic requirements.

The public Qleisli library and CLI produce these frontend diagnostics. The
external qargo project implements qlippy as a consumer of Qleisli checking and
diagnostics; this repository supplies no qlippy command. Its actual consumer
integration is excluded from this migration's completion conditions by the
maintainer's explicit decision. No updated qlippy integration is claimed.
Any later claim of support must validate its actual consumer version and
diagnostic forwarding against this grammar; a Reference contract or a
Qleisli CLI test alone does not establish that integration.

## Concrete profiles and proof boundary

Both finite and selected loading parse this form into the same original
`CoherentLift` AST and apply the same complete source judgment. Selected
elaboration retains the original binder, use-site and declaration identities
and evaluates the complete bounded label domain, including closed classical
helpers. Selected Raw lowering emits the existing `LiftBasis`; its separate
source-step comparison binds the exact retained table, ordered wires, owner
transitions and effects to the emitted instructions. The opaque `SourceStep`
exposes `kind() == "lift_basis"` and a read-only `basis_table()` view of the
untrusted coefficient-+1 labels. This view supplies no accepted handle or proof
of the preceding source elaboration.

Selected tables require at most eight input/output bits and preserve the
existing type-tree, depth, work, call and storage bounds. Square maps may use
the existing independently checked finite operation-access path; unitarity
alone grants no inverse or control. Selected hierarchy lowering admits ordinary
coherent lifts only for the exact singleton coefficient-+1 table `[0]`:
`Q<Unit>` or `Q<Bits<0>>` to either zero-width type, or to `Q<Bit>` prepared in
zero. The structural/preparation proposals retain the original source step,
complete ordered owner frames and actual root/child links, and still require
independent native acceptance. This bounded untrusted replay is not a proof of
source elaboration or general source preservation. Other coherent tables and
table-dependent static operation transforms, including zero repetition, remain
unsupported. Preparation after observation remains unsupported in this
hierarchy profile. Finite project lowering admits complete
closed Basis/Nat instances and ordinary/quantum registers within its twelve-bit
capacity. `Bits<0>` is
never replaced by Unit, and its quantum owner remains linear. Every concrete
unused finite declaration still requires checking. A lowering or native failure
cannot fall back to a weaker acceptance route.

This migration creates no new semantic primitive, native schema, accepted
handle, constitutional interpretation or guarantee admission. The scoped
ordinary QLV1 ownership and classical-scope guarantees retain their recorded
premises. Full QS, source preservation, forward PR correspondence and
quantitative RS remain separately pending under the adopted interpretations
and exactness boundary. Historical first sources, diagnostics and artifacts
remain unchanged beside explicit current migration derivatives.

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
