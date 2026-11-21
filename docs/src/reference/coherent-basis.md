# Coherent basis maps

A **coherent basis map** applies a function on basis labels to one quantum
owner. A program uses it to compute on the labels of a quantum state, for
example to flip a bit or to copy a label, without a measurement.

The expression `basis q as p { e }` consumes a `Q<A>` owner and returns a
`Q<B>` owner. It sends each basis state `|a>` to `|f(a)>` with coefficient
`+1`, where `f` is the function that the body `e` computes. The function `f`
must be injective: no two inputs get the same label.

This chapter is subordinate to the [authority hierarchy](authority.md). It
uses the [ordinary types and quantum-owner rules](type-model.md).

## Syntax

```text
CoherentBasisExpr ::= "basis" Expr "as" Pattern "{" BasisExpr "}"
```

`Expr` is the **input**, `Pattern` is the **binder** and `BasisExpr` is the
**body**. `basis` is a reserved word. `as` is contextual: it is a keyword at
this separator and an identifier elsewhere.

## The input

The input supplies the owner that the map transforms. The input is an existing
quantum input expression.

Rules:

- The input must produce **one** `Q<A>` owner. A tuple `(Q<A>,Q<B>)` is not one
  owner, and the checker joins nothing implicitly. An input with another owner
  shape is a type error.
- The input evaluates completely, and once, before the binder is bound.
- The input may contain an ordinary call or another coherent map. The checker
  checks its effects and its use of owners before this map.
- The map consumes the input owner once and returns one `Q<B>` owner. Using
  the old binding again is an ownership error.

## The binder

The binder gives names to the parts of an input label, so that the body can
use them. It is a pattern over the ordinary basis tree `A`. It uses the
existing pattern forms: a name, a wildcard, Unit and an ordered tuple.

Rules:

- The complete basis tree `A` determines the type of the pattern. Its width
  alone does not. The arity and the nesting of the pattern must match `A`.
- The binder binds ordinary labels of `A` for this basis computation. It never
  binds runtime quantum owners.
- A tuple pattern over `A` performs no runtime quantum `split`.
- Duplicate names and collisions with static names are errors, as for every
  ordinary pattern.

## The body

The body computes the output label from the labels that the binder binds. The
braces hold one `BasisExpr`. They do not hold an ordinary block. A `BasisExpr`
has one of these forms:

| Form | Meaning |
| --- | --- |
| A name that the binder binds | That label |
| `()` | The Unit label |
| `0`, `1` | A Bit label |
| `(e)`, `(e1, e2, ...)` | Grouping, and an ordered tuple |
| `not e`, `e1 and e2`, `e1 xor e2` | Boolean operations on Bit labels |
| `f(e1, ...)` | A call of a declared `classical fn` |
| `empty_bits()` | The `Bits<0>` label |
| `word[k]` | Coordinate `k` of a `Bits<n>` label |
| `Type::Variant`, `Type { field: e, ... }`, `e.field` | A nominal label, a record label and a field of one |
| `match e { Type::Variant => e1, ... }` | Selection on a nominal label |

[Total classical declarations](source-text.md#total-classical-declarations)
gives the rules of `classical fn`, and
[Parsed finite type declarations](source-text.md#parsed-finite-type-declarations)
gives the nominal forms. A `classical fn` declares a total ordinary
computation. A program may also call it on ordinary runtime values, including
measured Bits.

Rules:

- A call must name a declared `classical fn`. It must match the arity and the
  types of that function's argument list. A call of an ordinary or a measuring
  function is rejected, because that function is not a classical function.
- `empty_bits()` is the language primitive constructor that takes no argument.
  It needs no import, and it introduces no quantum owner. The checker requires
  the resolved identity of the primitive and its checked signature. An
  ordinary function with the same spelling therefore gains no special
  permission.
- A coordinate read `word[k]` must use a literal `k` with `k < n`, as the
  ordinary `Bits<n>` rule requires.
- The body must not call any other quantum primitive.
- The body must not contain `let`, a statement sequence, a semicolon, a
  measurement, an ordinary runtime call or a nested coherent map.
- The runtime values of the body are the labels that the binder binds, and
  nothing else. The body must not capture an outer ordinary value or an outer
  quantum owner, even an immutable one. An outer value in the body is unbound.
- Declared classical functions, and the static premises that their checking
  needs, keep their normal resolution and dependency checks. A retained static
  premise does not count as a capture of an outer runtime value.
- The body may nest to 64 levels.

## Meaning

This section states what the map does to a quantum state. For fixed valid
static premises, the body denotes a total ordinary function `f: A -> B`. The
map applies `f` to the label of each basis state and acts linearly:

```text
V_f |a> = |f(a)>
V_f (sum_a alpha_a |a>) = sum_a alpha_a |f(a)>
```

Rules:

- `f` must be injective on the complete domain `A`. A body that gives two
  inputs the same label is an error (`ownership`).
- The body must have one output type for every input label.
- Every basis transition has coefficient **`+1`**. The map preserves the input
  amplitudes and their phase. It does not choose a phase convention after the
  fact.
- With an arbitrary retained reference `R`, the action is `V_f tensor I_R`.
  The input need not be separable from `R`.
- The complete ordered basis tree `B` fixes the output labels and the axis
  order. The checker inserts no reassociation, flattening, same-width
  conversion or axis permutation.
- The map discards no input and measures no label.

## Effects

This section gives the effect that the checker assigns to a coherent basis
map. Injectivity makes the map an isometry. A bijection between equal finite
domains is unitary. A map into a larger basis space has the Isometry effect.

Rules:

- The effect of the expression includes every operation that the input
  expression performs.
- The checker records an injectivity obligation. It determines the effect
  conservatively from the basis premises and the width premises that are
  available.
- Equal width is an effect fact. It is not evidence of injectivity.
- An annotation, a favourable example, a runtime test or a name must not
  replace an unresolved check.

> **Implementation note.** The finite lowering evaluates every input label in
> its supported bounded domain, rejects repeated output labels and constructs a
> `LiftBasis` table. It preserves the ordered wire list and extends it for an
> admitted larger output basis. The native checker checks the resulting
> proposal independently.

## Examples

The checker accepts both functions:

```qli
fn invert(q: Q<Bit>) -> Q<Bit> {
    basis q as x { not x }
}

fn correlate(q: Q<Bit>) -> Q<(Bit,Bit)> {
    basis q as x { (x,x) }
}
```

`correlate` maps `alpha|0> + beta|1>` to `alpha|00> + beta|11>`. It can create
entanglement. It does not produce the tensor square of an arbitrary quantum
state. Copying an ordinary basis label inside an injective map is therefore
distinct from duplicating a quantum owner.

The checker rejects `basis q as x { 0 }` on `Q<Bit>`, because the two inputs
collide. An ordinary classical `if` or a runtime `let` does not inspect an
unmeasured quantum input, and `pure 0` does not prepare one.

The Unit case has the same contract. `basis q as () { () }` has coefficient
`+1` on the one-dimensional basis and returns a `Q<Unit>` owner. It preserves
any scalar phase already on `q`. A physical width of zero does not let that
owner disappear.

## Removed `do` and `pure` forms

`do` and `pure` are reserved words that the parser rejects. They have no
accepted alias, and they have no meaning as a general monadic bind, an
injection or a state preparation. Qleisli has no general quantum-core `Monad`
and no `do` syntax.

| Removed source | Source |
| --- | --- |
| `do x <- q; pure not x` | `basis q as x { not x }` |
| `do (x,y) <- q; pure (y,x)` | `basis q as (x,y) { (y,x) }` |
| `do () <- q; pure ()` | `basis q as () { () }` |

Rules:

- A migration keeps the same input expression, pattern and basis expression.
- A rewrite cannot repair a noninjective body, an outer capture, owner reuse or
  an unsupported concrete profile.
- The parser rejects both words. Its message gives the `basis q as p { e }`
  form. The message states that the form is a coherent basis map and that it
  is neither a monadic bind nor a measurement. It also states that no `pure`
  preparation operation exists. The message must not suggest that an old
  spelling is accepted.

## Diagnostics

Each failure keeps the stage that finds it:

| Failure | Report |
| --- | --- |
| An input with the wrong owner shape | A type error |
| An outer value in the body | An unbound name |
| A call of an ordinary or a measuring function in the body | Not a classical function |
| A finite map with colliding labels | An injectivity failure, with the code `ownership` |
| Reuse of the consumed input | An ownership error |

Text and JSON diagnostics retain the original source locations and the
frontend's public code and message. A syntax suggestion must not bypass these
semantic requirements. [Diagnostics and recovery](diagnostics.md) gives the
codes of each route.

<a id="concrete-profiles-and-proof-boundary"></a>

## Status and limits

Finite loading and selected loading treat the source form alike. Both parse
it into the same `CoherentLift` syntax tree, and both apply the same complete
source judgment. The profiles differ in the maps that they lower:

| Profile | Coherent basis maps that it lowers |
| --- | --- |
| Finite project | Complete closed Basis/Nat instances, and ordinary and quantum registers, within its twelve-bit capacity |
| Selected Raw | Tables of at most eight input and output bits, within the type-tree, depth, work, call and storage bounds of the profile |
| Selected hierarchy | Only the singleton coefficient-`+1` table `[0]`: from `Q<Unit>` or `Q<Bits<0>>` to either zero-width type, or to `Q<Bit>` prepared in zero |

Limits that apply to these profiles:

- Selected elaboration retains the original identities of the binder, of the
  use site and of the declaration. It evaluates the complete bounded label
  domain, including closed classical helpers.
- Selected Raw lowering emits `LiftBasis`. A separate source-step comparison
  binds the retained table, the ordered wires, the owner transitions and the
  effects to the emitted instructions.
- The opaque `SourceStep` exposes `kind() == "lift_basis"` and a read-only
  `basis_table()` view of the untrusted coefficient-`+1` labels. This view
  supplies no accepted handle and no proof of the preceding source
  elaboration.
- A square map may use the independently checked finite operation-access path.
  Unitarity alone grants no inverse and no control.
- In the selected hierarchy profile, the structural and preparation proposals
  retain the original source step, the complete ordered owner frames and the
  root and child links. They require independent native acceptance. This
  bounded untrusted replay is not a proof of source elaboration or of general
  source preservation.
- The selected hierarchy profile does not support other coherent tables. It
  does not support static operation transforms that depend on a table,
  including zero repetition. It does not support preparation after
  observation.
- Selected roots and ordinary project roots can use coherent basis maps over
  nominal labels, as the [type model](type-model.md) describes.
- `Bits<0>` is never replaced by Unit, and its quantum owner stays linear.
- Every concrete unused finite declaration requires checking.
- A lowering failure or a native failure cannot fall back to a weaker
  acceptance route.

Proof status:

- The form creates no semantic primitive, native schema, accepted handle,
  constitutional interpretation or guarantee admission.
- The scoped ordinary QLV1 ownership and classical-scope guarantees retain
  their recorded premises.
- Full QS, source preservation, forward PR correspondence and quantitative RS
  are pending under the adopted interpretations and the exactness boundary.

Tooling:

- The public Qleisli library and the CLI produce the diagnostics above.
- The external qargo project implements qlippy as a consumer of Qleisli
  checking and diagnostics. This repository supplies no qlippy command, and
  this chapter claims no qlippy integration.
- A later claim of qlippy support must validate the consumer version and its
  diagnostic forwarding against this grammar. A Reference contract or a
  Qleisli CLI test alone does not establish that integration.

## History

- The `basis q as p { e }` expression was adopted for edition 2026 through
  [Issue #81](https://github.com/MGYamada/Qleisli/issues/81). This chapter
  first named `0.3.0-beta` as its release; the changelog records the change
  under 0.3.0-alpha.
- The expression replaced the Haskell-style `do ... pure ...` form. The syntax
  changed. The CoherentLift semantic obligation and the finite lowering are
  those of the earlier form.
- The removal of `do` and `pure` is a concrete consequence of the
  [Haskell/Qleisli boundary in #80](https://github.com/MGYamada/Qleisli/issues/80).
  The migration does not complete that broader boundary audit.
- The maintainer excluded the qlippy consumer integration from the completion
  conditions of the migration by an explicit decision.
- Historical first sources, diagnostics and artifacts are unchanged. They sit
  beside explicit migration derivatives.

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
