# Type system: current finite source contract

Status: **normative for product 0.2.0**, 2026-09-29. This document is
the consolidated type contract. The [grammar](syntax-v0.md),
[typing/effect rules](source-typing-rules.md), [ownership rules](source-resource-rules.md)
and [tuple migration](tuple-shapes.md) refine its syntax, judgments and migration.
Current implementation evidence is recorded in [conformance](specification-status.md).
This specification is not a claim of a general compiler soundness proof.

**Design default: when uncertain about type or ownership discipline, follow
Rust.** The [adopted policy](design-philosophy.md#follow-rust-for-type-and-ownership-discipline)
applies to future design and unresolved choices. An intentional difference
must name the quantum-semantic or evidence obligation and the corresponding
checking rule. The current rules below remain explicit, including linear
quantum ownership and the smaller implemented syntax.

## Formation and equality

The implemented source types are exactly these finite trees, where a tuple
has `2 <= k <= 64` immediate fields:

```text
Basis     A ::= Unit | Bit | (A1,...,Ak)
Ordinary  T ::= Unit | CBit | Q<A> | (T1,...,Tk)
Classical C ::= Unit | CBit | (C1,...,Ck)
```

| Form | Meaning and permitted context |
| --- | --- |
| `Unit` | One basis label, or the ordinary value `()`. No physical bit. |
| `Bit` | A basis label, `0` or `1`; permitted in basis declarations and inside `Q`. It is not an ordinary runtime parameter/result type. |
| `CBit` | A copyable runtime measurement/Boolean value, `false` or `true`. It is not a basis type. |
| `Q<A>` | Linear ownership of one register whose ordered basis has type A. A may contain Unit factors and nested tuples. A cannot contain CBit or Q. |
| `(T1,...,Tk)` | An ordered product retaining immediate arity and every nested field. It is classical iff every field is classical. |

Type equality is structural, not equality of dimensions, underlying machine
bits, numerical encodings or isomorphic mathematical spaces:

```text
Unit = Unit; Bit = Bit; CBit = CBit
Q<A> = Q<B>                       iff A = B
(A1,...,Ak) = (B1,...,Bj)          iff k = j and Ai = Bi for every i
```

No different constructors compare equal. In particular:

```text
(Bit,Bit,Bit) != ((Bit,Bit),Bit) != (Bit,(Bit,Bit))
(Unit,Bit) != Bit
Q<(Bit,Bit)> != (Q<Bit>,Q<Bit>)
Unit != Q<Unit>
Bit != CBit
```

There are no type aliases, subtyping rules, implicit casts, inferred type
parameters or implicit product reassociation in the current language. Parameter
and result annotations are required; local values are checked with derived
types. Plain `(T)` is not a type production. Expression `(e)` groups an expression;
`() : Unit`; singleton tuples, empty tuple types and trailing commas are absent.

This arity/nesting distinction agrees with [Rust tuple types](https://doc.rust-lang.org/reference/types/tuple.html).
The grammars are not identical: Rust also accepts singleton `(T,)` tuples,
optional trailing commas and `()` as the unit type; Qleisli currently uses
`Unit` as the type name and `()` as its value, and accepts only 2–64-field
tuple constructors. Rust's parenthesized type `(T)` and numeric tuple access
such as `value.0` are also outside the current Qleisli grammar. This comparison
does not adopt Rust's full type system or ownership rules.

## Ownership, effects and exact interfaces

A classical value may be copied or unused. An ordinary value containing any
`Q` moves as a whole; a pattern may expose classical and quantum fields, but
cannot silently discard a quantum field. Every `Q<A>` is one owner, even when
`bits(A)=0`. For example `Q<(Unit,Unit,Unit)>` has one zero-wire owner, whereas
`(Q<Unit>,Q<Unit>,Q<Unit>)` has three. Neither can be copied or dropped implicitly.
This counts operation rights, not tensor-factor independence: different owners
may be entangled with each other and with an unmentioned reference.

`Unitary`, `Iso` and `Observe` are **function effects**, ordered
`Unitary <= Iso <= Observe`; they are not value-type constructors. `Q<A>` is an
ownership type, not an effect. An observation consumes or replaces ownership
according to its primitive contract; `measure_z : Q<Bit> -> CBit` does not return
the old owner. A function with a Unit-only signature can still have an observing
declared effect. Typing alone promises no eigenstate, zero ancilla, separability,
algorithmic success or hardware accuracy.

Tuple expressions evaluate fields once, left to right. Their effects join and
their owners remain live while later fields are evaluated, including through
classical branches. A tuple pattern must match exact immediate arity and nested
structure. Branch results must have identical full types, and phi transport
must cover every result and surviving frame owner, including zero-width owners.

Basis values are labels, not quantum states, and may be copied/ignored while
defining a total finite basis function. `do p <- q; pure e` consumes `Q<A>` and
returns `Q<B>` only after independently checking the induced table is injective
on all input labels. Explicit equal-width reshaping is a unitary basis mapping;
it is not a type equality. Its phase is fixed to +1 per mapped basis state.

Function signatures retain an ordered parameter list **separate from** each
parameter's type. `f(a,b,c)` has three arguments; `f((a,b,c))` has one tuple
argument. Destructuring a basis parameter does not change its argument count.
Ordinary function parameters remain names. The legacy internal aggregation of
multiple basis parameters into a binary domain for predicate tables remains an
encoding convention, not a conversion of a single n-ary parameter into several
arguments. Binary `split`/`join` and other sealed signatures remain explicit;
they do not flatten arbitrary tuples.

Static `Op<A>` and `Op<A,m>` are compile-time operation-description parameters,
not ordinary values. They retain exact A and require separately declared
Apply/Adjoint/Controlled access. Evidence for the right width but a different
type tree does not satisfy a request. See the [operation contract](next-minor-spec.md).

## Basis order, representation and limits

`bits(Unit)=0`, `bits(Bit)=1`, and
`bits((A1,...,Ak)) = sum_i bits(Ai)`. Within a tuple the first field occupies
the lowest axes. The encoding is
`label = sum_i label_i * 2^(sum_{j<i} bits(Aj))`, recursively within fields.
Unit fields contribute no axes, but remain type nodes. Numerical identity
between two encodings authorizes only a checked explicit conversion, never
erasure of their type distinction or of ownership.

The AST retains immediate fields; the compiler retains exact type/value shapes.
Raw wire-level execution can use existing finite lifts, split/join and ordered
ports. Evidence-bearing finite interfaces additionally retain their full
`BasisType` trees, including the distinct n-ary constructor. Untyped raw wire
widths alone do not establish preservation of source types; translation
validation and general frontend adequacy remain open obligations.

The current source profile limits tuple arity to 64, AST/type/value nesting to
their documented 64 levels, basis width to 12 bits and internal type/value
trees to 4096 nodes. Contract checking has the stricter 6-bit/128-node/depth-32
finite profile. Source byte and aggregate work limits also apply. Well-formed
types may therefore be rejected by a particular execution/evidence capacity;
mathematical type formation and implementation capacity are distinct claims.
Counts include zero-width type nodes. Boundaries are not inferred from width alone.

## Adopted future types

The [0.2.1 common-QPE plan](v0.2.1-plan.md) selects `Bits<n>` as a basis register type
and `CBits<m>` as a copyable measured-bit sequence. **Neither is implemented
source syntax yet.** A future extension must specify static argument formation,
bounds including zero width, ordering, explicit conversions and evidence binding
before enabling acceptance. The experimental Lean DAG's `Bits0`/`Bits1` tags
are not source types. They do not supply type parameters or these source APIs.

`Iso<A,B>`, `Unitary<A,B>` and generalized type/size notation in design drafts
are metanotation unless a normative implemented extension says otherwise.
Future additions must update this inventory, formation/equality rules,
ownership/effects, explicit conversions, source/IR mapping, capacity and
migration rules, plus independent acceptance/rejection and semantic tests.
Isomorphism must never silently become type equality during such an extension.
