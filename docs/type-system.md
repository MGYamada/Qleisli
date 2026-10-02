# Type system: current finite source contract

Normative finite source rules, unchanged in 0.2.6. [Language](language-spec.md),
[grammar](syntax-v0.md) and [tuple migration](tuple-shapes.md) refine this contract.
Follow [Rust](design-philosophy.md#follow-rust-for-type-and-ownership-discipline)
for unresolved discipline; each intentional difference needs a quantum/evidence
obligation and checking rule. General compiler soundness remains open.

## Formation and equality

```text
Basis     A ::= Unit | Bit | (A1,...,Ak)
Ordinary  T ::= Unit | CBit | Q<A> | (T1,...,Tk)
Classical C ::= Unit | CBit | (C1,...,Ck)        2 <= k <= 64
```

Unit has one label and zero bits; its ordinary value is `()`. Bit labels 0/1
occur only in basis declarations or Q; ordinary CBit values false/true are
copyable, never basis values. Q<A> owns one ordered register, with no CBit/Q
inside A. A product is classical exactly when every field is classical.

Equality compares constructors, immediate tuple arity, nesting and every field.
Q<A>=Q<B> iff A=B. Equal dimension, encoding or isomorphism is insufficient:
flat/nested triples, (Unit,Bit)/Bit, Q<(Bit,Bit)>/(Q<Bit>,Q<Bit>), Unit/Q<Unit>
and Bit/CBit differ. No aliases, subtyping, casts, inferred type parameters,
implicit reassociation, singleton tuples, trailing commas, `(T)` types or numeric
field access. Parameters/results require annotations; local types are derived.
Rust tuple discipline is the default, not adoption of its full grammar.

## Ownership, effects and exact interfaces

Classical values may be copied/unused. Any ordinary value containing Q moves
as a whole; exact patterns may expose fields but cannot discard owners. Every
Q<A> has one owner even at width zero: Q<(Unit,Unit,Unit)> has one, three Q<Unit>
fields have three. Ownership does not assert independence from other registers
or arbitrary references. Observation consumes/replaces ownership by its contract.

Unitary <= Iso <= Observe are function effects, not types. Declared effects
remain obligations even with Unit-only ports. Typing proves no eigenstate,
cleanup, success or hardware accuracy. Tuple fields evaluate once left to right;
branches retain earlier fields/pending owners. Branch result types and complete
result/surviving-frame phis must match, including zero-width owners.

Basis labels may be copied/ignored. `do p <- q; pure e` consumes Q<A> and issues
Q<B> only after a total full-domain injective table check. Equal-width explicit
reshape has coefficient +1; it changes representation, not type equality.

Parameter lists remain separate from parameter types: f(a,b,c) has three
arguments, f((a,b,c)) one. Basis patterns do not change arity; their internal
left-associated multi-parameter table domain does not unpack an ordinary tuple.
Sealed split/join are binary. [Static Op](next-minor-spec.md) parameters are
compile-time descriptions with separate Apply/Adjoint/Controlled capabilities,
exact A and no captured owners; they are not ordinary values.

## Basis order, representation and limits

bits(Unit)=0, bits(Bit)=1, product widths sum. First field occupies low axes:
label=sum_i label_i*2^(sum_(j<i) bits(Aj)), recursively. Unit remains a node.
AST/source checking and finite evidence retain exact trees; raw ordered widths
alone do not establish source preservation. Current arity 64, nesting 64,
width 12 and type/value nodes 4096 coexist with stricter [finite evidence](finite-contracts.md)
(six bits, 128 nodes, depth 32), byte/work and execution limits. Count empty nodes;
capacity rejection is distinct from mathematical type formation.

## Planned v0.3.0 specification

v0.3.0 specifies the type system and public migrations; concrete changes remain
open. QLT implementation waits until v0.4.0 or later. Compatible PATCH work
retains this contract.

## Adopted future types

Bits<n>/CBits<m> are adopted register/measured-sequence directions, implemented
only in the [experimental sized path](sized-corpus-source.md), not general source
syntax. [Linear sizes](size-expressions.md) permit constant multiplication and
guarded subtraction; equality reconciles indices of the same constructor only.
Bit/Bits<1>, Unit/Bits<0>, flat/nested trees remain distinct. Register segmentation,
bit reversal and owner conversion require explicit separately checked operations.
Arrays and generalized Iso<A,B>/Unitary<A,B> draft notation remain future APIs.
Each extension needs formation/equality, ownership/effects, encoding/lowering,
capacities, migration and independent positive/negative semantic checks.
