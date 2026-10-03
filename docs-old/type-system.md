# Type system: current finite source contract

Normative v0.2.x; Rust discipline, grammar/language. General compiler soundness open.

## Formation and equality

Basis A=Unit|Bit|(A1,...,Ak); ordinary T=Unit|CBit|Q<A>|(T1,...,Tk); classical omits Q,2<=k<=64. Unit has one label/zero bits/value(); Bit basis0/1 differs from copyable CBit false/true. Exact constructors/immediate arity/nesting/fields: flat/nested, Unit factors, Q<pair>/pair of Q, Unit/Q<Unit>,Bit/CBit differ. No aliases/subtyping/casts/implicit reassociation/singletons/trailing commas/grouped types/field indexing. Explicit signatures/local inference; unspecified Rust features not adopted.

## Ownership, effects and exact interfaces

Classical may copy/ignore; Q-containing mixed value moves whole, exact patterns cannot discard owners. Every Q owns once even width0 (one Q<Unit tuple> differs from several Unit owners). Owners imply no separability/eigenstate/cleanup/success. Unitary<=Iso<=Observe are effects; declared effects retained. Evaluate fields once left-right, complete branch/result/pending/caller frames with empty slots. do/pure checks total full-domain injection and explicit reshape phase+1; changes representation, not type identity. Function argument count differs from tuple arity. Static Op compile-time exact interface/access, no owner capture.

## Basis order, representation and limits

bits(Unit)=0,Bit=1,products sum; label=sum_i label_i*2^(sum_(j<i)bits(Aj)); first low, Unit node retained. Source/AST/evidence full trees, raw widths no source proof. Arity64/depth64/width12/type-value4096 nodes plus stricter evidence six bits/tree128/depth32 and bytes/work/execution. Pair binary/Tuple>=3, invalid small tuples reject, no normalization. All-classical tuples copy/mixed move; () Unit/(e) expression grouping, no singleton; values/types/patterns/interfaces retain exact shape/spans. Toffoli retains nested return ([#15](https://github.com/MGYamada/Qleisli/issues/15)).

## Explicit conversion and migration

0.2.0 replaced implicit left-fold products, frozen history retains old meanings. Explicit source conversion, no implicit packing:

```text
basis fn flatten3(((a,b),c): ((Bit,Bit),Bit)) -> (Bit,Bit,Bit) { (a,b,c) }
unitary fn to_flat(q: Q<((Bit,Bit),Bit)>) -> Q<(Bit,Bit,Bit)> {
    do x <- q; pure flatten3(x)
}
```

Inverse nests same labels via injective lift, full state/reference phase+1. Field permutation needs its own table. [Fixtures](../tests/fixtures/tuple_shapes/README.md); no general lowering proof.

## Planned v0.3.0 specification

Specify concrete type-system migrations at0.3; QLT>=0.4. PATCH retains present contract.

## Adopted future types

Bits<n>/CBits<m> only experimental sized profile; linear sizes allow constant multiplication/guarded subtraction. Bit/Bits1,Unit/Bits0,flat/nested distinct; segmentation/reversal/owner conversion explicit. Arrays/generalized Iso/Unitary draft APIs need complete formation/equality/owners/effects/encoding/lowering/capacity/migration and independent checks.
