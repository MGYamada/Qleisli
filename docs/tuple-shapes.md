# Arity-preserving tuples

Adopted breaking v0.2.0 migration replaces earlier left folding; frozen records retain
old meanings. Current [type contract](type-system.md) fixes structural equality.

## Types, values and patterns

Ordered immediate arity2..64, nested fields retained everywhere: types/Q, basis/ordinary
values, lets/lifts/basis parameters, function/branch/static/evidence interfaces. Flat
triple and either binary nesting differ; no reassociation/flattening/Unit erasure.
Binary meanings unchanged, arguments distinct from tuples; () Unit/(e) grouping,
no singleton/trailing commas. Fields evaluate once left-to-right, joining effects;
all-classical tuples copy, mixed tuples move. Patterns match full shape/order without
duplicated names/discarded owners, including zero width. Basis labels may be ignored
but lifted complete map still needs injectivity.

First field low, label=sum_i label_i*2^(sum_(j<i) bits(Aj)); Unit zero axes remains
node. Equal widths/encodings/matrices do not coerce trees. AST Tuple(Vec) retains
fields/spans; separate arity64/nesting64 and existing work/node/width budgets. Values
retain shape before ordered IR ports; no new gate/raw instruction.

Evidence Pair is exactly binary, Tuple at least3; noncanonical smaller Tuple rejects,
never normalizes. [QIRF](machine-interface-spec.md) encodes tuple fields, rejecting
unknown fields/arity/limits. Old binary encodings retain meaning; M2 also preserves
full arity, never reconstructs from widths.

## Explicit conversion and migration

```text
basis fn flatten3(((a,b),c): ((Bit,Bit),Bit)) -> (Bit,Bit,Bit) { (a,b,c) }
basis fn nest3((a,b,c): (Bit,Bit,Bit)) -> ((Bit,Bit),Bit) { ((a,b),c) }
unitary fn to_flat(q: Q<((Bit,Bit),Bit)>) -> Q<(Bit,Bit,Bit)> {
    do x <- q; pure flatten3(x)
}
unitary fn to_nested(q: Q<(Bit,Bit,Bit)>) -> Q<((Bit,Bit),Bit)> {
    do x <- q; pure nest3(x)
}
```

Ordinary definitions above check total identity-label injections, preserving complete
state/reference phase+1. Field permutation is another table, not identity evidence.
[Intact reshape](size-expressions.md) is an explicit single-owner metadata adapter,
not implicit equality or owner merging. Keep Toffoli's nested return until versioned
migration; flat return is tracked in [#15](https://github.com/MGYamada/Qleisli/issues/15).
Historical source/public AST migrations stay in immutable releases, current callers
must select exact trees and explicit conversion. [Tuple fixtures](../tests/fixtures/tuple_shapes/README.md)
retain positive/counterexample evidence; no general source adequacy proof is claimed.
