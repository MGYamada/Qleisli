# Arity-preserving tuples in 0.2.0

Status: adopted for 0.2.0 on 2026-09-29, superseding the 0.1.8
left-folding syntax rule and the earlier 0.2.0 plan's preservation of that rule.
This is a breaking source/public-AST change. Historical release and authoring
records retain their original meaning.

## Types, values and patterns

A tuple has an ordered list of **2 through 64 immediate fields**. Each field
may itself be a tuple. Equality requires equal arity and recursively equal
field types; no associativity, flattening or Unit elimination is implicit.
In particular `(Bit,Bit,Bit)`, `((Bit,Bit),Bit)` and `(Bit,(Bit,Bit))` are three
different basis types. This also applies inside `Q`, to classical/mixed values,
ordinary and basis expressions, `let`, coherent-lift and basis-parameter patterns,
function results, branch results, static operation arguments and exact contracts.
Two-field tuples retain their existing binary meaning. Function argument lists
remain separate from tuples. Unit `()` and expression grouping `(e)` retain
their meanings; singleton tuples and trailing commas remain unsupported.

Tuple expressions evaluate their immediate fields once, left to right, passing
the remaining ownership context to the next field and joining all effects.
A tuple is copyable exactly when all fields are classical. A mixed tuple moves
as a whole. Patterns require the same immediate arity and nested shape as the
value, visit fields left to right, and cannot duplicate names or discard owners.
This includes zero-width quantum ownership. Basis patterns bind labels only;
ignoring a basis label still requires whole-domain injectivity for a quantum lift.

The basis width is the sum of field widths. Its integer label is
`sum_i label_i * 2^(sum_{j<i} bits(A_j))`: the first field occupies the lowest
axes. Unit fields contribute zero axes but remain in the type. A flat tuple and
a nested tuple can have the same width and numerical encoding while having
different types. Equality of dimensions or matrices does not authorize coercion.

Tuple notation is a **language form**, not a new quantum operation. The public
AST stores `Tuple(Vec<...>)`, preserving immediate fields and spans. Flat arity
has its own 64-field bound; genuine nesting retains the 64-level AST bound.
Existing work, type/value-node and finite quantum-width bounds still apply.
Runtime values retain tuple shape before outputs are flattened into ordered IR
ports. Finite basis tables and existing wire operations suffice for execution;
no new gate or raw quantum instruction is introduced.

Exact evidence retains binary `BasisType::Pair` for two fields and a distinct
`BasisType::Tuple` for three or more. Both shape and semantics must match an
independently required contract. `Tuple` with fewer than three fields is
noncanonical and rejected, never normalized into Pair or Unit. The finite
interchange type encoding adds `{"tag":"tuple","fields":[...]}`; unknown
fields, noncanonical arity and existing depth/node limits reject. The format
is introduced in 0.2.0; old binary encodings keep
their meaning. The selected M2 interface must likewise retain ordered arity,
rather than recover it from widths or flattened ports.

## Explicit conversion and migration

These are ordinary checked definitions, not implicit casts:

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

Their tables are identity permutations on labels, checked as total injections;
the full quantum state and reference correlations are retained. An actual
permutation of fields has a different table and must not pass an identity
contract just because its result type is well formed.

To preserve the old type of a flat spelling, write its former binary tree
explicitly: `(a,b,c,d)` becomes `(((a,b),c),d)`, in matching types and patterns.
To adopt true n-ary types, update producer/consumer signatures and patterns
together and use explicit conversions at binary interfaces. Existing binary
`split`/`join`, tensor/control operation constructors and sealed `toffoli`
result shapes retain their contracts. A flat three-field pattern therefore
cannot destructure `toffoli`'s `((Q<Bit>,Q<Bit>),Q<Bit>)` result.

Reject a flat value returned as a nested declared type, a flat pattern on a
nested value, mismatched branches, mismatched static-operation/meaning shapes,
and equal-width differently shaped external evidence. The
[first source and original acceptance](../tests/fixtures/tuple_shapes/baseline.json)
preserve the semantic counterexample that motivated this correction.
General frontend adequacy is still open; existing binary Lean models do not
by themselves prove this source extension.
