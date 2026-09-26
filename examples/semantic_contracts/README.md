# Exact finite semantic contracts

This example uses the three-argument `with_computed` language form to check
three implementations against independently specified logical operations:

- A computed auxiliary phase realizes logical Z.
- H followed by H on the auxiliary realizes logical identity.
- X on both data and the computed auxiliary realizes logical X when the
  predicate is the identity function.

The independent IR verifier checks the exact operator equation
`W E_f = E_f u`, including phase and auxiliary cleanup. The raw IR retains
both the actual body circuit W and the specified logical circuit u. These
checks cover every encoded input and extend to arbitrary correlated reference
systems; the closed run below is only a small observable regression example.

Run from the repository root:

```sh
cargo run --bin qleisli -- check examples/semantic_contracts
cargo run --bin qleisli -- run examples/semantic_contracts
```

The CLI prints `101: 1.000000000000e0`: the flattened classical result is
`[true, false, true]` with probability one, up to reference-simulator rounding.
Changing the simultaneous flip body to
`(data, x(auxiliary))` is rejected during compilation because the equation
fails and exact cleanup is unproved.

This bounded implementation is progress toward the
[v0.1 release milestone](../../docs/release-milestones.md), not a claim that
all release conditions or general compiler soundness have been completed.
