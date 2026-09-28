# A fixed client contract with interchangeable implementations

`specification.qli` defines the client's exact logical phase operation. The client
uses `apply_contract(selected, phase, q)`, which independently checks the
selected implementation against that fixed specification and retains the
checked evidence in the final IR.

`implementation.qli` contains a direct Z implementation and a computed
implementation with a private auxiliary. Change only `selected`'s body from
`computed(q)` to `direct(q)` to exchange them; the logical specification and
client stay unchanged. Replacing that implementation by identity or X is
rejected because it fails the client's contract.

Run from the repository root:

```sh
cargo run --bin qleisli -- check examples/function_contracts
cargo run --bin qleisli -- run examples/function_contracts
```

The expected classical bits are `101`, with probability one up to numerical
rounding. The first two bits check phase against an entangled reference; the
last bit checks reuse under coherent control. Tests also cover adjoints,
repetition, shared evidence, and changes to source dependencies.

This example uses the bounded finite contract profile. It does not establish
general compiler correctness or support arbitrary encoding assertions.
