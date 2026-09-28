# Ghz3

Source: [GHZ_State_Reference](https://github.com/microsoft/QuantumKatas/blob/1a4740ff70ceffebde73d1434b2dedbe27643300/Superposition/ReferenceImplementation.qs).
The [original](../../upstream/quantum_katas/Superposition__ReferenceImplementation.qs) is preserved.
License: **MIT**; [intake policy](../../POLICY.md).

## Contract and translation scope

Apply CNOT(0,2) CNOT(0,1) H(0); |000> becomes (|000>+|111>)/sqrt(2).

The upstream loop is specialized to three wires. The full three-wire unitary extension is also tested.

All tuple leaves follow source wire order. Where a register is an integer,
its first leaf has weight 1. The interpreter prints leaves from left to right.
All quantum inputs are consumed and all surviving owners are returned; measured
owners cannot be reused. The kernels use existing ordinary QLI definitions only.

Run from the repository root:

```sh
cargo run --bin qleisli -- run corpus/quantum_katas/ghz3
python3 scripts/check_input_corpus.py target/debug/qleisli --case quantum_katas/ghz3
```

The semantic runner uses independent finite mathematical oracles, including
coherence/controlled-phase probes for unitary kernels and branch-sensitive
checks for measurement protocols. See [validation scope](../../README.md).
No upstream Python/Q# framework is executed by these checks.
