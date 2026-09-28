# Measure Plus

Source: [IsQubitPlus_Reference](https://github.com/microsoft/QuantumKatas/blob/1a4740ff70ceffebde73d1434b2dedbe27643300/Measurements/ReferenceImplementation.qs).
The [original](../../upstream/quantum_katas/Measurements__ReferenceImplementation.qs) is preserved.
License: **MIT**; [intake policy](../../POLICY.md).

## Contract and translation scope

Return 1 for |+> and 0 for |->. For any input rho, P(1)=(1+Tr(X rho))/2.

Measurement consumes the input; no post-measurement qubit is returned. The X before Z measurement preserves the upstream Boolean polarity.

All tuple leaves follow source wire order. Where a register is an integer,
its first leaf has weight 1. The interpreter prints leaves from left to right.
All quantum inputs are consumed and all surviving owners are returned; measured
owners cannot be reused. The kernels use existing ordinary QLI definitions only.

Run from the repository root:

```sh
cargo run --bin qleisli -- run corpus/quantum_katas/measure_plus
python3 scripts/check_input_corpus.py target/debug/qleisli --case quantum_katas/measure_plus
```

The semantic runner uses independent finite mathematical oracles, including
coherence/controlled-phase probes for unitary kernels and branch-sensitive
checks for measurement protocols. See [validation scope](../../README.md).
No upstream Python/Q# framework is executed by these checks.
