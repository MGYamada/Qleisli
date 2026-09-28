# Qpe3

Source: [QPE_Reference_QFT](https://github.com/microsoft/QuantumKatas/blob/1a4740ff70ceffebde73d1434b2dedbe27643300/PhaseEstimation/ReferenceImplementation.qs).
The [original](../../upstream/quantum_katas/PhaseEstimation__ReferenceImplementation.qs) is preserved.
License: **MIT**; [intake policy](../../POLICY.md).

## Contract and translation scope

Three-bit coherent QPE for U=T. On |000>|b>, the phase bits encode b/8, first bit least significant; the target survives.

Initialization/measurement live in main. Returns raw bits and target instead of a floating estimate and reset. The fixed precision and eighth-root phase are explicit.

All tuple leaves follow source wire order. Where a register is an integer,
its first leaf has weight 1. The interpreter prints leaves from left to right.
All quantum inputs are consumed and all surviving owners are returned; measured
owners cannot be reused. The kernels use existing ordinary QLI definitions only.

Run from the repository root:

```sh
cargo run --bin qleisli -- run corpus/quantum_katas/qpe3
python3 scripts/check_input_corpus.py target/debug/qleisli --case quantum_katas/qpe3
```

The semantic runner uses independent finite mathematical oracles, including
coherence/controlled-phase probes for unitary kernels and branch-sensitive
checks for measurement protocols. See [validation scope](../../README.md).
No upstream Python/Q# framework is executed by these checks.
