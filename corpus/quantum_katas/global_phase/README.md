# Global Phase

Source: [GlobalPhaseChange_Reference](https://github.com/microsoft/QuantumKatas/blob/1a4740ff70ceffebde73d1434b2dedbe27643300/BasicGates/ReferenceImplementation.qs).
The [original](../../upstream/quantum_katas/BasicGates__ReferenceImplementation.qs) is preserved.
License: **MIT**; [intake policy](../../POLICY.md).

## Contract and translation scope

Apply -I to an arbitrary input, including when controlled. XZXZ = -I exactly.

This replaces R(I,2*pi) with exact gates. The test must distinguish the sign under coherent control.

All tuple leaves follow source wire order. Where a register is an integer,
its first leaf has weight 1. The interpreter prints leaves from left to right.
All quantum inputs are consumed and all surviving owners are returned; measured
owners cannot be reused. The kernels use existing ordinary QLI definitions only.

Run from the repository root:

```sh
cargo run --bin qleisli -- run corpus/quantum_katas/global_phase
python3 scripts/check_input_corpus.py target/debug/qleisli --case quantum_katas/global_phase
```

The semantic runner uses independent finite mathematical oracles, including
coherence/controlled-phase probes for unitary kernels and branch-sensitive
checks for measurement protocols. See [validation scope](../../README.md).
No upstream Python/Q# framework is executed by these checks.
