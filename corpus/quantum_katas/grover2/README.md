# Grover2

Source: [GroversSearch_Reference; GroverIteration_Reference](https://github.com/microsoft/QuantumKatas/blob/1a4740ff70ceffebde73d1434b2dedbe27643300/GroversAlgorithm/ReferenceImplementation.qs).
The [original](../../upstream/quantum_katas/GroversAlgorithm__ReferenceImplementation.qs) is preserved.
License: **MIT**; [intake policy](../../POLICY.md).

## Contract and translation scope

One Grover iteration with one marked item 11: D O H^2, D=2|++><++|-I, O=diag(1,1,1,-1). |00> maps to |11> with phase +1.

Two input bits and one iteration. The upstream global-phase correction is preserved by the sign of the standard reflection.

All tuple leaves follow source wire order. Where a register is an integer,
its first leaf has weight 1. The interpreter prints leaves from left to right.
All quantum inputs are consumed and all surviving owners are returned; measured
owners cannot be reused. The kernels use existing ordinary QLI definitions only.

Run from the repository root:

```sh
cargo run --bin qleisli -- run corpus/quantum_katas/grover2
python3 scripts/check_input_corpus.py target/debug/qleisli --case quantum_katas/grover2
```

The semantic runner uses independent finite mathematical oracles, including
coherence/controlled-phase probes for unitary kernels and branch-sensitive
checks for measurement protocols. See [validation scope](../../README.md).
No upstream Python/Q# framework is executed by these checks.
