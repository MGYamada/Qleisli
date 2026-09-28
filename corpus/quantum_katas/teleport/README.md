# Teleport

Source: [StandardTeleport_Reference; ReconstructMessage_Reference](https://github.com/microsoft/QuantumKatas/blob/1a4740ff70ceffebde73d1434b2dedbe27643300/Teleportation/ReferenceImplementation.qs).
The [original](../../upstream/quantum_katas/Teleportation__ReferenceImplementation.qs) is preserved.
License: **MIT**; [intake policy](../../POLICY.md).

## Contract and translation scope

Consume the message and Alice half; return ((phase, parity), corrected Bob). Each branch has weight 1/4 and preserves the input density operator and any reference correlations.

Upstream corrections Z then X are retained. One branch differs from X then Z by a phase, irrelevant after the classical measurement. Reset of already consumed logical owners is omitted.

All tuple leaves follow source wire order. Where a register is an integer,
its first leaf has weight 1. The interpreter prints leaves from left to right.
All quantum inputs are consumed and all surviving owners are returned; measured
owners cannot be reused. The kernels use existing ordinary QLI definitions only.

Run from the repository root:

```sh
cargo run --bin qleisli -- run corpus/quantum_katas/teleport
python3 scripts/check_input_corpus.py target/debug/qleisli --case quantum_katas/teleport
```

The semantic runner uses independent finite mathematical oracles, including
coherence/controlled-phase probes for unitary kernels and branch-sensitive
checks for measurement protocols. See [validation scope](../../README.md).
No upstream Python/Q# framework is executed by these checks.
