# Qpe3

Source: [U; circuit_qpe](https://github.com/PennyLaneAI/demos/blob/3a04df83a16af3a2f0fd9398c0b5cc2c060ebedd/demonstrations_v2/tutorial_qpe/demo.py).
The [original](../../upstream/pennylane_demos/demonstrations_v2__tutorial_qpe__demo.py) is preserved.
License: **Apache-2.0**; [intake policy](../../POLICY.md).

## Contract and translation scope

Three-bit QPE for PhaseShift(3*pi/4)=T^3, returning low-weight-first phase bits and the retained target.

The demo angle 2*pi/5 is not exactly representable in the current coefficient domain. This explicitly changed-angle example uses 3*pi/4, not an approximation claim for the original 1/5 phase; precision is three bits.

All tuple leaves follow source wire order. Where a register is an integer,
its first leaf has weight 1. The interpreter prints leaves from left to right.
All quantum inputs are consumed and all surviving owners are returned; measured
owners cannot be reused. The kernels use existing ordinary QLI definitions only.

Run from the repository root:

```sh
cargo run --bin qleisli -- run corpus/pennylane_demos/qpe3
python3 scripts/check_input_corpus.py target/debug/qleisli --case pennylane_demos/qpe3
```

The semantic runner uses independent finite mathematical oracles, including
coherence/controlled-phase probes for unitary kernels and branch-sensitive
checks for measurement protocols. See [validation scope](../../README.md).
No upstream Python/Q# framework is executed by these checks.
