# Qubit Rotation

Source: [circuit](https://github.com/PennyLaneAI/demos/blob/3a04df83a16af3a2f0fd9398c0b5cc2c060ebedd/demonstrations_v2/tutorial_qubit_rotation/demo.py).
The [original](../../upstream/pennylane_demos/demonstrations_v2__tutorial_qubit_rotation__demo.py) is preserved.
License: **Apache-2.0**; [intake policy](../../POLICY.md).

## Contract and translation scope

Apply RY(pi/2) RX(pi/2) exactly, including scalar phase. From |0>, the Z expectation is zero.

Both continuous parameters are specialized to pi/2. Host-side expectation evaluation is tested; differentiation and optimization remain outside QLI.

All tuple leaves follow source wire order. Where a register is an integer,
its first leaf has weight 1. The interpreter prints leaves from left to right.
All quantum inputs are consumed and all surviving owners are returned; measured
owners cannot be reused. The kernels use existing ordinary QLI definitions only.

Run from the repository root:

```sh
cargo run --bin qleisli -- run corpus/pennylane_demos/qubit_rotation
python3 scripts/check_input_corpus.py target/debug/qleisli --case pennylane_demos/qubit_rotation
```

The semantic runner uses independent finite mathematical oracles, including
coherence/controlled-phase probes for unitary kernels and branch-sensitive
checks for measurement protocols. See [validation scope](../../README.md).
No upstream Python/Q# framework is executed by these checks.
