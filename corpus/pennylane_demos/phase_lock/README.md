# Phase Lock

Source: [quantum_lock; quantum_locking_mechanism](https://github.com/PennyLaneAI/demos/blob/3a04df83a16af3a2f0fd9398c0b5cc2c060ebedd/demonstrations_v2/tutorial_phase_kickback/demo.py).
The [original](../../upstream/pennylane_demos/demonstrations_v2__tutorial_phase_kickback__demo.py) is preserved.
License: **Apache-2.0**; [intake policy](../../POLICY.md).

## Contract and translation scope

The first wire is a lock meter. H, controlled FlipSign(0111), H XORs the predicate [key=0111] into that meter and preserves the four-wire key.

Keeps the demo five-wire size and secret 0111. Enumerates all 32 basis inputs and probes coherent keys; no shot noise or interactive guessing game.

All tuple leaves follow source wire order. Where a register is an integer,
its first leaf has weight 1. The interpreter prints leaves from left to right.
All quantum inputs are consumed and all surviving owners are returned; measured
owners cannot be reused. The kernels use existing ordinary QLI definitions only.

Run from the repository root:

```sh
cargo run --bin qleisli -- run corpus/pennylane_demos/phase_lock
python3 scripts/check_input_corpus.py target/debug/qleisli --case pennylane_demos/phase_lock
```

The semantic runner uses independent finite mathematical oracles, including
coherence/controlled-phase probes for unitary kernels and branch-sensitive
checks for measurement protocols. See [validation scope](../../README.md).
No upstream Python/Q# framework is executed by these checks.
