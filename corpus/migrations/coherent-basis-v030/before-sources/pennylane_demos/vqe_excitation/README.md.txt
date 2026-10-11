# Vqe Excitation

Source: [circuit / DoubleExcitation](https://github.com/PennyLaneAI/demos/blob/3a04df83a16af3a2f0fd9398c0b5cc2c060ebedd/demonstrations_v2/tutorial_vqe/demo.py).
The [original](../../upstream/pennylane_demos/demonstrations_v2__tutorial_vqe__demo.py) is preserved.
License: **Apache-2.0**; [intake policy](../../POLICY.md).

## Contract and translation scope

DoubleExcitation(pi): |0011> -> |1100>, |1100> -> -|0011>, all other basis vectors unchanged. The default input is Hartree-Fock |1100>.

Finite signed-permutation specialization of the four-orbital ansatz. Host tests Z expectations and excitation signs; molecular Hamiltonian construction, continuous angles, chemistry data and VQE minimization are not imported.

All tuple leaves follow source wire order. Where a register is an integer,
its first leaf has weight 1. The interpreter prints leaves from left to right.
All quantum inputs are consumed and all surviving owners are returned; measured
owners cannot be reused. The kernels use existing ordinary QLI definitions only.

Run from the repository root:

```sh
cargo run --bin qleisli -- run corpus/pennylane_demos/vqe_excitation
python3 scripts/check_input_corpus.py target/debug/qleisli --case pennylane_demos/vqe_excitation
```

The semantic runner uses independent finite mathematical oracles, including
coherence/controlled-phase probes for unitary kernels and branch-sensitive
checks for measurement protocols. See [validation scope](../../README.md).
No upstream Python/Q# framework is executed by these checks.
