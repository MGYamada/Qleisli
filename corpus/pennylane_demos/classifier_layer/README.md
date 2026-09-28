# Classifier Layer

Source: [layer (four-wire version)](https://github.com/PennyLaneAI/demos/blob/3a04df83a16af3a2f0fd9398c0b5cc2c060ebedd/demonstrations_v2/tutorial_variational_classifier/demo.py).
The [original](../../upstream/pennylane_demos/demonstrations_v2__tutorial_variational_classifier__demo.py) is preserved.
License: **Apache-2.0**; [intake policy](../../POLICY.md).

## Contract and translation scope

Rot(0,pi/2,0)=RY(pi/2) on all four wires, followed by the original CNOT ring 0->1->2->3->0.

One layer, fixed weights; arbitrary computational inputs tested. Training data, bias, losses, optimizer and later two-wire amplitude encoding are excluded. Host tests the Z0 expectation.

All tuple leaves follow source wire order. Where a register is an integer,
its first leaf has weight 1. The interpreter prints leaves from left to right.
All quantum inputs are consumed and all surviving owners are returned; measured
owners cannot be reused. The kernels use existing ordinary QLI definitions only.

Run from the repository root:

```sh
cargo run --bin qleisli -- run corpus/pennylane_demos/classifier_layer
python3 scripts/check_input_corpus.py target/debug/qleisli --case pennylane_demos/classifier_layer
```

The semantic runner uses independent finite mathematical oracles, including
coherence/controlled-phase probes for unitary kernels and branch-sensitive
checks for measurement protocols. See [validation scope](../../README.md).
No upstream Python/Q# framework is executed by these checks.
