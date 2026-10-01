# ry_negative_quarter

Source: [circuit(params)](https://github.com/PennyLaneAI/demos/blob/3a04df83a16af3a2f0fd9398c0b5cc2c060ebedd/demonstrations_v2/tutorial_qubit_rotation/demo.py).
License: **Apache-2.0**; [intake policy](../../POLICY.md).
The pinned original, license and required notices remain under `corpus/upstream/pennylane_demos/`.

## Contract and scope

Apply RY(-pi/2)=(I+iY)/sqrt(2): |0> -> (|0>-|1>)/sqrt(2), |1> -> (|0>+|1>)/sqrt(2).

Fix params=(0,-pi/2) with explicit Z-after-H order. This is the gate kernel only, with no optimizer, gradients or continuous-angle API.

The owner tree has 1 ordered Bit leaves. Its first leaf has integer weight 1;
`main` starts at all zero and prints those leaves from left to right. Every
input owner is consumed once and every output owner is returned. No scratch
escapes, and no observation occurs inside the unitary kernel.

```sh
cargo run --bin qleisli -- run corpus/pennylane_demos/ry_negative_quarter
python3 scripts/check_input_corpus.py target/debug/qleisli --case pennylane_demos/ry_negative_quarter --exhaustive
```

The independent oracle checks all basis columns and every complex entry through
controlled X/Y interference, including phase and bit order. The paired local
semantic fault must pass source checking before the oracle detects its wrong
meaning. See the [first-source session](../../authoring/v024-small/README.md).
Finite numerical checks do not prove translation correctness or execute the
upstream framework.
