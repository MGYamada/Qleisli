# Qaoa Vertex Cover

Source: [qaoa_layer; circuit](https://github.com/PennyLaneAI/demos/blob/3a04df83a16af3a2f0fd9398c0b5cc2c060ebedd/demonstrations_v2/tutorial_qaoa_intro/demo.py).
The [original](../../upstream/pennylane_demos/demonstrations_v2__tutorial_qaoa_intro__demo.py) is preserved.
License: **Apache-2.0**; [intake policy](../../POLICY.md).

## Contract and translation scope

One layer exp(-i*alpha*sum X) exp(-i*gamma*C) H^4 with alpha=gamma=pi/4; C=3*sum_edges(Zi*Zj+Zi+Zj)-sum_i Zi on edges (0,1),(1,2),(2,0),(2,3).

Specializes the original four-node unconstrained vertex-cover graph to one layer and exact angles. No optimizer or claim of optimal vertex-cover sampling. Cost expectation is computed on the host.

All tuple leaves follow source wire order. Where a register is an integer,
its first leaf has weight 1. The interpreter prints leaves from left to right.
All quantum inputs are consumed and all surviving owners are returned; measured
owners cannot be reused. The kernels use existing ordinary QLI definitions only.

Run from the repository root:

```sh
cargo run --bin qleisli -- run corpus/pennylane_demos/qaoa_vertex_cover
python3 scripts/check_input_corpus.py target/debug/qleisli --case pennylane_demos/qaoa_vertex_cover
```

The semantic runner uses independent finite mathematical oracles, including
coherence/controlled-phase probes for unitary kernels and branch-sensitive
checks for measurement protocols. See [validation scope](../../README.md).
No upstream Python/Q# framework is executed by these checks.
