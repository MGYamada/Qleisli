# Rx Quarter

Source: [circuit(params)](https://github.com/PennyLaneAI/demos/blob/3a04df83a16af3a2f0fd9398c0b5cc2c060ebedd/demonstrations_v2/tutorial_qubit_rotation/demo.py).
The [frozen original](../../upstream/pennylane_demos/demonstrations_v2__tutorial_qubit_rotation__demo.py) retains its notices.
License: **Apache-2.0**; [intake policy](../../POLICY.md).

## Contract and finite translation

Apply RX(pi/2)=(I-iX)/sqrt(2), including the exact scalar phase. On |0>, Z measurement is uniform and <Z>=0.

Specializes params=(pi/2,0), so the original RY is identity. Z expectation is aggregated on the host from the returned distribution. Reuses the known exact rotation decomposition; no optimizer, gradients, continuous angles or upstream framework execution.

Classification: ordinary case-local `.qli` definitions, with public interface
`Q<Bit> -> Q<Bit>` and effect `Unitary`. The kernel consumes each input
owner once and returns every owner; main explicitly prepares and measures.
Separate owners do not assert a product state. Integer bits use first-leaf
weight 1; result strings list leaves from left to right. Tuple shape is exact.
Existing gates, split/join and coherent control lower through the unchanged
independent Rust IR verifier; no language or standard-library API is added.
Duplicate/missing owners, incompatible shapes and observation in pure code
are rejected by existing checks. A type-correct wrong circuit needs semantic
validation rather than source checking alone.

```sh
cargo run --bin qleisli -- run corpus/pennylane_demos/rx_quarter
python3 scripts/check_input_corpus.py target/debug/qleisli --case pennylane_demos/rx_quarter --exhaustive
```

The independent oracle checks every complex matrix entry through X/Y coherent
interference, including absolute phase. See the
[first-source record](../../authoring/v022-simple/session.json) and
[validation scope](../../README.md). Upstream frameworks are not executed;
finite numerical checks are not a general algorithm or translation proof.
