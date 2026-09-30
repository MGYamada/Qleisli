# Ry quarter

Source: [circuit(params)](https://github.com/PennyLaneAI/demos/blob/3a04df83a16af3a2f0fd9398c0b5cc2c060ebedd/demonstrations_v2/tutorial_qubit_rotation/demo.py).
The [frozen original](../../upstream/pennylane_demos/demonstrations_v2__tutorial_qubit_rotation__demo.py) and source license retain attribution.
License: **Apache-2.0**; [intake policy](../../POLICY.md).

Apply RY(pi/2)=(I-iY)/sqrt(2)=[[1,-1],[1,1]]/sqrt(2) exactly, including the second-column sign.

Specializes params=(0,pi/2), making RX identity. The exact H Z implementation introduces no global scalar. No optimizer, continuous angle API, gradient or upstream framework execution.

Ordinary case-local `.qli` definitions with interface `Q<Bit> -> Q<Bit>`
and effect `Unitary`. The kernel consumes and returns every owner exactly once;
main explicitly prepares and measures. Arbitrary input/reference correlations
are permitted. Integer bits have first-leaf weight 1; output strings list leaves
from left to right. The enclosing `corpus/Qargo.toml` selects edition `2026`.
No language form, acceptance rule or standard API is added.

```sh
cargo run --bin qleisli -- run corpus/pennylane_demos/ry_quarter
python3 scripts/check_input_corpus.py target/debug/qleisli --case pennylane_demos/ry_quarter --exhaustive
```

The independent mathematical oracle compares every complex entry using X/Y
coherent interference, including absolute phase, order and target restoration.
The [first sources and actual observations](../../authoring/v023-small/session.json)
are preserved separately from the deliberate semantic mutation `ry_second_column_sign`.
These are finite numerical checks and informed authoring, not a translation
proof, general algorithm implementation or measured model benchmark.
