# Ising zz quarter2

Source: [U_C(gamma), single-edge factor](https://github.com/PennyLaneAI/demos/blob/3a04df83a16af3a2f0fd9398c0b5cc2c060ebedd/demonstrations_v2/tutorial_qaoa_maxcut/demo.py).
The [frozen original](../../upstream/pennylane_demos/demonstrations_v2__tutorial_qaoa_maxcut__demo.py) and source license retain attribution.
License: **Apache-2.0**; [intake policy](../../POLICY.md).

Apply exp(-i*pi*Z0*Z1/4): equal bits receive exp(-i*pi/4), unequal bits exp(+i*pi/4). Retain both owners and the absolute scalar phase.

Extracts one edge from U_C at gamma=pi/2. This is the cost-layer factor CNOT/RZ/CNOT, not the full four-node graph, mixer or optimizer. The two-wire specialization preserves the upstream rotation sign.

Ordinary case-local `.qli` definitions with interface `Q<(Bit, Bit)> -> Q<(Bit, Bit)>`
and effect `Unitary`. The kernel consumes and returns every owner exactly once;
main explicitly prepares and measures. Arbitrary input/reference correlations
are permitted. Integer bits have first-leaf weight 1; output strings list leaves
from left to right. The enclosing `corpus/Qargo.toml` selects edition `2026`.
No language form, acceptance rule or standard API is added.

```sh
cargo run --bin qleisli -- run corpus/pennylane_demos/ising_zz_quarter2
python3 scripts/check_input_corpus.py target/debug/qleisli --case pennylane_demos/ising_zz_quarter2 --exhaustive
```

The independent mathematical oracle compares every complex entry using X/Y
coherent interference, including absolute phase, order and target restoration.
The [first sources and actual observations](../../authoring/v023-small/session.json)
are preserved separately from the deliberate semantic mutation `zz_erased_scalar`.
These are finite numerical checks and informed authoring, not a translation
proof, general algorithm implementation or measured model benchmark.
