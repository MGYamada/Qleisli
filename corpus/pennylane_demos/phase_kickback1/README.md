# Phase Kickback1

Source: [quantum_lock; quantum_locking_mechanism](https://github.com/PennyLaneAI/demos/blob/3a04df83a16af3a2f0fd9398c0b5cc2c060ebedd/demonstrations_v2/tutorial_phase_kickback/demo.py).
The [frozen original](../../upstream/pennylane_demos/demonstrations_v2__tutorial_phase_kickback__demo.py) retains its notices.
License: **Apache-2.0**; [intake policy](../../POLICY.md).

## Contract and finite translation

For meter m (first leaf) and one-bit key k, H_m controlled(Z_k) H_m maps |m,k> to |m xor k,k> with scalar +1, retaining both owners and all coherent inputs.

Narrows the original four-bit secret 0111 to one-bit secret 1 with num_wires=2. Preserves the H/controlled-FlipSign/H mechanism. Basis preparation and readout live in main; returns both owners instead of one sampled bit. No shot-noise, interactive guessing game or claim to port the original five-wire configuration.

Classification: ordinary case-local `.qli` definitions, with public interface
`Q<(Bit, Bit)> -> Q<(Bit, Bit)>` and effect `Unitary`. The kernel consumes each input
owner once and returns every owner; main explicitly prepares and measures.
Separate owners do not assert a product state. Integer bits use first-leaf
weight 1; result strings list leaves from left to right. Tuple shape is exact.
Existing gates, split/join and coherent control lower through the unchanged
independent Rust IR verifier; no language or standard-library API is added.
Duplicate/missing owners, incompatible shapes and observation in pure code
are rejected by existing checks. A type-correct wrong circuit needs semantic
validation rather than source checking alone.

```sh
cargo run --bin qleisli -- run corpus/pennylane_demos/phase_kickback1
python3 scripts/check_input_corpus.py target/debug/qleisli --case pennylane_demos/phase_kickback1 --exhaustive
```

The independent oracle checks every complex matrix entry through X/Y coherent
interference, including absolute phase. See the
[first-source record](../../authoring/v022-simple/session.json) and
[validation scope](../../README.md). Upstream frameworks are not executed;
finite numerical checks are not a general algorithm or translation proof.
