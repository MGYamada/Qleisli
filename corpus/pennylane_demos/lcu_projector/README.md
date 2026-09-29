# Lcu Projector

Source: [lcu_circuit (Application: Projectors)](https://github.com/PennyLaneAI/demos/blob/3a04df83a16af3a2f0fd9398c0b5cc2c060ebedd/demonstrations_v2/tutorial_lcu_blockencoding/demo.py).
The [frozen original](../../upstream/pennylane_demos/demonstrations_v2__tutorial_lcu_blockencoding__demo.py) retains its source notices.
License: **Apache-2.0**; [intake policy](../../POLICY.md).

## Contract and translation scope

For selector s (first wire) and data d, U=(H_s tensor I_d) SELECT(I,Z) (H_s tensor I_d), so U|s,d>=|s xor d,d>. Its zero-selector block is (I+Z)/2=|0><0|.

Preserves the original equal coefficients and I/Z operators. Chooses H as an explicit unitary completion of PREP|0>=|+>; it does not identify all columns with an unspecified upstream StatePrep completion. The full QLI unitary is tested separately from the projected-block equation. Both owners are returned: selector zero return, deterministic projection, postselection, arbitrary coefficients and general LCU/QSVT are not provided.

Classification: ordinary `.qli` definitions, with public signature `Q<(Bit, Bit)> -> Q<(Bit, Bit)>`, `Unitary`.
All inputs are consumed, and every unmeasured owner is returned exactly once.
Integer bits use first-leaf weight 1; output strings list leaves left to right.
No implicit tuple conversion is used. These are case-local APIs, not new
standard-library APIs or language forms. Existing gates, split/join, static
transforms and measurement lower through the unchanged independent IR verifier.
Wrong types, duplicate owners and pure uses of observation are rejected by the
existing checker. Type-correct wrong algorithms need the independent semantic tests.

```sh
cargo run --bin qleisli -- run corpus/pennylane_demos/lcu_projector
python3 scripts/check_input_corpus.py target/debug/qleisli --case pennylane_demos/lcu_projector --exhaustive
```

Full complex-entry tests retain absolute phase for the unitary cases; Bell
measurement has branch/reference tomography. See the [validation scope](../../README.md)
and [first-source record](../../authoring/v021-expansion/session.json).
No upstream framework is executed and finite numerical agreement is not a proof.
