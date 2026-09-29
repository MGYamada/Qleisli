# Bell Measure

Source: [BellState_Reference](https://github.com/microsoft/QuantumKatas/blob/1a4740ff70ceffebde73d1434b2dedbe27643300/Measurements/ReferenceImplementation.qs).
The [frozen original](../../upstream/quantum_katas/Measurements__ReferenceImplementation.qs) retains its source notices.
License: **MIT**; [intake policy](../../POLICY.md).

## Contract and translation scope

Consume both inputs and return (phase, parity), encoding the upstream integer phase + 2*parity. Branch (s,t) has effect <B_st|, where |B_st> = (|0,t> + (-1)^s |1,1 xor t>)/sqrt(2), including arbitrary reference systems.

Translates the destructive Bell measurement to two CBit outputs instead of an Int. No quantum output is retained. Tests cover all four Bell labels and the complete branch/reference Choi state by nine Pauli pairs; no hardware Bell analyzer or general protocol proof.

Classification: ordinary `.qli` definitions, with public signature `Q<(Bit, Bit)> -> (CBit, CBit)`, `Observe`.
All inputs are consumed, and every unmeasured owner is returned exactly once.
Integer bits use first-leaf weight 1; output strings list leaves left to right.
No implicit tuple conversion is used. These are case-local APIs, not new
standard-library APIs or language forms. Existing gates, split/join, static
transforms and measurement lower through the unchanged independent IR verifier.
Wrong types, duplicate owners and pure uses of observation are rejected by the
existing checker. Type-correct wrong algorithms need the independent semantic tests.

```sh
cargo run --bin qleisli -- run corpus/quantum_katas/bell_measure
python3 scripts/check_input_corpus.py target/debug/qleisli --case quantum_katas/bell_measure --exhaustive
```

Full complex-entry tests retain absolute phase for the unitary cases; Bell
measurement has branch/reference tomography. See the [validation scope](../../README.md)
and [first-source record](../../authoring/v021-expansion/session.json).
No upstream framework is executed and finite numerical agreement is not a proof.
