# Odd parity3

Source: [AllStatesWithParitySuperposition_Reference](https://github.com/microsoft/QuantumKatas/blob/1a4740ff70ceffebde73d1434b2dedbe27643300/Superposition/ReferenceImplementation.qs).
The [frozen original](../../upstream/quantum_katas/Superposition__ReferenceImplementation.qs) and source license retain attribution.
License: **MIT**; [intake policy](../../POLICY.md).

Apply H to the first two wires, XOR them into the third, then flip the third: |000> becomes the uniform odd-parity state. The complete unitary extension retains signed input columns.

Specializes the recursive source to three wires and parity 1. The common even/odd recursive bodies share their Hadamards; their conditional last-wire X is a CNOT. This is deterministic preparation, not the postselection alternative.

Ordinary case-local `.qli` definitions with interface `Q<((Bit, Bit), Bit)> -> Q<((Bit, Bit), Bit)>`
and effect `Unitary`. The kernel consumes and returns every owner exactly once;
main explicitly prepares and measures. Arbitrary input/reference correlations
are permitted. Integer bits have first-leaf weight 1; output strings list leaves
from left to right. The enclosing `corpus/Qargo.toml` selects edition `2026`.
No language form, acceptance rule or standard API is added.

```sh
cargo run --bin qleisli -- run corpus/quantum_katas/odd_parity3
python3 scripts/check_input_corpus.py target/debug/qleisli --case quantum_katas/odd_parity3 --exhaustive
```

The independent mathematical oracle compares every complex entry using X/Y
coherent interference, including absolute phase, order and target restoration.
The [first sources and actual observations](../../authoring/v023-small/session.json)
are preserved separately from the deliberate semantic mutation `parity_prepared_even`.
These are finite numerical checks and informed authoring, not a translation
proof, general algorithm implementation or measured model benchmark.
