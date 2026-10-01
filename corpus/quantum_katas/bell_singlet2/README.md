# Bell singlet2

Source: [AllBellStates_Reference](https://github.com/microsoft/QuantumKatas/blob/1a4740ff70ceffebde73d1434b2dedbe27643300/Superposition/ReferenceImplementation.qs).
The [frozen original](../../upstream/quantum_katas/Superposition__ReferenceImplementation.qs) and source license retain attribution.
License: **MIT**; [intake policy](../../POLICY.md).

The index-3 Bell preparation X(second) Z(second) CNOT(first,second) H(first) sends |00> to (|01>-|10>)/sqrt(2) in upstream first/second-wire notation, retaining its sign on every input.

Specializes index to 3 and two wires. It returns the complete unitary extension, not a general classical-index API or a Bell measurement.

Ordinary case-local `.qli` definitions with interface `Q<(Bit, Bit)> -> Q<(Bit, Bit)>`
and effect `Unitary`. The kernel consumes and returns every owner exactly once;
main explicitly prepares and measures. Arbitrary input/reference correlations
are permitted. Integer bits have first-leaf weight 1; output strings list leaves
from left to right. The enclosing `corpus/Qargo.toml` selects edition `2026`.
No language form, acceptance rule or standard API is added.

```sh
cargo run --bin qleisli -- run corpus/quantum_katas/bell_singlet2
python3 scripts/check_input_corpus.py target/debug/qleisli --case quantum_katas/bell_singlet2 --exhaustive
```

The independent mathematical oracle compares every complex entry using X/Y
coherent interference, including absolute phase, order and target restoration.
The [first sources and actual observations](../../authoring/v023-small/session.json)
are preserved separately from the deliberate semantic mutation `singlet_phase_after_flip`.
These are finite numerical checks and informed authoring, not a translation
proof, general algorithm implementation or measured model benchmark.
