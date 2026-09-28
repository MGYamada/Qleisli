# Bernstein Vazirani

Source: [BV_Algorithm_Reference; Oracle_ProductFunction_Reference](https://github.com/microsoft/QuantumKatas/blob/1a4740ff70ceffebde73d1434b2dedbe27643300/DeutschJozsaAlgorithm/ReferenceImplementation.qs).
The [original](../../upstream/quantum_katas/DeutschJozsaAlgorithm__ReferenceImplementation.qs) is preserved.
License: **MIT**; [intake policy](../../POLICY.md).

## Contract and translation scope

For the fixed hidden string (1,1), H^2 diag((-1)^(a xor b)) H^2 sends |00> to |11>.

The input size is two; the hidden string is fixed at (1,1). Phase kickback replaces an explicitly retained |-> answer qubit; no general oracle parameter or host decoding is claimed.

All tuple leaves follow source wire order. Where a register is an integer,
its first leaf has weight 1. The interpreter prints leaves from left to right.
All quantum inputs are consumed and all surviving owners are returned; measured
owners cannot be reused. The kernels use existing ordinary QLI definitions only.

Run from the repository root:

```sh
cargo run --bin qleisli -- run corpus/quantum_katas/bernstein_vazirani
python3 scripts/check_input_corpus.py target/debug/qleisli --case quantum_katas/bernstein_vazirani
```

The semantic runner uses independent finite mathematical oracles, including
coherence/controlled-phase probes for unitary kernels and branch-sensitive
checks for measurement protocols. See [validation scope](../../README.md).
No upstream Python/Q# framework is executed by these checks.
