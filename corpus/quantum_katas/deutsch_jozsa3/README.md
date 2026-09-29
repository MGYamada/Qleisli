# Deutsch Jozsa3

Source: [DJ_Algorithm_Reference; Oracle_MajorityFunction_Reference](https://github.com/microsoft/QuantumKatas/blob/1a4740ff70ceffebde73d1434b2dedbe27643300/DeutschJozsaAlgorithm/ReferenceImplementation.qs).
The [frozen original](../../upstream/quantum_katas/DeutschJozsaAlgorithm__ReferenceImplementation.qs) retains its source notices.
License: **MIT**; [intake policy](../../POLICY.md).

## Contract and translation scope

U = H^3 diag((-1)^majority(x0,x1,x2)) H^3. On |000>, outcomes 100,010,001,111 each have probability 1/4, and 000 is impossible.

Specializes the balanced majority oracle on three query bits. Replaces the |- > answer register by independently checked compute/Z/uncompute phase kickback. Returns the full query register; the host identifies balanced from nonzero output. No arbitrary oracle, scalable synthesis or general Deutsch-Jozsa claim.

Classification: ordinary `.qli` definitions, with public signature `Q<((Bit, Bit), Bit)> -> Q<((Bit, Bit), Bit)>`, `Unitary`.
All inputs are consumed, and every unmeasured owner is returned exactly once.
Integer bits use first-leaf weight 1; output strings list leaves left to right.
No implicit tuple conversion is used. These are case-local APIs, not new
standard-library APIs or language forms. Existing gates, split/join, static
transforms and measurement lower through the unchanged independent IR verifier.
Wrong types, duplicate owners and pure uses of observation are rejected by the
existing checker. Type-correct wrong algorithms need the independent semantic tests.

```sh
cargo run --bin qleisli -- run corpus/quantum_katas/deutsch_jozsa3
python3 scripts/check_input_corpus.py target/debug/qleisli --case quantum_katas/deutsch_jozsa3 --exhaustive
```

Full complex-entry tests retain absolute phase for the unitary cases; Bell
measurement has branch/reference tomography. See the [validation scope](../../README.md)
and [first-source record](../../authoring/v021-expansion/session.json).
No upstream framework is executed and finite numerical agreement is not a proof.
