# Equals2

Source: [Equals](https://github.com/quantumlib/Qualtran/blob/8db02b8b3fb39d69d2900dcc7b52d9d6a36834c3/qualtran/bloqs/arithmetic/comparison.py).
The [frozen original](../../upstream/qualtran/qualtran__bloqs__arithmetic__comparison.py) retains its source notices.
License: **Apache-2.0**; [intake policy](../../POLICY.md).

## Contract and translation scope

For x=x0+2*x1 and y=y0+2*y1, map |x,y,t> to |x,y,t xor [x=y]> with phase +1; both target values and all input registers are preserved coherently.

Specializes Equals(QUInt(2)). XOR differences, zero-controlled Toffoli and inverse XOR preserve both registers; no truth-table synthesis or upstream asymptotic cost is claimed.

Classification: ordinary `.qli` definitions, with public signature `Q<((((Bit, Bit), Bit), Bit), Bit)> -> Q<((((Bit, Bit), Bit), Bit), Bit)>`, `Unitary`.
All inputs are consumed, and every unmeasured owner is returned exactly once.
Integer bits use first-leaf weight 1; output strings list leaves left to right.
No implicit tuple conversion is used. These are case-local APIs, not new
standard-library APIs or language forms. Existing gates, split/join, static
transforms and measurement lower through the unchanged independent IR verifier.
Wrong types, duplicate owners and pure uses of observation are rejected by the
existing checker. Type-correct wrong algorithms need the independent semantic tests.

```sh
cargo run --bin qleisli -- run corpus/qualtran/equals2
python3 scripts/check_input_corpus.py target/debug/qleisli --case qualtran/equals2 --exhaustive
```

Full complex-entry tests retain absolute phase for the unitary cases; Bell
measurement has branch/reference tomography. See the [validation scope](../../README.md)
and [first-source record](../../authoring/v021-expansion/session.json).
No upstream framework is executed and finite numerical agreement is not a proof.
