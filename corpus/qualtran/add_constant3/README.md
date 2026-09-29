# Add Constant3

Source: [AddK](https://github.com/quantumlib/Qualtran/blob/8db02b8b3fb39d69d2900dcc7b52d9d6a36834c3/qualtran/bloqs/arithmetic/addition.py).
The [frozen original](../../upstream/qualtran/qualtran__bloqs__arithmetic__addition.py) retains its source notices.
License: **Apache-2.0**; [intake policy](../../POLICY.md).

## Contract and translation scope

For x=x0+2*x1+4*x2, map |x> to |(x+3) mod 8> with amplitude +1 on all eight basis states, including wraparound.

Specializes AddK(QUInt(3), k=3) using an explicit carry circuit (+1 then +2), without temporary registers. General signed types, symbolic sizes and upstream resource-count claims are excluded.

Classification: ordinary `.qli` definitions, with public signature `Q<((Bit, Bit), Bit)> -> Q<((Bit, Bit), Bit)>`, `Unitary`.
All inputs are consumed, and every unmeasured owner is returned exactly once.
Integer bits use first-leaf weight 1; output strings list leaves left to right.
No implicit tuple conversion is used. These are case-local APIs, not new
standard-library APIs or language forms. Existing gates, split/join, static
transforms and measurement lower through the unchanged independent IR verifier.
Wrong types, duplicate owners and pure uses of observation are rejected by the
existing checker. Type-correct wrong algorithms need the independent semantic tests.

```sh
cargo run --bin qleisli -- run corpus/qualtran/add_constant3
python3 scripts/check_input_corpus.py target/debug/qleisli --case qualtran/add_constant3 --exhaustive
```

Full complex-entry tests retain absolute phase for the unitary cases; Bell
measurement has branch/reference tomography. See the [validation scope](../../README.md)
and [first-source record](../../authoring/v021-expansion/session.json).
No upstream framework is executed and finite numerical agreement is not a proof.
