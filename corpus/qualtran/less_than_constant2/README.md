# Less than constant2

Source: [LessThanConstant](https://github.com/quantumlib/Qualtran/blob/8db02b8b3fb39d69d2900dcc7b52d9d6a36834c3/qualtran/bloqs/arithmetic/comparison.py).
The [frozen original](../../upstream/qualtran/qualtran__bloqs__arithmetic__comparison.py) and source license retain attribution.
License: **Apache-2.0**; [intake policy](../../POLICY.md).

For x=x0+2*x1, map |x,t> to |x,t xor [x<3]> with scalar +1, retaining arbitrary target values and input correlations.

Specializes unsigned width to 2 and threshold to 3. Uses X(target) followed by Toffoli, since [x<3]=not(x0 and x1); no general comparator synthesis or upstream resource bound is transferred.

Ordinary case-local `.qli` definitions with interface `Q<((Bit, Bit), Bit)> -> Q<((Bit, Bit), Bit)>`
and effect `Unitary`. The kernel consumes and returns every owner exactly once;
main explicitly prepares and measures. Arbitrary input/reference correlations
are permitted. Integer bits have first-leaf weight 1; output strings list leaves
from left to right. The enclosing `corpus/Qargo.toml` selects edition `2026`.
No language form, acceptance rule or standard API is added.

```sh
cargo run --bin qleisli -- run corpus/qualtran/less_than_constant2
python3 scripts/check_input_corpus.py target/debug/qleisli --case qualtran/less_than_constant2 --exhaustive
```

The independent mathematical oracle compares every complex entry using X/Y
coherent interference, including absolute phase, order and target restoration.
The [first sources and actual observations](../../authoring/v023-small/session.json)
are preserved separately from the deliberate semantic mutation `threshold_wrong_polarity`.
These are finite numerical checks and informed authoring, not a translation
proof, general algorithm implementation or measured model benchmark.
