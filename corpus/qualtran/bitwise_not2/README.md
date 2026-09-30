# Bitwise Not2

Source: [BitwiseNot](https://github.com/quantumlib/Qualtran/blob/8db02b8b3fb39d69d2900dcc7b52d9d6a36834c3/qualtran/bloqs/arithmetic/bitwise.py).
The [frozen original](../../upstream/qualtran/qualtran__bloqs__arithmetic__bitwise.py) retains its notices.
License: **Apache-2.0**; [intake policy](../../POLICY.md).

## Contract and finite translation

For x=x0+2*x1, map |x> to |3-x> = |x xor 3> with scalar +1 on all four basis inputs.

Specializes BitwiseNot(QUInt(2)), flipping both bits and returning the same owner shape. General signed/modular types, symbolic sizes and resource estimation are excluded.

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
cargo run --bin qleisli -- run corpus/qualtran/bitwise_not2
python3 scripts/check_input_corpus.py target/debug/qleisli --case qualtran/bitwise_not2 --exhaustive
```

The independent oracle checks every complex matrix entry through X/Y coherent
interference, including absolute phase. See the
[first-source record](../../authoring/v022-simple/session.json) and
[validation scope](../../README.md). Upstream frameworks are not executed;
finite numerical checks are not a general algorithm or translation proof.
