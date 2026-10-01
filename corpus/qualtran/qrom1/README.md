# qrom1

Source: [QROM](https://github.com/quantumlib/Qualtran/blob/8db02b8b3fb39d69d2900dcc7b52d9d6a36834c3/qualtran/bloqs/data_loading/qrom.py).
License: **Apache-2.0**; [intake policy](../../POLICY.md).
The pinned original, license and required notices remain under `corpus/upstream/qualtran/`.

## Contract and scope

For address a and two-bit target y=b+2*c, map |a,y> to |a,y xor data[a]> with data=[2,1] and amplitude +1.

One address bit and two target bits, no extra control or scratch. The affine table uses explicit CNOT/X gates, not general unary-iteration or multidimensional QROM.

The owner tree has 3 ordered Bit leaves. Its first leaf has integer weight 1;
`main` starts at all zero and prints those leaves from left to right. Every
input owner is consumed once and every output owner is returned. No scratch
escapes, and no observation occurs inside the unitary kernel.

```sh
cargo run --bin qleisli -- run corpus/qualtran/qrom1
python3 scripts/check_input_corpus.py target/debug/qleisli --case qualtran/qrom1 --exhaustive
```

The independent oracle checks all basis columns and every complex entry through
controlled X/Y interference, including phase and bit order. The paired local
semantic fault must pass source checking before the oracle detects its wrong
meaning. See the [first-source session](../../authoring/v024-small/README.md).
Finite numerical checks do not prove translation correctness or execute the
upstream framework.
