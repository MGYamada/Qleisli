# add_minus_one2

Source: [AddK](https://github.com/quantumlib/Qualtran/blob/8db02b8b3fb39d69d2900dcc7b52d9d6a36834c3/qualtran/bloqs/arithmetic/addition.py).
License: **Apache-2.0**; [intake policy](../../POLICY.md).
The pinned original, license and required notices remain under `corpus/upstream/qualtran/`.

## Contract and scope

For x=a+2*b, map |x> to |(x-1) mod 4> with amplitude +1, including zero underflow.

Unsigned width two, k=-1; an explicit borrow circuit replaces upstream constant loading/addition. No general adder, auxiliary cost or scalable synthesis claim.

The owner tree has 2 ordered Bit leaves. Its first leaf has integer weight 1;
`main` starts at all zero and prints those leaves from left to right. Every
input owner is consumed once and every output owner is returned. No scratch
escapes, and no observation occurs inside the unitary kernel.

```sh
cargo run --bin qleisli -- run corpus/qualtran/add_minus_one2
python3 scripts/check_input_corpus.py target/debug/qleisli --case qualtran/add_minus_one2 --exhaustive
```

The independent oracle checks all basis columns and every complex entry through
controlled X/Y interference, including phase and bit order. The paired local
semantic fault must pass source checking before the oracle detects its wrong
meaning. See the [first-source session](../../authoring/v024-small/README.md).
Finite numerical checks do not prove translation correctness or execute the
upstream framework.
