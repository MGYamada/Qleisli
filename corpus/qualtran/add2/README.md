# Add2

Source: [Add](https://github.com/quantumlib/Qualtran/blob/8db02b8b3fb39d69d2900dcc7b52d9d6a36834c3/qualtran/bloqs/arithmetic/addition.py).
The [original](../../upstream/qualtran/qualtran__bloqs__arithmetic__addition.py) is preserved.
License: **Apache-2.0**; [intake policy](../../POLICY.md).

## Contract and translation scope

For a=a0+2*a1 and b=b0+2*b1, map |a,b> to |a,(a+b) mod 4> with amplitude +1 on the whole input space.

Specializes unsigned equal two-bit registers. Uses a direct carry circuit instead of the general upstream decomposition; upstream T-count formulas are not transferred.

All tuple leaves follow source wire order. Where a register is an integer,
its first leaf has weight 1. The interpreter prints leaves from left to right.
All quantum inputs are consumed and all surviving owners are returned; measured
owners cannot be reused. The kernels use existing ordinary QLI definitions only.

Run from the repository root:

```sh
cargo run --bin qleisli -- run corpus/qualtran/add2
python3 scripts/check_input_corpus.py target/debug/qleisli --case qualtran/add2
```

The semantic runner uses independent finite mathematical oracles, including
coherence/controlled-phase probes for unitary kernels and branch-sensitive
checks for measurement protocols. See [validation scope](../../README.md).
No upstream Python/Q# framework is executed by these checks.
