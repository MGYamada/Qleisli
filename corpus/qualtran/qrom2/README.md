# Qrom2

Source: [QROM](https://github.com/quantumlib/Qualtran/blob/8db02b8b3fb39d69d2900dcc7b52d9d6a36834c3/qualtran/bloqs/data_loading/qrom.py).
The [original](../../upstream/qualtran/qualtran__bloqs__data_loading__qrom.py) is preserved.
License: **Apache-2.0**; [intake policy](../../POLICY.md).

## Contract and translation scope

For address a=a0+2*a1, XOR data[a] into the two-bit target, with data=[1,2,3,0]; retain address and arbitrary target.

This selected affine data table has a short CNOT/X circuit. It does not implement general unary-iteration QROM, multidimensional loading or symbolic resource estimates.

All tuple leaves follow source wire order. Where a register is an integer,
its first leaf has weight 1. The interpreter prints leaves from left to right.
All quantum inputs are consumed and all surviving owners are returned; measured
owners cannot be reused. The kernels use existing ordinary QLI definitions only.

Run from the repository root:

```sh
cargo run --bin qleisli -- run corpus/qualtran/qrom2
python3 scripts/check_input_corpus.py target/debug/qleisli --case qualtran/qrom2
```

The semantic runner uses independent finite mathematical oracles, including
coherence/controlled-phase probes for unitary kernels and branch-sensitive
checks for measurement protocols. See [validation scope](../../README.md).
No upstream Python/Q# framework is executed by these checks.
