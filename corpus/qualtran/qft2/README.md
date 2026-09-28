# Qft2

Source: [QFTTextBook](https://github.com/quantumlib/Qualtran/blob/8db02b8b3fb39d69d2900dcc7b52d9d6a36834c3/qualtran/bloqs/qft/qft_text_book.py).
The [original](../../upstream/qualtran/qualtran__bloqs__qft__qft_text_book.py) is preserved.
License: **Apache-2.0**; [intake policy](../../POLICY.md).

## Contract and translation scope

F4[y,x]=exp(2*pi*i*x*y/4)/2 with output reversal included. Integer bit order is first leaf least significant.

Two-bit specialization of the mathematical Fourier transform using the existing QLI library. The explicit integer encoding adapter differs from upstream big-endian register presentation.

All tuple leaves follow source wire order. Where a register is an integer,
its first leaf has weight 1. The interpreter prints leaves from left to right.
All quantum inputs are consumed and all surviving owners are returned; measured
owners cannot be reused. The kernels use existing ordinary QLI definitions only.

Run from the repository root:

```sh
cargo run --bin qleisli -- run corpus/qualtran/qft2
python3 scripts/check_input_corpus.py target/debug/qleisli --case qualtran/qft2
```

The semantic runner uses independent finite mathematical oracles, including
coherence/controlled-phase probes for unitary kernels and branch-sensitive
checks for measurement protocols. See [validation scope](../../README.md).
No upstream Python/Q# framework is executed by these checks.
