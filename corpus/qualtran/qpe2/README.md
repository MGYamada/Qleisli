# Qpe2

Source: [TextbookQPE](https://github.com/quantumlib/Qualtran/blob/8db02b8b3fb39d69d2900dcc7b52d9d6a36834c3/qualtran/bloqs/phase_estimation/text_book_qpe.py).
The [original](../../upstream/qualtran/qualtran__bloqs__phase_estimation__text_book_qpe.py) is preserved.
License: **Apache-2.0**; [intake policy](../../POLICY.md).

## Contract and translation scope

Two-bit coherent QPE with rectangular/uniform window and U=S=T^2. On |00>|b>, report b/4 and retain the target.

Two precision bits, one target bit and exact powers; no arbitrary state preparation window, precision calculator or symbolic sizes.

All tuple leaves follow source wire order. Where a register is an integer,
its first leaf has weight 1. The interpreter prints leaves from left to right.
All quantum inputs are consumed and all surviving owners are returned; measured
owners cannot be reused. The kernels use existing ordinary QLI definitions only.

Run from the repository root:

```sh
cargo run --bin qleisli -- run corpus/qualtran/qpe2
python3 scripts/check_input_corpus.py target/debug/qleisli --case qualtran/qpe2
```

The semantic runner uses independent finite mathematical oracles, including
coherence/controlled-phase probes for unitary kernels and branch-sensitive
checks for measurement protocols. See [validation scope](../../README.md).
No upstream Python/Q# framework is executed by these checks.
