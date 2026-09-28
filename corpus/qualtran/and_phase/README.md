# And Phase

Source: [And](https://github.com/quantumlib/Qualtran/blob/8db02b8b3fb39d69d2900dcc7b52d9d6a36834c3/qualtran/bloqs/mcmt/and_bloq.py).
The [original](../../upstream/qualtran/qualtran__bloqs__mcmt__and_bloq.py) is preserved.
License: **Apache-2.0**; [intake policy](../../POLICY.md).

## Contract and translation scope

Compute a positive-control AND into a clean auxiliary, phase it by Z and uncompute: diag(1,1,1,-1) on the two inputs.

A compute/use/uncompute adaptation of And, not its standalone signature. QLI checks exact zero return; it does not use the upstream measurement-based uncompute or inherit its T-count.

All tuple leaves follow source wire order. Where a register is an integer,
its first leaf has weight 1. The interpreter prints leaves from left to right.
All quantum inputs are consumed and all surviving owners are returned; measured
owners cannot be reused. The kernels use existing ordinary QLI definitions only.

Run from the repository root:

```sh
cargo run --bin qleisli -- run corpus/qualtran/and_phase
python3 scripts/check_input_corpus.py target/debug/qleisli --case qualtran/and_phase
```

The semantic runner uses independent finite mathematical oracles, including
coherence/controlled-phase probes for unitary kernels and branch-sensitive
checks for measurement protocols. See [validation scope](../../README.md).
No upstream Python/Q# framework is executed by these checks.
