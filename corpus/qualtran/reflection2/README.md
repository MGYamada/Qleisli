# Reflection2

Source: [ReflectionUsingPrepare](https://github.com/quantumlib/Qualtran/blob/8db02b8b3fb39d69d2900dcc7b52d9d6a36834c3/qualtran/bloqs/reflections/reflection_using_prepare.py).
The [original](../../upstream/qualtran/qualtran__bloqs__reflections__reflection_using_prepare.py) is preserved.
License: **Apache-2.0**; [intake policy](../../POLICY.md).

## Contract and translation scope

I-2|++><++|, with prepare=H^2 and upstream global_phase=+1.

This is the negative of std::routines::reflect_uniform2. Controlled interference tests retain that distinction; no arbitrary prepare oracle is accepted here.

All tuple leaves follow source wire order. Where a register is an integer,
its first leaf has weight 1. The interpreter prints leaves from left to right.
All quantum inputs are consumed and all surviving owners are returned; measured
owners cannot be reused. The kernels use existing ordinary QLI definitions only.

Run from the repository root:

```sh
cargo run --bin qleisli -- run corpus/qualtran/reflection2
python3 scripts/check_input_corpus.py target/debug/qleisli --case qualtran/reflection2
```

The semantic runner uses independent finite mathematical oracles, including
coherence/controlled-phase probes for unitary kernels and branch-sensitive
checks for measurement protocols. See [validation scope](../../README.md).
No upstream Python/Q# framework is executed by these checks.
