# reflection_minus1

Translation of `ReflectionUsingPrepare` from the [frozen source](https://github.com/quantumlib/Qualtran/blob/8db02b8b3fb39d69d2900dcc7b52d9d6a36834c3/qualtran/bloqs/reflections/reflection_using_prepare.py); `Apache-2.0`. Original notices and [permission records](../../POLICY.md) apply.

Contract: With PREPARE=H and global_phase=-1, 2|+><+|-I=X on the whole one-wire space, including coherent control and arbitrary references.

`kernel` consumes and returns every input owner; left-to-right leaves are low-weight first. `main` starts from [0] and measures each returned leaf in Z.

Scope: One-wire specialization. A clean predicate flag implements I-2|+><+| before its explicit -1 completion; no general PrepareOracle or cost-equivalence claim.

[Authoring](../../authoring/v026-small/README.md) retains first source/checks. Independent analytic full-entry X/Y interference checks every input and output coefficient, including phase; the paired `reflection_minus_missing_phase` fault must typecheck and disagree. Numerical tolerance is 1e-11; this is finite validation, not a translation proof, upstream-framework execution or model benchmark.
