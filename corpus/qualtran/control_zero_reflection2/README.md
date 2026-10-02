# control_zero_reflection2

Translation of `ReflectionUsingPrepare` from the [frozen source](https://github.com/quantumlib/Qualtran/blob/8db02b8b3fb39d69d2900dcc7b52d9d6a36834c3/qualtran/bloqs/reflections/reflection_using_prepare.py); `Apache-2.0`. Original notices and [permission records](../../POLICY.md) apply.

Contract: |c,t> -> |c,t xor [c=0]> with amplitude +1. PREPARE=H, global_phase=-1 and control_val=0, retaining both owners.

`kernel` consumes and returns every input owner; left-to-right leaves are low-weight first. `main` starts from [0, 0] and measures each returned leaf in Z.

Scope: One control and one selection wire. The global phase is relative inside the control-zero block; one private clean flag is proved by restricted with_computed. No general upstream decomposition/resource equivalence.

[Authoring](../../authoring/v026-small/README.md) retains first source/checks. Independent analytic full-entry X/Y interference checks every input and output coefficient, including phase; the paired `controlled_reflection_missing_phase` fault must typecheck and disagree. Numerical tolerance is 1e-11; this is finite validation, not a translation proof, upstream-framework execution or model benchmark.
