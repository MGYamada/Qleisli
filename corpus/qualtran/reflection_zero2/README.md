# reflection_zero2

[ReflectionUsingPrepare.reflection_around_zero](https://github.com/quantumlib/Qualtran/blob/8db02b8b3fb39d69d2900dcc7b52d9d6a36834c3/qualtran/bloqs/reflections/reflection_using_prepare.py), frozen Apache-2.0 input; [license](../../upstream/qualtran/LICENSE).

I-2|00><00|, global_phase=+1, no outer control. Preserve every nonzero basis label and its phase; negate only zero.

Two-bit identity PREPARE specialization with direct phase circuit; no borrowed ancilla, general PREPARE oracle or arbitrary phase.

The first QLI leaf is the low bit; output measurements follow leaf order. Every input owner is returned; no implicit discard or postselection. Complete complex columns are compared by X/Y interference at tolerance 1e-11, including coherent control. The paired fault tests reflect around |11> instead of |00>. Numerical agreement is not a translation proof; upstream frameworks are not executed.

[First sources and diagnostics](../../authoring/v028-small/README.md).
