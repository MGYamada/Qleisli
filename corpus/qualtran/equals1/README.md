# equals1

[Equals](https://github.com/quantumlib/Qualtran/blob/8db02b8b3fb39d69d2900dcc7b52d9d6a36834c3/qualtran/bloqs/arithmetic/comparison.py), frozen Apache-2.0 input; [license](../../upstream/qualtran/LICENSE).

|a,b,t> maps to |a,b,t xor [a=b]>, scalar +1, including an initially-one target and restored comparison inputs.

QUInt(1) inputs; finite XOR/negative-control/uncompute specialization, not a symbolic comparator.

The first QLI leaf is the low bit; output measurements follow leaf order. Every input owner is returned; no implicit discard or postselection. Complete complex columns are compared by X/Y interference at tolerance 1e-11, including coherent control. The paired fault tests fail to restore the complemented comparison input. Numerical agreement is not a translation proof; upstream frameworks are not executed.

[First sources and diagnostics](../../authoring/v028-small/README.md).
