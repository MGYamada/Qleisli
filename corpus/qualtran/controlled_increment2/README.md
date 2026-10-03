# controlled_increment2

[AddK; controlled specialization](https://github.com/quantumlib/Qualtran/blob/8db02b8b3fb39d69d2900dcc7b52d9d6a36834c3/qualtran/bloqs/arithmetic/addition.py), frozen Apache-2.0 input; [license](../../upstream/qualtran/LICENSE).

|c,x> maps to |c,(x+c) mod 4>, scalar +1; c is axis 0 and x has axes 1,2. Both control sectors and overflow are retained.

Unsigned width-two AddK(k=1) with one coherent control, as allowed by the upstream controlled construction. Direct carry circuit; no upstream auxiliary decomposition or resource-count equivalence.

The first QLI leaf is the low bit; output measurements follow leaf order. Every input owner is returned; no implicit discard or postselection. Complete complex columns are compared by X/Y interference at tolerance 1e-11, including coherent control. The paired fault tests compute the carry from the updated low bit instead of the original one. Numerical agreement is not a translation proof; upstream frameworks are not executed.

[First sources and diagnostics](../../authoring/v028-small/README.md).
