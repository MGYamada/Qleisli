# QFT hierarchy authoring and type-context reuse

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

This informed implementation experiment follows the
[QFT binding packet](../qft-binding-packet.md), the preserved shared-QPE desired
source and the existing Qualtran QFT translation. It is not a controlled model
benchmark or a proof that the source frontend supports `Bits<n>`.

The Python producer and Rust harness snapshots were saved before their first
check. [The first native observation](native.json) accepts width one but rejects
widths 2–4 as invalid IR. The producer attempted a within-register axis reversal
using a type-preserving rewire. `PortsMatch` correctly rejects that implicit
change to within-register order. The repair extracts two Bit owners, explicitly
swaps their data with a checked port permutation, and reinserts both bits; the
original register and zero-width remainder owners remain explicit.

[The repaired initial observation](explicit-swap.json) accepts widths one and
two, then reaches the unchanged aggregate limit. The
[cost breakdown](cost-breakdown.json) independently runs each existing local
check at its normal ceiling and sums diagnostics. It never accepts the whole
artifact under separate budgets. At width eight, definition typing accounts
for 3,021,349 units, contract typing for 3,312,435 and local rule checks for
18,298,054. The complete graph still rejects.

The independent test interpreter reads only actual implementation bodies and
compares complex amplitudes with the Fourier formula, including reference-state
columns. The first mutation probe used just three small basis inputs and failed
to detect a width-four controlled-phase fault whose control bit stayed zero.
The repaired probe uses every retained vector, including the complex columns.
That observed assertion and repair are summarized here; no full terminal log
of that Python assertion was preserved. These numerical tests issue no evidence.

`TypedRule.lean.txt` preserves the initial type-context matcher before repairs,
but after its first failed check because the preceding snapshot command used
the wrong working directory. [The preserved recheck](typed-rule-build.json)
records the unchanged initial errors. Repairs annotate natural indices, avoid
the reserved identifier `at`, and simplify option binds before using the typing
facts. `Conditional-before.lean.txt` preserves the previous pass;
`Conditional-typed-first.lean.txt` records the first integrated pass before its
check. Its repairs supply the context to `foldlM`, retain distinct legacy/new
theorem names, and handle the dependent successful-typing match explicitly.

The final matcher proves its ordinary result implies the original predicate
under a context itself proved from actual complete-artifact typing. No typed
flag is imported, and all existing public theorem conclusions are retained.
The old standalone scan remains available. A final precharge was added before
premise traversal. The retained `before-final-precharge-*` reports distinguish
earlier validation from the final run; one runtime sequence observed a missing
object file while that rebuild was in progress, then was rerun after completion.

[Current native checks](../qft-typed-rule-native.json) accept widths 1–4 and
retain the width-eight `limit`. They reject incorrect layout, empty-owner,
finite-H and phase inputs, and confirm the independently requested named Fourier
meaning is still unsupported. [Current cost diagnostics](../qft-typed-rule-cost.json)
show the reduced local rule work. Full Fourier binding, width eight, sized
source, execution and integrated corpus acceptance remain necessary.

## Sharing actual phase gradients

[The first recursive factorization](factored-first.py) was saved before
execution. It groups a stage's phases into a controlled gradient but initially
builds separate gradients at each precision. Its [native observation](factored-first-native.json)
accepts widths 1–4 and retains the width-eight limit; the separately summed
[local costs](factored-first-cost.json) exceed the aggregate allowance. Its
empty-owner test also fails: a hard-coded owner `1` becomes a valid fresh name
with the new producer, and shared Python header objects consistently propagate
that rename. This is a mutation-harness error, not a checker bypass. The
repair duplicates the actual first output owner, independent of its spelling.

`shared-gradient-first.py.txt` and `shared-gradient-first.rs.txt` were saved
before the [first shared-gradient run](shared-gradient-first-native.json).
At fixed precision N, the producer shares G_r, whose intended action on the
low-axis-first integer x is multiplication by exp(2πix/2^N). A width-w stage
controls G_(w−1) raised to 2^(N−w). Recursive register boundaries and finite H
leaves remain explicit; width-one empty owners and final data swaps remain.
The checker uses its existing repeated-composition rule without expanding
the body. The intended gradient/Fourier equations are producer explanations
and numerical diagnostics here, not new proved or externally trusted schemas.

The [final native record](../qft-shared-gradient-native.json) accepts every
width 1–8, including width eight at 1,694,205 structural and 536 exact units.
It compares 70 amplitude vectors against the direct DFT, detects 35 coherent
semantic faults and rejects five native malformed/mismatched artifacts.
All eight named Fourier requests still reject. The [lifted regression](../qft-lifted-regression-native.json)
retains the original width-eight capacity result. No kernel source or acceptance
rule changed in this producer refinement; full Fourier binding, sized source,
execution and integrated corpus acceptance are still required.
