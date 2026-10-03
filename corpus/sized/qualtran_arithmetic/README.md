# Shared reversible AddK and Equals

These ordinary `.qli` definitions use the experimental
[sized source producer](https://github.com/MGYamada/Qleisli/blob/v0.2.7/docs/sized-corpus-source.md), with the existing
independent hierarchy checker and exact finite reconstruction. They are not yet
production CLI or bundled standard-library APIs. Each body is reused at widths
0–3; zero width is a local ownership boundary test, not an upstream domain claim.
No maximum-size circuit is generated or checked by this validation.

## From coherent control to arithmetic

All contracts below have unitary effect and scalar +1 on each stated basis
mapping. Axis k carries weight 2^k. All input owners are consumed and returned
once, including empty registers. Separate owners may be entangled.

| Definition | Complete contract | Reading purpose |
| --- | --- | --- |
| [all_ones](controls.qli) | `\|c,t>` maps to `\|c,t xor [c=2^n-1]>`. | Recursively control one X by every register bit. The empty conjunction is true. |
| [increment](increment.qli) | `\|x>` maps to `\|(x+1) mod 2^n>`. | Flip the high bit on a carry from the original lower bits, then increment the lower register. |
| [add_k](addition.qli) | `\|x>` maps to `\|(x+K) mod 2^n>`. | Reuse the same increment K times; include zero, wraparound and constants larger than the modulus. |
| [invert_bits](negation.qli) | `\|x>` maps to `\|x xor (2^n-1)>`. | Share a register complement as an ordinary operation. |
| [equals](comparison.qli) | `\|x,y,t>` maps to `\|x,y,t xor [x=y]>`. | Compute a predicate into the target and restore both inputs, for either initial target value. |

For increment, the high bit changes precisely when all original low bits are
one. Updating the low register first loses that carry information; the test
suite retains this type-correct counterexample. Recursive control expresses
the conjunction directly, without a predicate truth table or scratch register.

For equality, first use the existing [shared XOR](../qualtran_xor/bitwise.qli)
to form `y xor x`. Complementing makes all bits one exactly when x=y. Apply
`all_ones` to the target, undo the complement, then undo XOR. Both input
registers are restored coherently, so the action also preserves correlations
with an arbitrary reference according to the stated permutation. Neither
measurement nor a claim that the inputs are classical is needed.

The implementation uses explicit owner tuples for recursive calls and controls.
It does not identify a tuple of owners with one quantum tuple owner, or `Bit`
with `Bits<1>`. The local empty case retains both `Bits<0>` owners and flips
the equality target. The zero-width increment is identity on its empty owner.

## Validation and cost

```sh
python3 scripts/compile_sized_corpus.py corpus/sized/qualtran_arithmetic/addition.qli \
  --entry add_k --size n=3 --size K=3 \
  --module bitwise=corpus/sized/qualtran_xor/bitwise.qli --output /tmp/add3.json
python3 scripts/test_sized_arithmetic.py
```

The CLI loads sibling modules, so supply the shared bitwise module even for
an addition entry. The first command only proposes untrusted IR. The second
freshly checks the actual graph and finite equations, then compares its action
with independently written permutations, without global-phase alignment.

The [record](../arithmetic-validation.json) covers 48 positive artifacts:
557 complete basis columns and 96 coherent reference columns, with zero
observed numerical discrepancy. It includes source-level inverse and controlled
addition, inverse equality on an explicit multi-owner group, and two shared
equality calls. Seven valid but wrong algorithms pass circuit inspection and
fail the algorithm oracle: wrong carry order, missing carry, reversed bit order,
wrong repetition count, missing restoration, wrong predicate and extra target
phase. A falsified finite X equation rejects independently. Twenty malformed
source cases reject, including aliases, owner loss, wrong grouping, hidden
operation names, invalid empty bodies, recursion and aggregate limits.

| Case | Structural work | Exact work | Unique finite leaves | Executed X applications |
| --- | --- | --- | --- | --- |
| AddK, n=3, K=3 | 762,549 | 67 | 1 | 9 |
| Equals, n=3 | 1,604,715 | 469 | 7 | 13 |
| Equals twice, n=2 | 1,300,424 | 335 | 5 | 18 |

The two-million structural ceiling is unchanged. Sharing compares complete
graph/evidence content, including leaf bytes, and does not remove repeated
execution. AddK executes nK controlled or uncontrolled X applications; this
simple reference implementation is not efficient binary-constant synthesis.
Equals executes 4n+1 X applications, some controlled, and needs no scratch.
These counts do not include the physical cost of decomposing multi-controls.

The initial width-three equality proposal exceeded the budget. Extracting the
repeated complement and sharing identical imported graph/evidence entries
admits that same small case. The
[authoring record](../../../tests/fixtures/authoring_sessions/sized-arithmetic-v021/session.json)
retains both source snapshots and actual diagnostics. This is informed
development, not a controlled model benchmark. The tests issue no independently
named arithmetic theorem, general source-preservation proof or production
acceptance claim; those integration/adoption gates remain open.

## Provenance

Apache-2.0 translations and local decomposition helpers for the already retained
Qualtran `AddK` and `Equals`, commit
`8db02b8b3fb39d69d2900dcc7b52d9d6a36834c3`. Preserve Copyright 2023 Google LLC,
the [license](../../upstream/qualtran/LICENSE), and Qleisli modification notices.
The original [addition source](../../upstream/qualtran/qualtran__bloqs__arithmetic__addition.py),
[comparison source](../../upstream/qualtran/qualtran__bloqs__arithmetic__comparison.py),
and finite [AddK](../../qualtran/add_constant3/README.md)/[Equals](../../qualtran/equals2/README.md)
regressions are unchanged. No upstream material was downloaded.
