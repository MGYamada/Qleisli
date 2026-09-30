# QLT design sources and semantic counterexamples

These are **informed design drafts**, saved during 0.2.0 development on
2026-09-29 JST. QLT is not implemented. The
[adopted design](https://github.com/MGYamada/Qleisli/issues/50) now defers its Rust experiment to
v0.4.0 or later, after the 0.3.0 type-system work, followed by a separate Lean
migration. This is not a controlled model benchmark, a new external corpus source or evidence that `.qlt` executes today.

## Preserved sources

The [first-source record](first-source-record.json) hashes all six original
files before the first QLI check. It separates future QLT expectations and
mathematically derived witnesses from actual command observations.

| Source | Purpose | Intended QLT result, not executed |
| --- | --- | --- |
| [Exact comparisons](first-source/tests/exact.qlt) | QFT2/3 versus formula-derived DFT; modular increment versus `[1,2,3,0]`. Arithmetic is the second use, independent of QFT. | Three passes. |
| [Parameterization](first-source/tests/reference.qlt) | Three finite DFT reference-library sanity cases with an explicit bounded attribute. This is not a test of generalized source QFT. | Three passes. |
| [Costs](first-source/tests/cost.qlt) | Logical gate counts for increment2 (X and CNOT) and add2 (Toffoli and two CNOTs). Field names are provisional; no physical decomposition/T-count is claimed. | Two passes under the proposed profile. |
| [QLI subjects and doctest](first-source/subjects.qli) | Current-language unitary counterexamples and a future identity doctest in a documentation comment. | One extracted doctest pass. |
| [Wrong meanings](counterexamples/meaning.qlt) | Inverse Fourier sign, omitted reversal, scalar phase and controlled relative phase. | Four assertion failures. |
| [Unsupported domain](counterexamples/domain.qlt) | DFT16 fits the 64-dimensional matrix cap but needs roots outside R8. Even comparing it with itself must not silently approximate. | Domain error before comparison. |

The deliberate failures are outside `first-source/tests/`. A future acceptance
harness must run them against `first-source` and check their expected failures,
not install them in the ordinary passing suite. No such harness exists yet.

## Mathematical counterexamples

For the positive normalized `F4`, entry `(row=1,column=1)` is `i/2`.
The inverse has `-i/2` there. Undoing the final two-bit reversal instead gives
`F4[2,1] = -1/2`. Both circuits remain well-typed unitaries.

The source sequence X;Z;X;Z is `-I`, so entry `(0,0)` is `-1`, not `1`.
Its controlled version on the first, least-significant bit has diagonal
`[1,-1,1,-1]`; entry `(1,1)` witnesses the error. This phase can be invisible
to isolated computational-basis probabilities while remaining essential under
control. These are mathematical expected values, not outputs of a QLT runner.

Later instrument tests should retain the existing
[QPE dephasing counterexample](../lean_qpe_instrument/README.md): an unchanged
phase marginal does not establish the target/reference instrument. Preserve
the [typed graph mutations](../lean_qft_graph/README.md) when adding name/cache
binding tests. Real invalid retained evidence must fail normal verification;
QLT must not weaken that boundary merely to evaluate a negative test.

## Actual observations and author burden

The [QLI check](observations/current-qli-check.json) records successful current
source/IR checking of the subjects, with **zero QLI source repairs**. The QLI
loader ignores `.qlt` files, so that success says nothing about their syntax or
assertions. The [command-boundary observation](observations/qlt-unimplemented.json)
records that `qleisli test` is still unsupported. No QLT repairs, performance
improvement, certificate or evaluator proof is claimed.

Existing [Rust operator tests](../../static_semantics.rs) and
[independent QFT experiments](../../../scripts/test_lean_qft.py) currently
require host harnesses, manual finite source selection and mathematical
reference code. The desired QLT removes repeated harness/diagnostic plumbing
while retaining independent reference construction. Duplicated definitions,
manual conversions and generation/evaluation costs have not been measured
before/after an implementation, because none exists yet. Append real QLT
attempts and diagnostics later rather than changing these first sources.
