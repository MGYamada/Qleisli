# Interference foundation: retained development record

This is informed code-driven development on 2026-09-29, not a controlled model
benchmark. The [packet contract](../../../docs/lean-interference-slice.md) was
written before the new runtime definitions. No external input source was added.

## Before

[First source](first_source/main.qli) was saved before checking. It is already
valid finite QLI and returns two equiprobable outcomes: H;T;H;H;T;H = H;S;H.
[baseline.json](baseline.json) retains its hash and actual first run. The missing
obligation was a proved amplitude semantics for the executable Lean kernel,
not a parser error. The source has not been revised.

[reference_client](reference_client/main.qli) uses the same operation on half
of a Bell pair. Its [first run](reference-baseline.json) gives four equiprobable
joint outcomes. [wrong_order](wrong_order/main.qli) moves the final T past H;
it is type-correct but gives probabilities (2±sqrt(2))/4 instead. Its
[baseline](wrong-order-baseline.json) is retained and CI checks the semantic
difference. The native oracle also detects wrong global phase and wrong axes,
which closed measurement probabilities alone cannot establish.

## Implementation and actual repairs

[Interference-first.lean.txt](Interference-first.lean.txt) and
[first-diagnostics.txt](first-diagnostics.txt) retain the first proof attempt:
an unresolved nested conditional and an incorrect Boolean lemma name. The
repair splits the index equality explicitly and uses ordinary reductions.
[Complex-first.lean.txt](Complex-first.lean.txt) and
[first-complex-diagnostics.txt](first-complex-diagnostics.txt) retain the first
complex bridge attempt: real ordered-arithmetic automation was inappropriate
for complex coefficients, and a natural-number cast obstructed rewriting.
The repair uses a field identity and an explicit cast normalization. Subsequent
local probability lemmas passed on their first check. These are observed proof
repairs, not a measured authoring-performance comparison.

The actual runtime normalizer cancels only adjacent H on the same axis and
normalizes individual diagonal polynomials. Its theorem quantifies over joint
amplitudes with arbitrary reference coordinates. The mathematical package
imports the definitions and instantiates h=1/sqrt(2), z=exp(2πi/256), with
proved premises and local probability identities. No external acceptance rule
or production source lowering uses the transformation yet.

## After and reproducibility

Run from the repository root, after building both Lean packages and the Rust CLI:

```sh
python3 scripts/test_lean_interference.py
python3 scripts/test_lean_interference.py --source-only target/debug/qleisli
```

[native.json](native.json) records a temporary C-compiled Lean harness importing
the actual normalizer: 422 words, 1,260 joint-amplitude comparisons, all 256
phase ticks, four deliberately wrong transformations, and two large symbolic
cases. [source-after.json](source-after.json) records six positive and two
semantic-counterexample outcomes. [proof-checks.json](proof-checks.json) records
the separate proof build and axiom audit. [regressions.json](regressions.json)
retains the previous hierarchy/layout/phase native suites and helper tests.
[kernel-checks.json](kernel-checks.json) records the runtime checks observed
during this packet. Full release validation remains separate.

The positive source repair count is zero, duplicated source bodies and manual
wiring are unchanged, and no source ergonomics improvement is claimed yet.
The removed future obligation is re-proving local H cancellation for every
client: the transformation theorem is reusable. Checking still must validate
the original types, ownership, axes and capacities before any simplification.
No matrices are constructed by normalization; only the independent small test
oracle uses vectors of dimension at most eight.
