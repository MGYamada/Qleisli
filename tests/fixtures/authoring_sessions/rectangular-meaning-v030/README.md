# Rectangular Meaning and ordinary project integration

Informed implementation study for resumed #83, under the approved 127-Issue
0.3.0-beta plan. The context, first sources and real before/after diagnostics
are retained in [session.json](session.json).

The first ordinary project cannot lower its differing-port Op. Its reference
variant first fails parsing the Meaning arrow. After implementation both reach
the existing closed-project entry restriction: these original sources have
quantum input arguments. They remain unchanged. Attempt 02 adds explicit
`unit(())` input and `measure_z` readout to each entry, preserving the quantum
bodies and Plus request. Both actual check/run calls succeed; readout is 0/1
with probability approximately one half.

These observations do not prove phase equality. `tests/pure_leaf.rs` separately
checks independently written exact rectangular matrices, phase/axis mutants,
hidden observation/reset/discard, zero-width ownership, dependency substitution,
strict packet fields and budgets. `tests/rectangular_meanings.rs` compares
ordinary and selected Raw adapters, including tensor, composition, distinct
type trees, inverse access and a suspended entangled reference. The native Lean
proofs connect the actual reconstructed body to its exact requested matrix and
Gram identity. These are bounded artifact equations, not general source/runtime
preservation or full QS/PR/RS discharges.

The selected adapter still rejects coherent `basis` expressions in its existing
preparation projection; an exploratory cross-adapter lift regression exposed
that restriction. The common executable regression uses `init0`/`cnot`/`join`
for the same small copying isometry. General frontend consolidation remains
#250 work. First sources and diagnostics above were not rewritten for it.

No maximum-size cases were intentionally selected for this study. An earlier
unfiltered finite-leaf test command inadvertently reached the existing six-bit
identity test; it was interrupted, then rerun with that test explicitly skipped.
The completed small finite-leaf run passed 15 tests with one filtered out.
The retained maximum-size test is now explicitly ignored by default so a normal
CI invocation does not newly run it; its original body remains unchanged.
This is not a successful maximum-size check. Final validation and commit/CI
bindings remain in #83 and #142; this record does not close either Issue.

The first full PR CI run at `0fbc1285dc85661024a03005f0b5b70b9d3e9c6d`
[failed two existing function-contract tests](https://github.com/MGYamada/Qleisli/actions/runs/38188616226/job/114616660282).
Both asserted shared `Arc` identity across adjoint, control and repetition;
the nested case also retained three levels of evidence. The new named-adjoint
adapter had unnecessarily wrapped endomorphic contract evidence in a new
provider. Restricting that route to differing input/output types restores the
existing shared steps. The tests and their source programs remain unchanged.
The repaired tree passed all 24 function-contract, 19 general-arrow and six
rectangular-Meaning tests on both the default toolchain and Rust 1.85.0.
This focused result does not replace the required full CI run on the fix.
