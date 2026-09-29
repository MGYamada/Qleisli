# Interference semantics for the executable kernel

Status: **implemented with executable-definition and complex proofs**, 2026-09-29. This extends
the mathematical foundation of CD-3, before enabling non-diagonal hierarchical
acceptance. Production verification remains Rust-authoritative.

The retained [first source](../tests/fixtures/lean_interference/first_source/main.qli)
places a cancelling H pair between two T gates. Its independent expectation
is equal probabilities for zero and one. Removing either outer H, moving a
phase through H, or treating coherent branches as probabilities changes its
meaning. A second client must retain a reference entangled with the input.

## Contract selected before implementation

Add Mathlib-free amplitude semantics over a commutative ring, an explicitly
specified inverse-square-root-of-two coefficient h with 2hh=1, and a phase
root z with z^256=1. These are quantified mathematical premises, never
artifact-supplied evidence or a new coefficient-provider API. Instantiate
the model with h=1/sqrt(2), z=exp(2πi/256) in the separate mathematical proof
package; the executable package must not import Mathlib. The runtime uses
Lean core's `Lean.Grind.CommRing`; no algebra package was added to it.

Assignments are functions from axis indices to bits. H at axis j replaces
that coordinate with each of zero and one and adds amplitudes with the exact
sign (-1)^(input[j]·output[j]). It leaves other coordinates and any external
reference untouched. A diagonal polynomial uses its exact cyclic value and
multiplies the amplitude by z to that power. The initial word transformation
only normalizes diagonal polynomials and cancels adjacent H on the same axis.
It must not commute gates, identify different axes or erase global phase.

Prove H involution, polynomial normalization preservation and word
normalization preservation on arbitrary amplitude functions, including any
reference coordinate. Keep ownership and capacity checking separate; this
internal transformation does not authorize otherwise-invalid input, create
an external IR profile or enable a QFT/QPE registry entry. Later hierarchical
checking must validate all original nodes before applying these equalities.

The independent experiment compares native normalization with direct dense
complex action only at small widths (at most three), including arbitrary
complex reference amplitudes, all 256 phases, deliberate wrong order/axis/sign,
empty words and repeated cancellation. Large-axis symbolic examples must not
allocate dense matrices. Retain first proof diagnostics and actual commands.
These tests do not prove native compilation or source-to-IR correspondence.

## Implemented theorem and execution boundary

[Interference.lean](../lean-kernel/QleisliKernel/Interference.lean) proves
`hadamard_involution`, `diagonal_normalize`, `push_sound`, `normalize_sound`
and `normalize_reference` for the actual definitions. Normalization processes
a flat word once, retaining a reverse chronological stack; it performs no
matrix construction or basis enumeration. It does not simplify an arbitrary
unitary, expand a hierarchy, or count the execution cost of removed operations.

The [complex bridge](../lean/Qleisli/Interference.lean) imports that module
through a local Lake dependency. It constructs `complexModel` with proved
premises, establishes `root_phase` and `root_half_turn`, and instantiates the
word/reference equalities. `hadamard_pair_norm` and `diagonal_point_norm`
establish the local probability identities for those same definitions.
This is the first bridge to executable definitions, not a duplicate model.
The dependency is one-way: `lean/` imports `lean-kernel/`; the latter still
has zero external Lake dependencies and its own compiled audit.

`checked_phase_layout` applies the existing actual checker's theorem to weighted
basis transitions: for every input x and continuation f, the accepted graph
gives z^P(x)·f(L(x)). This is a basis-transition interpretation (the transpose
action on continuations), not an assertion that the backwards axis map acts
directly on output amplitudes. Complete matrix/instrument and QFT/QPE schema
proofs remain open. The local H/diagonal word is not yet integrated into the
typed graph verifier, and no H-bearing external artifact is newly accepted.

The [native harness](../scripts/test_lean_interference.py) builds a temporary
C-compiled Lean executable importing the actual normalizer, without adding a
production command. It covers **422 words**, including all 256 ticks, and
**1,260** independent joint-amplitude comparisons; four wrong phase/order/axis
transformations are distinguished. Dense dimension is at most eight in the
Python oracle and zero in normalization. A 4,096-H word and an axis index of
one million normalize symbolically. Those are internal equality experiments,
not claims that invalid external axes or excessive input are accepted.

The [second source](../tests/fixtures/lean_interference/reference_client/main.qli)
applies the same interference body to one half of a Bell pair. Source checks
compare two plus four probabilities with independent expectations. Original
source hashes, diagnostics and executed results are in the
[development record](../tests/fixtures/lean_interference/README.md).
