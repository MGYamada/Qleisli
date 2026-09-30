# Three-bit iterative phase estimation

Run `cargo run --bin qleisli -- run examples/iterative_phase_estimation`.
The [entry point](main.qli) applies T to `|1>`. Its ideal distribution is
`1001` with probability one: low-weight phase bits first, followed by the
target's Z measurement. The floating-point reference `run` also lists
`0001`, `0011`, `0101` and `0111` with rounding residuals of about `1e-33`;
these are numerical artifacts, not additional ideal outcomes.

[iterative::phase3](iterative.qli) is an ordinary experimental `.qli` definition:
`Observe`, with `static U: Op<Bit>`, `requires Controlled(U)`, and runtime type
`Q<Bit> -> ((CBit,CBit,CBit),Q<Bit>)`. It consumes the input binding and returns
the conditional target owner. The input need not be an eigenstate and may be
entangled with a reference. No stdlib API, syntax or checker rule is added.

The three rounds use U⁴, U² and U. Each meter is measured and consumed before
the next `init0()`. Prior classical bits select T† and (T²)† corrections with
ordinary `if`. This uses at most one live logical meter alongside the target;
it makes no claim that the current IR/backend recycles physical wire IDs or
reduces the simulator's allocation. The target is neither reset nor discarded.

For output `y = low + 2*middle + 4*high`, the intended unnormalized branch is

```text
K_y = (1/8) sum_{r=0}^7 exp(-2*pi*i*r*y/8) U^r
rho -> (K_y tensor I_R) rho (K_y† tensor I_R).
```

The first round gives the low-weight bit: subsequent rounds remove low/4,
then low/8 + middle/4 cycles before their final H and measurement. The three
factors expand to the polynomial above. This fixes both feedback signs and
bit order and agrees with the existing coherent inverse-QFT QPE.

Run `cargo test --test iterative_qpe`. Finite checks cover all eight T powers,
both X eigenstates, identity preserving Bell coherence, and U = H T off the
phase grid. For H T, nine X/Y/Z measurement pairs on the reference and target
check every output branch against an independently evaluated Fourier polynomial
and against coherent QPE. Deliberate missing-feedback and reversed-bit-order
faults compile but fail the semantic oracle. Numerical tolerance is 1e-12;
these tests are not a general compiler/algorithm proof or hardware experiment.

Supplying an observe operation or missing controlled access must reject under
the existing operation rules. Reusing a measured meter violates ownership.
Before stdlib adoption, settle generalized types/precision, result roles and
the applicable exact-angle/evidence profile. The Bit-only interface and three
unrolled rounds retain the [A020-02/03 limitations](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/v0.2.0-backlog.md).
The [preserved authoring session](../../tests/fixtures/authoring_sessions/README.md)
records the informed first attempt and its actual observations.
