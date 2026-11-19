# Comparing v0.2.9 and the unified source frontend

Issue #250 asks whether migrated programs preserve complex amplitudes and
measurement outcomes, including the residual quantum state. The
[observation record](checks.json) identifies the release sources, native
binaries and per-program observations. The baseline is release `v0.2.9`
(`a77e68f4`), and the beta source is `336438ef`. Both used their own public
CLI and native checker on macOS arm64. The released v0.2.9 native archive
matched its published SHA-256. The beta CLI was built from `11e036c8`,
whose Rust, embedded std and corpus sources match `336438ef`. The record
includes Git tree identities for 1,138 baseline files, 2,311 candidate
source files and the 720 tracked files in the native checker source tree.

## Finite corpus and examples

For each common project, run the v0.2.9 directory and the beta manifest's
current migrated directory through `qleisli run PROJECT --format=json`.
Compare every output probability, including outcomes present in only one
distribution. All 14 shipped example entry points are closed observing
programs. The measurements below additionally probe finite corpus kernels.

For a unitary on `n` bits, let `d = 2^n`. For each input column `x`,
prepare a meter in `|+⟩`. Arm zero maps the known input to the uniform
state by clearing the bits set in `x` and applying H to every bit. Arm one
calls the project's actual kernel. Measure the output register in Z. The
following joint probabilities recover the complex amplitude at output `y`,
including its phase relative to the reference arm:

```text
Re U[y,x] = sqrt(d) * (P(X+, y) - P(X-, y))
Im U[y,x] = sqrt(d) * (P(Y+, y) - P(Y-, y))
```

Both readings use unnormalized joint outcome weights. Compare each column
between releases and with the independent mathematical `reference_column`
in each release's `scripts/check_input_corpus.py`. The absolute amplitude
tolerance is 1e-10. The new `qualtran/qrom2_qmatch` kernel has a beta
observation and an independent reference. Its baseline field is absent.

For the five observing protocols, compare every outcome of each release's
`protocol_probes` with its prescribed distribution and with the other
release. These cover Bell labels and conditional reference states,
teleportation with retained measurement history, dense-coding messages
and the X-measurement effect. Probability tolerance is 1e-11. To
recheck a finite kernel separately, use its release's
`python3 scripts/check_input_corpus.py /path/to/qleisli --exhaustive --case SOURCE/CASE`
with `QLEISLI_KERNEL` set to the matching native binary. That command
probes each matrix entry individually.

## Fixed std declarations

One client imports all 12 public v0.2.9 functions and another imports all 26
beta functions. Both clients passed a public project check and produced the
expected equiprobable bit outcomes. The twelve public v0.2.9 declarations
also have individual client observations.
The seven unitary routines use the same two-arm reading with independent
Hadamard, reflection, positive Fourier and permutation formulas.
`increment2`, `add2` and `mul2_mod15` use the beta implementations in
`examples/order_finding/arithmetic.qli`. The `xor2` and `and2` clients
apply the Boolean result into a third bit by XOR while keeping both inputs.
Each two-bit register retains the original order inside its tuple tree.

For the three observing routines, prepare a Bell pair for each input with
a retained reference. For each classical result, measure all products of
X, Y and Z on the remaining reference and data wires. Compare each joint
probability between releases and to the Born probabilities of the X, Z
or ZZ-parity projectors. This gives 3 settings for `measure_x`, 9 for
`measure_z2` and 81 for `parity_zz`. The first `measure_z2` driver
shadowed gate `t` with a local bit. The record preserves the source and
type diagnostic alongside the result obtained with fresh local names.

## Sized sources

The 15 module records identify both selected sources by SHA-256 and record
the actual beta bytes after the bounded Fourier syntax translations. The
historical forward header needs `const`. Its inverse client also needs
curried `adjoint(fourier[n])(q)`. The first refusal and the repaired client
are both retained. These width-one and width-two observations concern the
historical Fourier experiment. Public generic QFT integration has its own
release scope.

For each selected entry and static argument assignment, run v0.2.9
`qleisli sized run` and beta `qleisli run --ir-profile=hierarchy --format=json`
with explicit module bindings, `--entry`, `--basis` and the corresponding
native checker. Preserve output widths and branch boundaries. Compare all
complex coefficients with independent analytic vectors, permutations or
measurement branches at tolerance 1e-11. The 27 paired configurations span
110 inputs and 700 coefficients. The initialization observer additionally
checks exact reference-bit preservation and every zero/readout branch at
widths one and two. Standalone isometry execution is supported in beta;
v0.2.9 reports its selected-root restriction. Both accepted the observing
client of the same preparation.

The observations establish bounded numerical agreement for the named
programs. The scope reported by the hierarchy runs is producer consistency.
Source-preservation proofs, wide generic instances and release-wide replay
have their own acceptance criteria.

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
