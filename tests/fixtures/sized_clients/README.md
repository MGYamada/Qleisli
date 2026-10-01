# Two local clients of the same shared QPE

These Qleisli-authored integration fixtures reuse the
[retained Qualtran-derived QPE definition](../../../corpus/sized/qualtran_qpe/estimation.qli)
through the experimental [source path](../../../docs/sized-corpus-source.md).
They are Apache-2.0 local verification material, not a fourth external corpus
or additional upstream translations. No upstream file was downloaded. The
existing three-source intake and thirty production CLI cases are unchanged.

Both clients consume and return the phase and target quantum registers, with
unitary effect. They do not yet initialize phase bits or consume them into
`CBits<m>`. The diagnostic branch vectors below are not a production measurement
instrument, a certified classical decoder or a proof of general source adequacy.

## Order probing

[order_phase](order.qli) forwards a declared `Controlled(U)` capability to the
same QPE source. The [mul_two](modular.qli) provider is explicit cyclic bit
rotation: for N=2^n-1, map each residue x<N to `2x mod N`, and fix the otherwise
unused label N. All basis amplitudes are +1. Fixing N is essential for a
permutation of the complete register; mapping it to zero would not be unitary.
The source extracts the high bit and reinserts it at the low position. It
contains no truth table and makes no general modular-synthesis claim.

With phase input zero and target input one, the orbit is
`1,2,...,2^(n-1)` and has length n. For M=2^m, the diagnostic phase distribution
is the equally weighted mixture of QPE kernels for eigenphases k/n. Width
three exercises phases that do not lie on a dyadic grid. The n=4,m=3 case
matches the existing N=15 baseline: labels 0,2,4,6 each have probability 1/4.
The [existing classical factor/retry contract](https://github.com/MGYamada/Qleisli/blob/7bfcd36916199b05d5ab11851d38d53375ccf71e/docs/arithmetic-order-finding.md)
is unchanged; this new coherent path has not yet connected measurement or
host postprocessing to its actual returned values.

The complete arbitrary-input contract is the shared QPE Walsh/DFT sum with
this specified modular permutation. Tests cover the unused label, every phase
input, target-reference correlations and reversed rotation. A reversed cycle
can preserve the order histogram while changing the residual target operator;
full complex-amplitude checks detect it.

## Finite amplitude estimation

[prepare](rotation.qli) applies `A = H P(j,d) H` to the low target bit and
identity to the spectators, where `P(j,d)=diag(1,exp(2*pi*i*j/2^d))` uses the
existing exact dyadic profile. Let alpha=pi*j/2^d. On zero input the success
probability of low bit one is `p=sin(alpha)^2`.

[reflect_low](reflection.qli) is the phase-fixed Z reflection on that low-bit
plane. [grover](amplification.qli) composes `G=A Z A† Z` using the same
preparation definition and its actual adjoint. This is a finite two-level
amplitude problem with spectator identity, not a general n-qubit zero-state
reflection or a generic predicate builder. [amplitude_phase](amplitude.qli)
prepares the target with A, then passes the actual G definition to shared QPE.

The independent oracle uses the closed formula

```text
A = exp(i alpha) exp(-i alpha X)
G^s A = exp(i alpha) [cos((2s+1)alpha) I - i sin((2s+1)alpha) X].
```

The initial global factor is retained in the full circuit comparison. G has
eigenphases ±alpha/pi; on the prepared zero-input trial they have equal weights.
The diagnostic grid estimate for phase label y is `sin(pi*y/M)^2`. At aligned
phases both labels give p. An off-grid case retains its entire distribution;
the grid value is not a per-sample certificate of the true probability.
Tests include p=0, p=1, p=1/2, complementary probabilities and a spectator.

The sign of G is observable under control: using -G shifts labels by M/2 and
changes the same decoder to the complementary estimate. Omitting A can leave
the phase histogram unchanged but changes the residual target; the complete
oracle detects this too. The numerical sine evaluation is a diagnostic, with
no certified rounding or statistical-confidence API claimed.

## Executable checks and source obligations

```sh
python3 scripts/test_sized_qpe_clients.py
```

The [validation record](validation.json) covers small target widths 1–4 and
phase widths 2–3, at most seven wires. It freshly inspects actual generated
hierarchies and finite equations, then tests independent full-input and coherent
reference formulas. Both clients contain calls to `estimate`; neither embeds
a separate QPE body. Mutating the common source breaks both clients' oracles.
There are 432 complete basis columns and 31 coherent reference columns, with
maximum observed error below 3.34e-15. Twenty-two native inspections pass,
including six valid-but-wrong algorithm variants, and one falsified finite
equation rejects. All six variants fail the independent semantic oracles;
eighteen malformed provider/source cases reject before execution.

Forwarded access is checked at each source boundary, including empty folds
and unselected branches. Apply/Adjoint do not imply Controlled. Static argument
kinds and declaration order, exact target widths, complete owner groups and
lexical hiding are retained. Transparent nested providers carry their actual
definitions and natural arguments. The instantiation cache includes the
complete nested provider assignments: using equal sizes with two different
phase providers cannot reuse the first provider's circuit. A three-wire
phase-sensitive test exercises that case.

The [authoring session](../authoring_sessions/sized-qpe-clients-v021/session.json)
preserves desired source before the missing static-argument parser rejection,
the first successful native checks and the final semantic run. This is informed
development, not a controlled model benchmark. Maximum-size testing is omitted
under the user's scope decision. Production source/runtime integration, named
algorithm binding, initialization/measurement and applicable R14/H1–H5 gates
remain open.
