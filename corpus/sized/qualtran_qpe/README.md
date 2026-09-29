# Shared coherent QPE source

[The same estimate definition](estimation.qli) accepts target width n, precision
m and a transparent phase-fixed `Op<Bits<n>>` provider. It calls ordinary
[Hadamard preparation](preparation.qli), controlled powers of that provider,
and the adjoint of the [existing shared Fourier source](../qualtran_qft/fourier.qli).
[Evolution](evolution.qli) is a replaceable test provider, not part of QPE's
algorithm meaning. This is the experimental development source path; production
CLI integration and the complete measured QPE API remain open.

## Contract and reading guide

The inputs and outputs are `(Q<Bits<m>>, Q<Bits<n>>)`, both consumed and
returned once, with unitary effect. Axis zero has weight one in each register.
Let M=2^m and U be the provider's phase-fixed operator. For arbitrary phase
input a and target state psi, the complete contract is

```text
|a>|psi>  ->  sum_y |y> [ (1/M) sum_s (-1)^popcount(a&s)
                                      exp(-2*pi*i*s*y/M) U^s ] |psi>.
```

All sums range over 0..M-1. On the prepared input a=0, the bracket is K_y(U),
the QPE branch operator. For an eigenvector with U|psi>=exp(2*pi*i*theta)|psi>,
its amplitude at y is the finite geometric sum
`(1/M) sum_s exp(2*pi*i*s*(theta-y/M))`. An exactly representable theta=z/M
gives label z with probability one; an off-grid phase has a distribution.
These statements retain global phase: replacing U by a scalar multiple changes
its controlled powers and QPE's answer.

Hadamards create the uniform sum over s when a=0. The k-th low-order bit
controls U^(2^k), so together the controls implement U^s. The inverse Fourier
transform resolves their relative phases. Returning the target matters: for
superposed eigenvectors it becomes correlated with the phase register. Tests
therefore compare complex amplitudes and target branch vectors, not only a
histogram or a separable eigenstate example.

The current function receives its phase register and returns it as quantum
data. Initialization and consumption by measurement into `CBits<m>` are still
required for the selected full QPE API. Diagnostic slicing of amplitudes into
branches is not that runtime or a proved measurement instrument.

## Execution and verification status

```sh
python3 scripts/compile_sized_corpus.py corpus/sized/qualtran_qpe/estimation.qli \
  --entry estimate --size n=1 --size m=3 \
  --module fourier=corpus/sized/qualtran_qft/fourier.qli \
  --operation U=evolution::evolve:1,1,3 --output /tmp/qpe13.json
python3 scripts/test_sized_qpe.py
```

The first command emits an untrusted proposal. The second freshly checks the
actual graph and finite equations, then compares it against the direct formula.
Following the 2026-09-30 user decision, remaining validation uses small qubit
systems only. It does not generate or check the maximum-size case. A successful
run does **not** mean the full measured API or release is complete.

| Target/precision | Native inspection | Structural work | Exact work |
| --- | --- | --- | --- |
| (1,3) | Pass | 1,112,204 | 402 |
| (2,4) | Pass | 1,655,343 | 536 |

The [validation record](../qpe-validation.json) includes 192 complete basis
columns and 14 reference columns across seven positive cases: both small
selected sizes, off-grid phase, non-basis eigenvectors, global scalar phase,
SWAP and a three-cycle target permutation. Six type-correct source faults pass
circuit inspection but fail the independent QPE formula. Falsified finite and
repeat equations reject in the verifier. Twenty-seven malformed source/provider
cases reject, including missing Controlled access at zero count or empty loop.
No independent named QPE request is implemented yet; numerical tests do not
issue algorithm evidence or prove source preservation.

The [local order/amplitude clients](../../../tests/fixtures/sized_clients/README.md)
now call this exact `estimate` definition through ordinary source operation
arguments. Order probing forwards a declared Controlled parameter; finite
amplitude estimation supplies its actual Grover-iterate body. Small native and
full-state/reference checks pass, including a shared-QPE mutation detected by
both clients. Their measured `CBits` and classical-result paths remain open.

Before that decision, the (8,8) proposal contained 330 shared definitions and
373,326 bytes, and failed the structural ceiling. That historical result is
retained in the authoring session; maximum-size validation is now deferred and
is not a completion requirement for the remaining corpus. No capacity success
is claimed and no budget was increased. Recursive
explicit QFT reversal did reduce its width-eight named check to 1,649,990
structural units, and all earlier Fourier tests still pass. It does not close
any untested large-system capacity claim.

## Provenance

Apache-2.0 translation of the already retained Qualtran `TextbookQPE`, commit
`8db02b8b3fb39d69d2900dcc7b52d9d6a36834c3`; preserve its 2024 Google attribution
and [license](../../upstream/qualtran/LICENSE). The
[original source](../../upstream/qualtran/qualtran__bloqs__phase_estimation__text_book_qpe.py)
and [finite QPE regression](../../qualtran/qpe2/README.md) are unchanged.
No upstream material was downloaded. The
[authoring session](../../../tests/fixtures/authoring_sessions/sized-qpe-v021/session.json)
retains first sources, actual failures and the attribution correction. It is
informed development, not a controlled model benchmark.
