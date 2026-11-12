# Independent expectations, frozen before execution

This is a two-qubit informed example, not a general CPTP or source-preservation
proof. Displayed kets use logical factor order |q,a>; observations are tuples
(q_result,a_result). Do not infer raw integer labels from ket typography. With
q on the least-significant physical axis, tuple (1,0) has raw label 1.

Let |psi> = alpha|0> + beta|1>, with |alpha|^2 + |beta|^2 = 1. Starting from
|psi>_q |0>_a, the common first CNOT produces alpha|00> + beta|11>.

- Coherent uncompute: the second CNOT returns |psi>_q |0>_a, with exact phase.
  After H(q), P(0,0)=|alpha+beta|^2/2 and P(1,0)=|alpha-beta|^2/2.
- Explicit reset: its hidden Kraus actions are I_q tensor |0><0|_a and
  I_q tensor |0><1|_a. The unnormalized histories are alpha|00> and beta|10>.
  Add their density matrices without interference:
  rho_out=(|alpha|^2|0><0|+|beta|^2|1><1|)_q tensor |0><0|_a.
  After H(q), P(0,0)=P(1,0)=1/2. All outcomes with a_result=1 have weight zero.

The source uses H(init0()), so alpha=beta=1/sqrt(2):

| First source | Expected check | Expected full output distribution |
| --- | --- | --- |
| coherent-uncompute | Accept; helper is Unitary, main is Observe | (0,0): 1 |
| explicit-reset | Accept; helper and main are Observe | (0,0): 1/2; (1,0): 1/2 |
| false-unitary-reset | Reject the helper: reset has Observe effect | No execution result expected |

Before the final H, both ancilla marginals are exactly |0><0|. The coherent
live state is |+><+|=[[1,1],[1,1]]/2; after reset it is I/2. Thus reset
DOES satisfy the clean fixed-state/separation condition while implementing
the wrong requested live unitary. This does not refute the all-input pure
marginal/factorization equivalence. The observer explicitly measures both
remaining owners; no general release API or implicit cleanup is used.

Reset histories remain unnormalized: for this source the post-H history
vectors are (|00>+|10>)/2 and (|00>-|10>)/2. Summing amplitudes between those
histories would incorrectly make (0,0) certain. Their probabilities add.
The false-unitary source differs from explicit-reset only in the helper effect
annotation. An observing caller cannot repair a falsely Unitary callee body.

For an arbitrary reference, the same elementary example sends
|0>_q|u>_E + |1>_q|v>_E to the sum of its two sector density operators under
reset, deleting cross terms while factoring out |0><0|_a. This explanatory
calculation is not a Lean theorem or a claim of general instrument correctness.
