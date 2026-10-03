# Standard-library direction

## Adopted library goal

A BLAS/LAPACK-like foundation combining reusable quantum source, textbook concepts/derivations and formal contracts. Until v0.5 algorithms go to corpus; then mathlib-style community growth under [STDLIB](../STDLIB.md). General APIs/organization/qlippy/borrowing remain future. Intent review is independent of conformance.

## Library areas and layers

Sealed primitives → ordinary composition/data structures → algorithms → teaching/evidence. Specify width/signedness/order/subspace; reversible full-space arithmetic/cleanup; phase/encoding/error-preserving transforms; access/success/iteration/precision/cost skeletons; fresh trials separate from host statistics/optimization. Block encoding fixes projectors/normalization/full unitary; success block is no unconditional pure map. Names/modules/arbitrary matrices are not adopted. [Current ledger](https://github.com/MGYamada/Qleisli/blob/v0.2.7/docs/stdlib-contracts.md).

## First algorithm skeleton contracts

Future metanotation, no current API. Descriptions capture no owners; application transfers them. No unrestricted free-vector bind.

| Candidate | Obligation |
| --- | --- |
| amplify(P,good,k) | Phase-fixed full-space unitary P with inverse; a=sin²θ, success sin²((2k+1)θ). Expand/reverify; k=0 only prepares, empty marked set has success0. Unknown owned state/Iso supplies no inverse reflection. |
| phase_estimate(U,m;q) | Positive precision, checked control/power, complete outcome/residual/reference instrument, retained target/low-bit readout. Reject Observe/aliases/hidden disposal. |
| simulate(H,t,ε;q) | Hamiltonian/access model, actual whole-space realization and certified compositional error; Hermitian matrix/name alone grants no efficient access. |
| estimate(prep,observable,plan) | Fresh preparation per destructive trial, finite host plan/statistical error. No unknown-state copying or one sample as expectation; retries/optimizer separate. |

Πgood=Σgood(x)|x><x|; O=I−2Πgood; R=P(2|0><0|−I)P†; G=RO; output G^kP|0>. QPE Ky=M⁻¹Σr exp(−2πiry/M)U^r, outcome (Ky⊗I)ρ(Ky†⊗I). Signs/scalars matter under control; exact cleanup, approximation, sampling and noise are distinct.

## Standard adoption and feedback

Extract from multiple corpus clients with fixed contracts/readable implementation/derivation path, independent semantics/faults, actual-IR binding and proof assumptions. Evaluate two uses plus a held-out problem, then intent/stability/phase/ownership/encoding/error/cost/compatibility review. Track gaps in Issues. Frequency and numerics alone grant no adoption/proof; informed authoring is no model benchmark.
<a id="5-標準への採用とaiからの還流"></a>
