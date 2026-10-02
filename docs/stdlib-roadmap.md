# Standard-library direction

## Adopted library goal

Build a BLAS/LAPACK-like foundation integrating reusable quantum components,
a quantum-information textbook and formal specifications. Readers should learn
concepts/derivations from readable source, examples, counterexamples and explicit
proof status. Until v0.5 add algorithms to corpus; from v0.5 develop a mathlib-style
community library under [STDLIB.md](../STDLIB.md). Comprehensive generalized APIs,
qlippy and general borrowing remain future work. Specification-intent review is
independent of implementation conformance.

## Library areas and layers

Primitives use sealed contracts; structural composition prefers ordinary definitions
and specified language transformations. Data structures need width/signedness/order/
subspace contracts; arithmetic needs full-space reversible extensions and cleanup.
Transforms preserve phase/encoding/error; algorithm skeletons specify access, success,
iterations/precision/cost; hybrid patterns separate fresh quantum trials from host
statistics/optimizers. A block encoding additionally fixes projectors, normalization
and full unitary completion; its successful block is not an unconditional pure map.

Layers proceed from sealed operations and finite definitions through reusable
structures, algorithms, quantum-information explanations and evidence. These are
organization directions, not adoption of new names/modules or arbitrary matrices.
[Current ledger](stdlib-contracts.md) records the shipped finite definitions.

## First algorithm skeleton contracts

Candidate metanotation below creates no current API. Operation descriptions capture
no owners; application consumes/transfers owned resources. Arbitrary free-vector bind
is not adopted.

| Candidate | Contract and checking direction |
| --- | --- |
| amplify(P,good,k) | P phase-fixed whole-space unitary with inverse access; a=sin²(theta), success sin²((2k+1)theta). Expand finite oracle/reflection/repetition and reverify; k=0 prepares only, empty good set succeeds with probability zero. Unknown owned state/Iso preparation supplies no inverse reflection. |
| phase_estimate(U,m;q) | Positive precision, separately checked control/power access, full outcome/residual/reference instrument, retained target and low-bit readout. Reject Observe providers, aliasing and hidden disposal; [sized experiments](sized-corpus-source.md) do not implement the general API. |
| simulate(H,t,epsilon;q) | Explicit Hamiltonian/access model, actual whole-space realization and certified composition/error budgets. Expand contracted term evolutions; check approximation to H separately from IR unitarity. Hermitian matrix/name alone grants no efficient access. |
| estimate(prep,observable,plan) | Fresh preparation per destructive measurement, finite host trial plan and stated statistical error. No copying an unknown state or reporting one sample as expectation. Host retries/optimization are separate. |

```text
Π_good = Σ_{x:good(x)=1} |x⟩⟨x|
O_good = I - 2Π_good
R_ψ = P (2|0_A⟩⟨0_A| - I) P†
G = R_ψ O_good; output = G^k P|0_A⟩
K_y = (1/M) Σ_(r=0)^(M-1) exp(-2π i r y/M) U^r
E_y(ρ_AR) = (K_y ⊗ I_R) ρ_AR (K_y† ⊗ I_R)
```

Oracle/reflection signs and global phase remain observable under control. Cleanup
must be exact; approximation, sampling and noise are separate obligations.

## Standard adoption and feedback

Extract candidates from multiple corpus clients. Provide a short fixed contract,
readable ordinary implementation, concept/derivation reading path, independent
semantic/fault tests, actual-IR binding and explicit proof assumptions. Evaluate at
least two different uses and one problem not used for extraction; then review intent,
stability, phase/ownership/encoding/error/cost and compatibility before adoption.
Track unmet gates in Issues. Human/AI frequency and numerical agreement alone are
neither adoption criteria nor proofs; informed authoring is not a model benchmark.

<a id="5-標準への採用とaiからの還流"></a>
