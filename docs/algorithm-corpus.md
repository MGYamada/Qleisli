<a id="アルゴリズム構造の初期コーパス"></a>

# Initial corpus of algorithm structures

Status: **initial organization of 20 entries** (2026-09-26). This corpus
supplies extraction material for the [second development goal](algorithm-structure-goal.md).
It includes derived algorithms, foundations, and protocols; the count does
not mean 20 independent speedup principles. The decompositions and Qleisli
mappings below are design analysis informed by primary sources, not quotations
from those papers or implemented guarantees. S1–S8 are the structure IDs in
the goal document. This English edition supersedes the earlier Japanese
corpus without changing its assumptions or implementation-status claims.

| ID, subject, and category | Input model and purpose | Extracted structure | Required premises / difference from the current core | Primary sources |
| --- | --- | --- | --- | --- |
| C01 Deutsch–Jozsa (phase version); algorithm | Distinguish a Boolean oracle promised to be constant or balanced. | S1, S2: Hadamard → phase marking → Hadamard → measurement. | Types alone do not establish the constant/balanced promise. Finite functions can be constructed with the current `with_computed`. | [Cleve et al., §3](https://arxiv.org/abs/quant-ph/9708016) |
| C02 Bernstein–Vazirani; algorithm | Recover a hidden bit string from access to `f(x)=s·x mod 2`. | S1, S2: Fourier sampling and a phase oracle. | Linear-function promise and bit order. The two-bit version is implemented and checked for every hidden string. | [Bernstein–Vazirani, Quantum complexity theory](https://people.eecs.berkeley.edu/~vazirani/pubs/bv.pdf) |
| C03 Simon; algorithm | Recover a period from the two-to-one structure `f(x)=f(x xor s)`. | S1, S2, S6: reversible evaluation → partial measurement → Hadamard → collect linear equations. | Collision promise, multi-output oracle, and classical GF(2) postprocessing. The current one-bit auxiliary oracle alone cannot express the general form. | [Simon](https://doi.org/10.1137/S0097539796298637) |
| C04 Shor factorization; algorithm | Find an order from an integer and a selected coprime base, then validate factor candidates classically. | S2, S4: reversible modular arithmetic, order finding, Fourier transform. | Arithmetic circuits, controlled powers, continued fractions, and retries. The finite N=15, base-2 example and continued-fraction candidate checking are [implemented and checked](arithmetic-order-finding.md). Efficient general-size arithmetic, precision selection, and automatic retries are unimplemented. | [Shor](https://arxiv.org/abs/quant-ph/9508027), [phase-estimation reformulation, §6](https://arxiv.org/abs/quant-ph/9708016) |
| C05 QPE; foundational algorithm | Estimate eigenphases using a phase-preserving unitary and an eigenstate or superposition of eigenstates. | S1, S4, S5: preparation, controlled `2^k` powers, inverse QFT, measurement. | General inputs produce a distribution according to their eigencomponents. Controllable implementation, precision, and bit order are required. Same-type static control, phases in units of π/4, and [operation-parameter two-/three-bit QPE](../examples/operation_algorithms/README.md) are implemented and tested with eigenstate and correlated inputs. General angles and size parameters are unimplemented. | [Cleve et al., §5](https://arxiv.org/abs/quant-ph/9708016) |
| C06 Grover; algorithm | Search a finite set using a marked predicate. | S1, S3, S5: uniform preparation, oracle, reflection, repetition. | Iteration count depends on the number of marked items. With two bits and one marked item, one iteration succeeds with probability one. Finite examples are implemented and checked. | [Grover](https://arxiv.org/abs/quant-ph/9605043) |
| C07 Amplitude amplification; generalization | Amplify the success amplitude of a preparation unitary `A` and a good predicate. | S1, S3, S5: `A`, `A†`, two reflections, repetition. | Inverse and phase of `A`, and initial success probability. An arbitrary state-preparation `Iso` cannot simply be inverted. The general form is unimplemented. | [Brassard et al.](https://arxiv.org/abs/quant-ph/0005055) |
| C08 Amplitude estimation (QPE version); generalization | Estimate a preparation procedure's good-outcome probability. | S3, S4: phase estimation of the amplitude-amplification operator. | Controlled amplification operator, conversion to probability, precision, and failure probability. Unimplemented. | [Brassard et al.](https://arxiv.org/abs/quant-ph/0005055) |
| C09 Quantum counting; derived algorithm | Estimate the number of marked items in a finite set. | S3, S4: convert a Grover-operator phase to a marked count. | Search-space size and error in the estimated count. Shares structure with C08. Unimplemented. | [Brassard–Høyer–Tapp](https://arxiv.org/abs/quant-ph/9805082) |
| C10 Szegedy walk; foundation | Coherently access transition probabilities and detect a marked set. | S1, S3, S5: transition preparation, product of subspace reflections, repetition/phase analysis. | Transition access and promises such as stationary distribution and spectral gap. An arbitrary classical random walk cannot be quantized for free. Unimplemented. | [Szegedy](https://arxiv.org/abs/quant-ph/0401053) |
| C11 HHL; algorithm | Obtain a solution-related state or observable from a matrix satisfying the required conditions and a state `\|b⟩`. | S1, S2, S4, S6: Hamiltonian evolution, QPE, controlled rotation, uncomputation, measurement. | Sparsity, condition number, input preparation, and a success flag. This is not a contract for efficiently outputting all components classically. Unimplemented. | [Harrow–Hassidim–Lloyd](https://arxiv.org/abs/0811.3171) |
| C12 Product-formula time evolution; method | Approximate evolution under a Hamiltonian decomposed into local terms. | S4, S5: exponentials of individual terms and ordered repetition. | Error from noncommuting terms, time, and subdivision count. Rotation angles and error budgets are unimplemented. | [Childs et al., A Theory of Trotter Error](https://arxiv.org/abs/1912.08854) |
| C13 LCU/Taylor time evolution; method | Approximate evolution using access to a linear combination of unitaries. | S1, S2, S3, S8: PREPARE, SELECT, inverse preparation, amplification. | Coefficient normalization, success subspace, and approximation error. Do not turn an arbitrary linear combination into a pure `bind`. Unimplemented. | [Berry et al.](https://arxiv.org/abs/1412.4687) |
| C14 Qubitization; foundation | Encode a Hamiltonian in a block of a specified unitary. | S1, S3, S8: build invariant subspaces from preparation, control, and reflection. | Normalization and encoding equation, auxiliaries, and controlled oracles. The evidence format is not yet designed. | [Low–Chuang](https://arxiv.org/abs/1610.06546) |
| C15 QSVT; foundation | Apply a polynomial transformation to the singular values of a block-encoded matrix. | S4, S5, S8: `U/U†`, projector phases, alternating layers. | Polynomial boundedness, degree, parity, and approximation error. Do not treat a general matrix directly as a unitary. Unimplemented. | [Gilyén et al.](https://arxiv.org/abs/1806.01838) |
| C16 VQE; hybrid algorithm | Estimate energy from an ansatz and Hamiltonian, and update parameters classically. | S1, S5, S6: parameterized preparation, observable measurement, statistical aggregation, optimization. | Ansatz expressiveness, measurement error, and convergence conditions. Only measurement components are expressible in the current core. General angles and host optimization are unimplemented. | [Peruzzo et al.](https://arxiv.org/abs/1304.3061) |
| C17 QAOA; hybrid algorithm | Build finite layers from a cost function and mixer, then sample candidates. | S1, S5, S6: alternating cost-phase and mixer layers, measurement, classical optimization. | Layer count, angles, and problem-specific performance. Shares host iteration with VQE, but not the same success guarantee. Unimplemented. | [Farhi–Goldstone–Gutmann](https://arxiv.org/abs/1411.4028) |
| C18 Classical shadows; measurement-estimation method | Measure fresh states from the same preparation procedure in random bases to estimate multiple properties. | S1, S6: measurement plan, destructive measurement, classical estimation. | Measurement ensemble, target observables, shadow norm, and error. Cannot require copies of an unknown state. Unimplemented. | [Huang–Kueng–Preskill](https://arxiv.org/abs/2002.08953) |
| C19 Stabilizer QEC; protocol family | Extract syndromes of commuting checks from data in a code space and recover. | S2, S6, S7: parity extraction, auxiliary measurement, decoder, conditional correction. | Code space, correctable error set, and errors in the measurement circuit. The initial case is limited to a three-bit code under ideal operations and at most one X error. | [Gottesman, Stabilizer Codes and Quantum Error Correction](https://arxiv.org/abs/quant-ph/9705052) |
| C20 Teleportation; communication protocol | Transfer an unknown input state to another resource using a shared Bell pair and two classical outcomes. | S1, S6, S7: entanglement preparation, Bell measurement, classical correction. | Measured input is consumed; output has distinct ownership. Preservation of reference correlations is a verification target. The [protocol corpus](../examples/protocols/README.md) now implements teleportation with seven state checks and branch-sensitive Bell-reference recovery; the general instrument proof remains open. | [Bennett et al.](https://journals.aps.org/prl/abstract/10.1103/PhysRevLett.70.1895) |

<a id="次の抽出課題"></a>

The [0.1.8 iterative QPE experiment](../examples/iterative_phase_estimation/README.md)
uses existing operations, measurement and classical feedback. Its fixed Bit
interface and three explicit rounds are retained as authoring evidence, not a
size-generic algorithm. [Tests](../tests/iterative_qpe.rs) check the joint phase/
reference instrument, and [session records](../tests/fixtures/authoring_sessions/README.md)
preserve the first source and subsequent observations.

The separately [licensed input corpus](../corpus/README.md), adopted on
2026-09-28 and expanded during 0.2.1 development, provides 30 finite translations from a closed set of three
sources. It is distinct from the C01–C20 research inventory above. Its fixed
QAOA/VQE kernels do not change the unimplemented general-algorithm claims in
that inventory. Contracts, original sources, actual authoring attempts and
independent semantic oracles accompany the translations.

The six 0.2.1 additions cover majority-oracle Deutsch–Jozsa, destructive Bell
measurement, constant addition, register equality, a two-wire LCU projector
embedding and a fixed quantum-kernel overlap. The LCU example returns its
selector and tests a chosen full unitary completion; it does not implement
general C13 time evolution or deterministic nonunitary projection. Bell
measurement is checked on its full conditional reference state. These remain
finite case-local definitions, not new standard APIs.

## Next extraction tasks

- Include signs and control capability in public S3 reflection contracts so
  that search, estimation, and walks can share them.
- Instantiate S4/S5 in QPE and check reuse in C04, C08, and C09.
- Give the single-trial instrument of S6 a separate interface from host
  statistical estimation and optimization.
- Manage S2 zero return, C19 code spaces, and S8 projected blocks as distinct
  forms of evidence.
- Add links for each row's finite implementation, rejection tests, complexity
  model, and general proofs. Do not count unimplemented rows as supported.
