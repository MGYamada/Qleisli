# Imaginary Qleisli 1.0: amplitude estimation through shared QPE

Status: **initial design draft, unimplemented and noncompiling** (2026-09-27).
This original design code uses the [shared future-language notation](../language-evolution.md),
the [Grover iterate](grover.md), and the [QPE body](qpe.md). None of its proposed
generalized types or functions is a current public API. This initial variant
uses phase estimation; iterative and maximum-likelihood variants would need
different observation and statistical contracts.

## Algorithm body

The task is to estimate the success probability
`p = <0^n| A† Pi_good A |0^n>`. Here `A` is a unitary on the entire n-bit
register, `good: Bits<n> -> Bit` is total, and `n,m >= 1` are finite static
parameters. The desired probability is not provided as an input or encoded as
a known answer. Required controlled access concerns the exact shared iterate
`G = (2|psi><psi|-I)(I-2Pi_good)`, with `psi=A|0^n>`.

```text
// IMAGINARY QLEISLI 1.0 — DESIGN CODE, NOT CURRENT SOURCE SYNTAX
use imaginary::grover::grover_iterate;
use imaginary::qpe::qpe;

observe fn amplitude_phase_sample<n,m>(
    static A: UnitaryOp<Bits<n>>,
    static good: BasisFn<Bits<n>, Bit>
) -> CWord<m> {
    let G = grover_iterate<n>(A, good);
    let target = A(init_zero<n>());
    let (phase_word, residual) = qpe<n,m>(G, target);
    discard(residual);
    phase_word
}

// HOST PSEUDOCODE — CLASSICAL POSTPROCESSING OF ONE ACTUAL SAMPLE
host fn estimate_probability<n,m>(A, good, eta_classical: PositiveRational)
    -> Result<ProbabilityEstimate, EstimationFailure> {
    let phase_word = sample(amplitude_phase_sample<n,m>(A, good))?;
    let y = decode_word(phase_word);
    let M = 2^m;
    // Mathematical target: p_grid = sin(pi * y / M)^2.
    let p_hat = approx_sin_squared_pi_ratio(y, M, eta_classical)?;
    Ok(ProbabilityEstimate {
        value: p_hat,
        raw_phase_word: phase_word,
        phase_denominator: M,
        classical_error_bound: eta_classical
    })
}
```

`use imaginary::...` denotes links between these documentation drafts, not an
existing module namespace. `qpe<n,m>` returns both the measured phase word and
the still-owned target. The explicit discard is `Observe`; the target is not
assumed restored to its prepared state or separable after phase measurement.
There is one preparation per sample. Repeated estimates must invoke this
closed trial afresh, with an explicit policy, rather than reuse or clone its
former quantum input.

The proposed classical helper returns a number in `[0,1]` within absolute
`eta_classical` of `sin²(pi y/M)`, or reports an evaluation failure. Its finite
representation and certified implementation are unresolved. Recording a chosen
tolerance is not evidence that an arbitrary numerical library achieved it.
The returned record preserves the raw sample and its interpretation, not a
per-sample certificate that this estimate is close to the unknown p.

## Exact phase and instrument contract

Using the normalized good/bad plane from [Grover](grover.md), the shared G has
eigenvalues `exp(±2i theta)` where `p=sin²(theta)` and `0<=theta<=pi/2`.
Its phase alternatives are `theta/pi` and `1-theta/pi` modulo one. Their
amplitude estimates agree because `sin²(pi t)=sin²(pi(1-t))`.
This is the phase-estimation amplitude estimator of
[Brassard, Hoyer, Mosca, and Tapp, Section 4](https://arxiv.org/pdf/quant-ph/0005055).

The QPE convention is positive-sign Fourier transform followed by its inverse
after the controlled powers. Bit k of `phase_word` has weight `2^k`;
`decode_word` returns `y = sum_k 2^k bit_k`, with `0<=y<M` and `M=2^m`.
The returned scalar estimates probability p, not a signed or complex amplitude.
Estimating its nonnegative square root requires another error analysis near
p=0; the code makes no such amplitude-error claim.

For the exact specified G, define the full target operator

```text
K_y = (1/M) sum_{r=0}^{M-1} exp(-2 pi i r y/M) G^r.
```

QPE has branch map `(K_y tensor I_R) rho_DR (K_y† tensor I_R)` and returns D.
After our explicit discard, the branch on a possibly correlated reference is

```text
F_y(rho_DR) = tr_D[(K_y tensor I_R) rho_DR (K_y† tensor I_R)].
```

The closed trial inserts `rho_D=|psi><psi|`. Classical evaluation maps each
y to its reported estimate without suppressing any branch. The total outcome
instrument preserves trace; host execution errors are recorded separately.
For `0<p<1`, the phase distribution is the equally weighted sum of the two
eigenphase QPE distributions. Coherences and the residual target are governed
by the complete K_y equation, not by pretending each shot began in one known
eigenstate.

Changing G to −G adds one half to its phases. With m>=1 this shifts grid labels
by M/2 modulo M and changes the ideal postprocessed estimate to its complement.
The reflection sign is therefore an observable part of this shared interface.
At p=0 the ideal estimate is 0; at p=1, even M represents phase 1/2 exactly
and the ideal estimate is 1. These are useful boundary counterexamples to an
incorrect sign convention, not results of executing the proposed source.

## Capabilities, resources, and accuracy

The builder needs A apply/inverse access and exact predicate/zero-reflection
implementations. This client additionally needs a phase-fixed controlled G and
its finite controlled powers. Use the selected
[conjugation derivation](../decisions/2026-09-27-v1-path.md#control-through-conjugation):
controlled `A R0 A†` needs A and A† access plus controlled R0, not controlled A.
The phase oracle can likewise control its central Z while computing/uncomputing
its predicate unconditionally with checked exact cleanup. Fixed-width
`controlled_op(conjugate_op(A,R0))` now supports the first derivation under the
[M1 contract](../next-minor-spec.md); the sized builder and automatic recognition
of arbitrary computed predicates in this draft remain future work. Alternatively,
controlled G may be supplied with independently checked matching evidence.
An opaque unitary device, a state-preparation sample, or an uncontrolled oracle alone does not
satisfy it. A finite repeated implementation of powers is permitted with its
full cost; efficient direct power access is a separate assumption.

Before measurement, the routine owns n target and m phase qubits, plus every
implementation's private scratch. QPE consumes the phase register and returns
the target; the caller explicitly discards that target. Each private flag or
scratch region inside A, G, or QFT must return exactly to zero and separate
from every valid input/reference before any pure release. Statistical error,
operator approximation, and discarded final target ownership do not authorize
an otherwise invalid private pure release. The composed routine is `Observe`,
not `Unitary` or a pure intertwining contract alone.

For ideal exact components, the standard single-sample guarantee is

```text
Pr[ |sin²(pi Y/M) - p|
      <= 2 pi sqrt(p(1-p))/M + pi²/M² ] >= 8/pi².
```

This is [Theorem 12 of the primary paper](https://arxiv.org/pdf/quant-ph/0005055).
The result is a probabilistic bound, not a deterministic certificate for the
observed Y. A separately justified classical evaluation adds `eta_classical`
to that absolute-error bound. In particular a p-independent upper bound is
`pi/M + pi²/M² + eta_classical`. No arbitrary requested confidence follows from
m alone, and a single sample cannot reveal whether it was an outlier.

The initial draft assumes exact A, G, and QFT. Approximate controlled gates or
QFT need an additional error metric and compositional instrument/phase analysis
before the above guarantee can be transferred. General exact-angle syntax,
angle synthesis, and those approximation certificates are not implemented.
Confidence amplification by independent repetitions is future host-policy
work, requiring an explicit estimator and failure calculation.

With straightforward repeated controlled G, the QPE powers use
`1+2+...+2^(m-1)=M-1` controlled iterates. Each decomposed iterate contains
one A†, one controlled R0, one A, and one controlled O_good when using the
conjugation rule; A and A† are unconditional. Thus this construction uses M-1
calls each to A† and A, and state preparation uses A once more. A computed
O_good uses unconditional predicate compute/uncompute and controlled central Z.
The alternative gate-by-gate construction controls A† and A as well; that is
what current flattened `qif` would do. Neither construction makes power access
unit-cost, and no cancellation between iterates is assumed. The phase-register
preparation and inverse QFT, predicate compute/uncompute, classical decoding,
and bounded numerical evaluation have separate costs. A compact `power` or
operation description does not imply compact expanded IR or unit-cost oracle
access. Memory includes private scratch as well as n+m logical data qubits;
generation and execution costs must both be reported.

## Proposed facilities and acceptance records

All entries below are **unimplemented design obligations**. They supplement
the shared Grover and QPE records rather than adopt new standard definitions.

| ID / facility | Classification and intended type/effect | Acceptance / rejection and proposed IR responsibility |
| --- | --- | --- |
| AE-1 `amplitude_phase_sample` | Ordinary-definition candidate, `() -> CWord<m>` with `Observe`, parameterized by A/good/n/m. | Accept shared G with exact signs and justified control; reject a separately redefined −G with the unchanged decoder. Inline or retain checked calls, keep QPE's instrument and all final ownership. |
| AE-2 shared `qpe`, `grover_iterate`, controlled powers | Ordinary definitions with proposed static operation language support; `qpe` consumes and returns the target plus a classical word. | Accept reusable same-meaning implementations; reject discarded evidence, phase-equivalent-only substitution, mismatched axes, or unavailable control. Retain contracts through actual final IR. |
| AE-3 `discard(residual)` | Existing sealed observation principle, generalized through proposed sized types; `Q<Bits<n>> -> Unit`, `Observe`. | Accept any residual state, including reference correlations; reject silent pure release or omission of returned target ownership. Lower to a verified partial-trace operation. |
| AE-4 classical interpretation | Host-only proposal: `CWord<m> -> UInt`, then `(y,M,eta) -> Result<Real,EvaluationFailure>` and a record. | Accept valid bit order, M=2^m and certified absolute evaluation error; reject complement/endianness mistakes, failure suppression, or a claimed confidence interval from an unverified approximation. Host ABI, arithmetic and result representation are unresolved. |
| AE-5 error and statistical evidence | Unresolved contract representation for instrument accuracy and probability bounds; distinct from exact pure-operator evidence. | Accept explicitly proved premises and bounds; reject treating small leakage as cleanup evidence or a statistical theorem as a check on each shot. Future IR must bind implemented operation errors to the claimed instrument. |

Planned review cases include p=0 and p=1, p=1/2 on the exact grid, a non-grid
probability such as p=1/4, conjugate phase labels with identical estimates,
the −G complement counterexample, missing control access, reversed bit order,
and a returned residual that must be consumed. Reference-sensitive tests belong
to the shared K_y instrument, while the probability-estimation promise assumes
the particular prepared input A|0^n>. General-source compilation, numerical
execution, and Lean verification of this draft have not occurred.

Open questions are the generalized capability/evidence representation, exact
or approximate QFT realization, statistical-contract checking, certified
classical arithmetic, and a specified confidence-boosting host strategy.
Their resolution and the [standard-library adoption criteria](../stdlib-roadmap.md#5-標準への採用とaiからの還流)
precede implementation/adoption claims. The broader amplitude-estimation draft
does not add an extra executable algorithm to V1-C1–C5.
