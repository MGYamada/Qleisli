# Imaginary Qleisli 1.0: amplitude estimation through shared QPE

Imaginary uncompiled QPE-based amplitude estimator, with shared [Grover](grover.md) and [QPE](qpe.md). Bounded [local clients](../../tests/fixtures/sized_clients/README.md) do not adopt the generic API or confidence contract.

## Algorithm body

Estimate p=<0|A†Pi_good A|0> for whole-space unitary A, total good and n, m>=1, using exact shared G rather than supplying a known answer. Return actual raw phase sample and certified classical evaluation error; target is explicitly discarded, not assumed restored/separable. Every repetition prepares afresh. Numerical evaluation may fail; eta is not evidence that a library achieved it.

```text
// IMAGINARY QLEISLI 1.0 — DESIGN CODE, NOT CURRENT SOURCE SYNTAX
use imaginary::grover::grover_iterate;
use imaginary::qpe::qpe;

observe fn amplitude_phase_sample<n,m>(
    static A: UnitaryOp<Bits<n>>,
    static good: BasisFn<Bits<n>, Bit>
) -> CBits<m> {
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

## Exact phase and instrument contract

G eigenphases are ±theta/pi with p=sin²theta. Use QPE positive Fourier/inverse and low-weight-first y; estimate probability sin²(pi y/M), not signed amplitude. Complete K_y governs correlated target/reference and discarded-target branch. -G shifts labels by M/2 and complements the ideal estimate; p=0/1 are exact boundaries. [Primary amplitude estimation](https://arxiv.org/abs/quant-ph/0005055) fixes this convention.

```text
K_y = (1/M) sum_{r=0}^{M-1} exp(-2 pi i r y/M) G^r.
```

```text
F_y(rho_DR) = tr_D[(K_y tensor I_R) rho_DR (K_y† tensor I_R)].
```

## Capabilities, resources, and accuracy

A/A† and controlled central reflections/oracle can derive controlled conjugation without controlled A; actual provider identity remains checked. QPE owns n+m plus exact-clean scratch and charges M-1 controlled G uses, M-1 each A/A† plus initial A. The probability bound below is ideal single-sample, not a certificate for each shot; justified classical evaluation adds eta. QFT/gate approximation and confidence amplification need separate instrument/statistical proofs, not leakage-based cleanup.

```text
Pr[ |sin²(pi Y/M) - p|
      <= 2 pi sqrt(p(1-p))/M + pi²/M² ] >= 8/pi².
```

## Proposed facilities and acceptance records

Unimplemented obligations. Review boundaries p=0/1/1/2, off-grid p=1/4, conjugate labels, -G, missing control, reversed bits and retained residual ownership. Generic capability/evidence, realizability, interval arithmetic and confidence-boosting policy remain open.

| ID / facility | Classification and intended type/effect | Acceptance / rejection and proposed IR responsibility |
| --- | --- | --- |
| AE-1 `amplitude_phase_sample` | Ordinary-definition candidate, `() -> CBits<m>` with `Observe`, parameterized by A/good/n/m. | Accept shared G with exact signs and justified control; reject a separately redefined −G with the unchanged decoder. Inline or retain checked calls, keep QPE's instrument and all final ownership. |
| AE-2 shared `qpe`, `grover_iterate`, controlled powers | Ordinary definitions with proposed static operation language support; `qpe` consumes and returns the target plus a classical word. | Accept reusable same-meaning implementations; reject discarded evidence, phase-equivalent-only substitution, mismatched axes, or unavailable control. Retain contracts through actual final IR. |
| AE-3 `discard(residual)` | Existing sealed observation principle, generalized through proposed sized types; `Q<Bits<n>> -> Unit`, `Observe`. | Accept any residual state, including reference correlations; reject silent pure release or omission of returned target ownership. Lower to a verified partial-trace operation. |
| AE-4 classical interpretation | Host-only proposal: `CBits<m> -> UInt`, then `(y,M,eta) -> Result<Real,EvaluationFailure>` and a record. | Accept valid bit order, M=2^m and certified absolute evaluation error; reject complement/endianness mistakes, failure suppression, or a claimed confidence interval from an unverified approximation. Host ABI, arithmetic and result representation are unresolved. |
| AE-5 error and statistical evidence | Unresolved contract representation for instrument accuracy and probability bounds; distinct from exact pure-operator evidence. | Accept explicitly proved premises and bounds; reject treating small leakage as cleanup evidence or a statistical theorem as a check on each shot. Future IR must bind implemented operation errors to the claimed instrument. |
