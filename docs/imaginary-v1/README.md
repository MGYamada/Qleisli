# Imaginary Qleisli 1.0 algorithm corpus

Status: **initial design drafts for the pre-0.2.0 prerequisite** (2026-09-27).
All code in this directory is **imaginary, uncompiled, and unimplemented**.
It is not normative `.qli`, a shipped standard API, or evidence that v1 is
complete. The current executable language remains the [finite core](../language-spec.md).
The [English language evolution framework](https://github.com/MGYamada/Qleisli/blob/7bfcd36916199b05d5ab11851d38d53375ccf71e/docs/language-evolution.md) supplies
the common conventions; [release milestones](../release-milestones.md) define
the authoritative prerequisite and the separate V1-C1–C5 acceptance target.

The drafts are original Qleisli design examples based on the mathematical
algorithms cited in each document. Their contents are covered by the repository's
[Apache-2.0 license](../../LICENSE), with existing third-party references retained
as references rather than imported source code.

## Corpus and shared structure

| Draft | Exposed composition | Reused concepts |
| --- | --- | --- |
| [QPE](qpe.md) | Phase-register preparation, controlled powers, inverse QFT, measurement, residual target | Phase-fixed operation access, sized registers, instruments |
| [Grover](grover.md) | Preparation, good-state oracle, preparation-state reflection, repetition, checked candidate | Exact uncomputation and reflection signs |
| [Amplitude estimation](amplitude-estimation.md) | Grover iterate, shared QPE, phase-to-probability conversion | The same preparation, predicate, iterate, and QPE contracts |
| [Shor](shor.md) | Classical preprocessing, reversible modular powers, shared QPE, period/factor validation, retries | QPE, whole-space arithmetic, bounded host trials |
| [Quantum walk](quantum-walk.md) | A specified walk model, coherent transition preparation, reflections, step composition, observation | Preparation/inverse access and subspace contracts |
| [QSVT](qsvt.md) | Projected-unitary access, phase sequence, alternating signal transformations, use of the resulting block | Inverse access, projector phases, explicit success branches |

These six drafts test the proposed vocabulary across distinct uses. QSVT and
walk variants have incompatible conventions if combined carelessly; each draft
fixes its own selected model. Their existence does not require shipping all six
algorithms in v1. Executable Shor, QPE, and Grover remain the acceptance target.

## How to read and review a draft

1. Read its status, register layout, and input promises before the code.
2. Follow consumed and returned quantum ownership through every stage.
3. Compare the body with its phase-fixed operator or full observation instrument.
4. Check access, accuracy, success/failure, and cost assumptions separately.
5. Follow its missing facilities into the [shared requirements](requirements.md).
6. Consult the [semantic review](https://github.com/MGYamada/Qleisli/blob/7bfcd36916199b05d5ab11851d38d53375ccf71e/docs/imaginary-v1/review.md) for counterexamples, revisions,
   finite mathematical checks, and open decisions.

The requirement index is a design ledger, not a list of adopted features.
Unresolved contracts are allowed when explicit. An initial draft may change
after a counterexample. The [conformance record](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/specification-status.md)
records prerequisite completion separately from any future implementation,
validation of compiled programs, proof, or release publication.
