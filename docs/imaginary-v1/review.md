# Initial corpus semantic review

Status: **initial design review completed; implementation and general proofs
remain open** (2026-09-27). This records P012-4 of the
[0.1.2 plan](../releases/v0.1.2.md). The [six drafts](README.md) and
[shared requirements](requirements.md) are reviewable design artifacts.
They have not been parsed, compiled, or executed as Qleisli source.

## Review scope and corrections

The review compared the displayed bodies with their mathematical equations,
traced live owners and residual states, checked shared conventions, and
consulted the primary references linked in each draft. Independent readers
cross-checked QPE/Shor and Grover/amplitude estimation; the integrated review
also checked walk and QSVT conventions. This is a documented design review,
not peer-reviewed research, a machine proof, or general compiler validation.

| Boundary | Counterexample or failure mode | Recorded disposition |
| --- | --- | --- |
| Current language versus future notation | A planned `UnitaryOp` or sized type is mistaken for a shipped API | Every draft is explicitly imaginary; current v0/SC/FC norms remain authoritative. P012-0 corrects stale finite-v0.1 status text without altering rules. |
| Basis labels versus classical words | A measured register is returned as an unexplained `Bits<n>` basis value | Normalize readout to `CBits<n>` in all drafts; retain `Bits<n>` inside the basis/ownership notation. Static operation closures share `unitary_op` where used. |
| QPE Fourier and axis order | Dropped reversal or wrong Fourier sign changes phase 1/4 from word 1 to word 3 | QPE displays the positive QFT body with reversal, applies its adjoint, and specifies little-endian decoding and the complete `K_y` instrument. |
| QPE residual correlations | Correct phase probabilities accompany an incorrectly reset or discarded target | Return the target owner explicitly; preserve the branch CP map with arbitrary references. AE and Shor explicitly discard their residual targets with observation effect. |
| Grover and amplitude-estimation phase | Replacing `G` by `-G` leaves isolated search probabilities unchanged but complements AE's probability estimate | Share `G=(2 ket(psi)bra(psi)-I)(I-2Pi_good)` exactly, with a phase-fixed control contract. Keep the `sin²` decoder and endpoint behavior consistent. |
| Shor arithmetic and reconstruction | Mapping padded x=N to zero is noninjective; an unverified denominator or nonminimal period produces a false success claim | Define full-space identity outside residues, bind inverse/power evidence, check modular exponentiation and nontrivial factors. An order candidate need not be minimal if the factor is independently verified. |
| Shor host errors and static inputs | Failed compilation/execution becomes an algorithmic sample, or host I/O silently enters a static builder | Show fallible host calls and error propagation in the body; bound provider indices and sizes. Deterministic exact arithmetic may be staged, while randomness and I/O remain at the host boundary. |
| Quantum walk model | A classical row sampler is treated as coherent access, or reflection order is reversed | Select symmetric padded Szegedy access, fix `W=R_B R_A`, and require full-space row unitaries with inverse. The draft only promises its stated sampling instrument. |
| QSVT parity and real polynomial | A real bounded polynomial is assumed to be a direct single-sequence block; even output uses the wrong singular space | Specify the scalar convention, the opposite-phase selector, and even right-space/odd right-to-left-space transforms, including the kernel. |
| QSVT success and cleanup | A useful projected block is returned as an unconditional pure operation | Measure selector/encoding flags, return all failure branches and residual data. Provider workspace alone is eligible for a separate exact cleanup proof. |
| Approximation and capabilities | Small error certifies pure release, or apply-only access implies free control/inverse/powers | Keep error, access, success, and exact zero-return contracts separate; enumerate unresolved certificates and construction costs. |

## Reproducible finite mathematical checks

Run from the repository root:

```sh
python3 scripts/check_imaginary_v1_examples.py
```

The [script](../../scripts/check_imaginary_v1_examples.py) passes **52 checks**:

- Compare the displayed QFT gate ordering at widths 1–4 with every entry of
  the independently specified positive Fourier matrix; check phase decoding,
  normalization, and a QPE instrument's completeness and Bell-reference branches.
- Compare a four-item Grover result and a nonuniform amplification plane with
  analytic success laws; distinguish controlled signs and AE conjugate phases.
- Check small full-space modular permutations and inverse-related rejection
  boundaries, verified factor outcomes, and unhelpful period candidates.
- Check a symmetric two-state walk's encoding, reflection product, stationary
  vector, and the counterexample to reversing the two reflections.
- Check odd/even scalar QSVT identities and a non-Hermitian block dilation;
  distinguish singular transforms from matrix polynomials and even right-space
  from left-space output. Check the real-polynomial selector and its complete
  success/failure instrument.

These are small Python mathematical models, using floating-point tolerance
`1e-11` for matrices and exact integer/rational arithmetic where stated. A
manual transcription of a gate order is not a parser or lowering test. The
fixtures do not prove interval polynomial admissibility, general algorithms,
exact zero return, or current/future compiler correctness. In particular they
do not make the imaginary source executable. The existing
[exact semantic examples](../../scripts/check_semantic_contract_examples.py)
and Rust/Lean validations have their own recorded scopes.

## Prerequisite disposition and unresolved decisions

All six initial bodies, per-draft contracts, capability/ownership/effect
records, classifications, open questions, shared index and review now exist.
This satisfies the **initial design-corpus prerequisite** as specified in
[release milestones](../release-milestones.md#pre-v020-imaginary-v1-code).
It does not satisfy V1-C1–C5, adopt the imaginary grammar, or implement 0.2.0.
The [conformance ledger](../specification-status.md) records this limited result.

Open decisions include static type/capability inference, scalable retained
evidence, exact versus approximate rotations, independent interval/phase
certificates, general reversible arithmetic, coherent input loading, and the
host sampling/failure ABI. Walk detection promises and broader QSVT encodings
remain outside the selected first variants. A global Shor confidence contract
and confidence-boosted amplitude estimation are also still open.

At this initial review, the next step was to select an English extension
specification. The subsequent [M1 rules](../next-minor-spec.md),
[machine contracts](../machine-interface-spec.md) and
[M2 checker profile](../hierarchical-ir-spec.md) settle fixed-width access syntax,
external ABI and ideal dyadic checking decisions. Remaining general requirements
above are not implementation claims. New rules must include actual acceptance/rejection
and source-to-IR evidence before implementation. The general finite-core
adequacy and soundness proof obligations continue independently.
