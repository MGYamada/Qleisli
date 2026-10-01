# Imaginary Qleisli 1.0: quantum singular value transformation

Imaginary uncompiled alternating real-QSVT design; neither unconditional p(A), phase synthesis nor new language APIs are implemented.

## 1. Selected encoding and polynomial contract

Square exact same-zero-projector encoding, order ancilla/data and phase-fixed U plus adjoint. Scale alpha>0 and full-space implementation/axes are bound. Degree d>0, real p of parity d and |p|<=1 on [-1, 1]. Odd transform uses left/right singular spaces; even acts on the full right space including kernel p(0), not generally p(B). Empty ancilla remains owned. Rectangular/inexact encodings and d=0 require separate extensions. [Gilyén et al.](https://arxiv.org/abs/1806.01838) fixes the real-selector convention.

```text
E |psi> = |0^a> tensor |psi>,
Pi = E E†,
U unitary on H(Bits<a>) tensor H(Bits<n>),
E† U E = B = A/alpha,      alpha > 0,      ||A|| <= alpha.
```

```text
T_p(B) = L p(Sigma) V†    when d is odd,
T_p(B) = V p(Sigma) V†    when d is even.
```

## 2. Phase planning and the exact sequence convention

Uniform Re F_Phi=p (or certified epsilon_synth) must hold across the interval, not only sampled points. Mathematical one-based angles map to zero-based phi; rightmost factor acts first and chronological traversal is reversed. Positive/negative phase lists require a selector for the real construction. Exact tolerance needs exact evidence; synthesis failure is explicit. Review scalar d=1 Phi=0 and d=3 Phi=(pi, pi/2, pi/2), successful block 4x³-3x; complementary amplitude remains.

```text
R(x) = [[x, sqrt(1-x^2)], [sqrt(1-x^2), -x]],
D(phi) = diag(exp(i phi), exp(-i phi)),
F_Phi(x) = <0| (D(phi_1) R(x)) ... (D(phi_d) R(x)) |0>.
```

```text
// IMAGINARY QLEISLI 1.0 — host/elaboration boundary, not quantum execution.
host fn plan_real_qsvt(p: RealPolynomial, d: UInt,
    tolerance: Real) -> Result<PhasePlan, SynthesisError> {
    check_degree_parity_and_interval_bound(p, d)?;
    let candidate = synthesize_reflection_phases(p, d, tolerance)?;
    let certificate = verify_uniform_scalar_identity(
        p, candidate, reflection_product_convention, tolerance)?;
    Ok(PhasePlan(candidate, certificate))
}
```

```text
d odd:  U_Phi = R_Pi(phi_1) U R_Pi(phi_2) U† ... R_Pi(phi_d) U,
d even: U_Phi = R_Pi(phi_1) U† R_Pi(phi_2) U ... R_Pi(phi_d) U.
```

## 3. Visible alternating body and observation

Signed projector phases preserve both branch scalars. U/U† are unconditional on selector, so only phase control is required; controlling the full dilation later is a new access obligation. Carry returns selector and block, readout preserves every failure outcome and residual data owner.

```text
// IMAGINARY QLEISLI 1.0 — does not compile in v0.1.2.

unitary fn signed_projector_phase[static a, static n, static theta]
    (selector: Q<Bit>, block: Q<(Bits<a>, Bits<n>)>)
    -> (Q<Bit>, Q<(Bits<a>, Bits<n>)>) {
    let (ancilla, data) = split(block);
    let (selector, ancilla) = qif(selector, ancilla) {
        0 => zero_projector_phase<a>( theta),
        1 => zero_projector_phase<a>(-theta)
    };
    (selector, join(ancilla, data))
}

iso fn real_qsvt_dilation[static a, static n, static d,
    static U: UnitaryOp<(Bits<a>, Bits<n>)>,
    static plan: VerifiedPhasePlan<d>]
    (data: Q<Bits<n>>) -> (Q<Bit>, Q<(Bits<a>, Bits<n>)>) {
    let selector = h(init0());
    let block = join(init_zero<a>(), data);
    let (selector, block) = for static k in 0..d
        carry (s, q) = (selector, block) {
        let q = if static k % 2 == 0 { U(q) }
                else { adjoint(U)(q) };
        let (s, q) = signed_projector_phase[a, n, plan.phi[d-1-k]](s, q);
        yield (s, q);
    };
    (h(selector), block)
}

observe fn real_qsvt_observe[static a, static n, static d,
    static U: UnitaryOp<(Bits<a>, Bits<n>)>,
    static plan: VerifiedPhasePlan<d>]
    (data: Q<Bits<n>>) -> ((CBit, CBits<a>), Q<Bits<n>>) {
    let (selector, block) = real_qsvt_dilation[a, n, d, U, plan](data);
    let (ancilla, data) = split(block);
    let s = measure_z(selector);
    let b = measure_bits(ancilla);
    ((s, b), data)                 // Success exactly when s=0 and b=0^a.
}

observe fn real_qsvt_sample[static a, static n, static d,
    static U: UnitaryOp<(Bits<a>, Bits<n>)>,
    static plan: VerifiedPhasePlan<d>]
    (data: Q<Bits<n>>) -> ((CBit, CBits<a>), CBits<n>) {
    let (outcome, data) = real_qsvt_observe[a, n, d, U, plan](data);
    let sample = measure_bits(data);
    (outcome, sample)              // Preserve failed outcomes as well.
}
```

## 4. Complete instrument, references, and cleanup

Completeness sum K†K=I follows from full unitary/measurement, with arbitrary references. The success block is T_p(B), input-dependent probability norm squared and normalized output only when nonzero. Coarsening failure sums CP maps; sample consumes failure data too. Selector/encoding ancillas are measured, not clean workspace. Internal providers have separate exact cleanup even when the logical angle is approximated.

```text
V_Phi = (H tensor I)
        (|0><0| tensor U_Phi + |1><1| tensor U_(-Phi))
        (H tensor I).
```

```text
K_(s,b) = (<s| tensor <b| tensor I_data)
          V_Phi (|0> tensor E).
```

```text
K_(0,0^a) = T_p(B),
Pr[success | psi] = ||T_p(B)|psi>||^2.
```

## 5. Error, success, host work, and resource accounting

Uniform polynomial, scalar-synthesis and full-circuit errors add for the unnormalized block. Contractions with operator error epsilon differ in success probability by <=2 epsilon; normalized conditional error needs a success lower bound. A justified circuit bound is d delta_U+sum delta_phi plus other gates; a block-only encoding error supplies no full-U bound. Costs are d signals (ceil(d/2) U, floor(d/2) U†), d phases, n+a+1 plus workspace, two H and a+1 measurements (+n for sample), O(d) sequence records before expansion. Input loading/phase planning/synthesis and fresh retries need separate costs/access; no success lower bound is implied.

## 6. Proposed facilities and intended acceptance boundaries

Proposed evidence/ownership/accuracy facilities only; normalization, even/odd spaces, complete outcomes, exact scratch and phase ordering are essential.

| ID / facility / classification | Types, ownership, effect, and intended IR route | Intended acceptance and rejection |
| --- | --- | --- |
| QSVT-1: sized registers, operation/plan parameters and finite fold; language forms | Static `UnitaryOp<(Bits<a>,Bits<n>)>` and checked `VerifiedPhasePlan<d>`; each application consumes/returns the complete owner. Carry retains selector and block. Specialize checked finite operations, bounds, and axis layouts. | Accept finite positive `d`, a phase vector of length `d`, and no captured live owners. Reject parity/length mismatch, duplicate selector/target ownership, omission of carried data, or a zero-degree plan under this body. |
| QSVT-2: exact block encoding; unresolved evidence schema, supplied by an ordinary implementation | `U:Q<(Bits<a>,Bits<n>)> -> Q<(Bits<a>,Bits<n>)>`, `Unitary`; retain `alpha`, `E`, and actual `E† U E=A/alpha` binding in independently checked IR evidence. | Accept an explicit normalized encoding and adjoint capability. Reject treating `A` as unitary, erasing its scale, or substituting a different padded/axis layout. |
| QSVT-3: phase planning and scalar verification; host-only processing, evidence schema unresolved | Total budgeted `plan_real_qsvt -> Result<PhasePlan,SynthesisError>`; no quantum owners or quantum effect. Retain coefficient/parity/bound evidence, phase convention, and verified uniform error in elaborated metadata. | Accept an independently verified exact or bounded-error plan. Reject a floating list without evidence, point-sampled agreement as an interval proof, or an optimizer failure silently treated as a circuit. |
| QSVT-4: exact projected phases; ordinary definition over an unresolved phase primitive | `zero_projector_phase:Q<Bits<a>> -> Q<Bits<a>>`, `Unitary`; `signed_projector_phase` returns selector and block. Lower exact diagonal branch phases and optional proved predicate uncomputation. Arbitrary-angle primitive/synthesis classification remains unresolved. | Accept the stated `exp(i theta(2Pi-I))` convention with both branches' phases. Reject replacing it by `exp(2i theta Pi)` while dropping the branch-dependent factor, or reversing `phi` traversal without changing evidence. |
| QSVT-5: register initialization and consuming readout; ordinary definitions over sealed primitives | Fresh zero initialization is `Iso`; `measure_bits` is `Observe`. `real_qsvt_observe` returns every residual data owner and every measured flag, with explicit complete CP outcomes in IR. | Accept failure plus its surviving data. Reject pure release of encoding ancillas, postselection without a failure result, or implicit discard of returned data. |
| QSVT-6: approximation and success contracts; unresolved evidence schema | Retain operator/scalar error metrics, intervals, probability premises, reference extension, and implementation identities alongside exact resource/cleanup evidence. | Accept unnormalized-block error with its assumptions. Reject interpreting a small leakage bound as exact zero return, treating parity-even output as left-space output, or promising normalized output accuracy without a success bound. |

## 7. Open questions and review targets

Open questions and review targets below remain future work; no executed compiler tests or complete-generalization claims.

- **QSVT-O1:** Select finite coefficient/angle representations, a budgeted
  synthesis algorithm, and an independent interval/certificate checker.
  An ideal real-number oracle is not an implementation choice.
- **QSVT-O2:** Specify generalized projected-unitary evidence and its
  preservation through static inverse, phase composition, final IR, and
  observation. The current exact finite evidence checker has not acquired
  these capabilities because this document names them.
- **QSVT-O3:** Extend only after selecting rectangular/different-projector
  conventions, inexact encoding robustness, and kernel behavior. The square
  same-projector equations must not be transplanted without those changes.
- **QSVT-O4:** Review future scalar checks with `d=1`, `d=2`, an odd polynomial
  with `p(1)<1` that needs the selector, an even nonzero `p(0)`, and a zero
  singular value. Test a non-Hermitian block to distinguish singular transforms
  from matrix polynomials and even from odd output spaces.
- **QSVT-O5:** Proposed failure checks include a reversed phase vector,
  missing adjoint, dropped normalization, a measured selector reused as a
  quantum owner, discarded failure data, and approximate ancillas passed to
  pure release. None are presented as executed compiler tests.
