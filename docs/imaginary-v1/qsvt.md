# Imaginary Qleisli 1.0: quantum singular value transformation

Status: **initial design draft; uncompiled imaginary code** (2026-09-27).
Every size, static operation parameter, phase-plan record, and API below is a
proposal. The [shared notation](../language-evolution.md) governs ownership
and effects; the [finite-core specification](../language-spec.md) remains
the current language. This draft exposes an alternating circuit and its
observed block. It does not add an unconditional operation `p(A)` to the
pure language, implement phase synthesis, or prove compiler correctness.

## 1. Selected encoding and polynomial contract

This first draft chooses a **square exact block encoding with the same
zero-ancilla input and output projector**. Rectangular matrices, different
projectors, and nonzero encoding error require separate extension records.
For finite static `a,n`, the block register order is `(ancilla:Bits<a>,
data:Bits<n>)`, with little-endian axes inside each register. Let

```text
E |psi> = |0^a> tensor |psi>,
Pi = E E†,
U unitary on H(Bits<a>) tensor H(Bits<n>),
E† U E = B = A/alpha,      alpha > 0,      ||A|| <= alpha.
```

Access to the phase-fixed implementation `U` **and its adjoint** is required.
Knowing entries of `A` or being able to multiply classical vectors by `A`
does not supply that access. The scale `alpha`, embeddings, ordered axes,
implementation identity, and equality are part of the encoding evidence.
If `a=0`, the empty register remains an owned resource and all structural
rules still apply; an implementation may instead select `a>=1` as its future
profile, with that decision made explicitly.

Choose a real polynomial `p` of degree at most a positive static `d`, with
parity `d mod 2` and `|p(x)| <= 1` for all `x` in `[-1,1]`. For a full
square singular-value decomposition `B = L Sigma V†`, define the target

```text
T_p(B) = L p(Sigma) V†    when d is odd,
T_p(B) = V p(Sigma) V†    when d is even.
```

The even case acts in the right singular space, including the entire kernel
with value `p(0)`. The odd polynomial has `p(0)=0`, so arbitrary choices of
null singular vectors do not change its target. Neither case is generally
the matrix polynomial `p(B)`. The transformation applies to `A/alpha`, not
to `A` without normalization. A degree-zero constant is deferred to a
separately specified direct construction rather than an unchecked empty loop.

The mathematical convention is Gilyén, Su, Low, and Wiebe's
[Definition 15, Eq. (31); Theorem 17, Eq. (32); and Corollary 18, Eq. (33)](https://arxiv.org/pdf/1806.01838).
The real-polynomial construction uses a selector that combines two opposite
phase lists. Omitting that selector would require a stronger complex-polynomial
admissibility contract, not merely boundedness and parity of a real polynomial.

## 2. Phase planning and the exact sequence convention

Define the scalar reference matrices

```text
R(x) = [[x, sqrt(1-x^2)], [sqrt(1-x^2), -x]],
D(phi) = diag(exp(i phi), exp(-i phi)),
F_Phi(x) = <0| (D(phi_1) R(x)) ... (D(phi_d) R(x)) |0>.
```

A phase plan must certify `Re F_Phi(x) = p(x)` for all `x in [-1,1]`, or
provide an explicitly quantified uniform error `epsilon_synth` in this
same convention. The product is written with increasing indices from left
to right; the rightmost factor acts first. The plan records one-based
mathematical angles `(phi_1,...,phi_d)` in a zero-based vector `phi[0..d)`.
A floating-point list from an optimizer, a plot, or agreement on sampled
points is not a certificate for the entire interval.

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

The synthesis algorithm, numerical representation, termination budget,
interval proof method, and certificate format are unresolved requirements.
This host body names those obligations explicitly; it does not conceal the
quantum algorithm in a synthesis call. Only a verified plan is eligible to
become static circuit data. Failure to synthesize or verify returns an error
before execution. `tolerance=0` requires exact evidence; a requested positive
tolerance does not relax unitarity or cleanup rules.

For a sign `s` in `{0,1}`, use the projected phase
`R_Pi((-1)^s phi) = exp(i (-1)^s phi (2Pi-I))`.
For `s=0`, the circuit below realizes, respectively,

```text
d odd:  U_Phi = R_Pi(phi_1) U R_Pi(phi_2) U† ... R_Pi(phi_d) U,
d even: U_Phi = R_Pi(phi_1) U† R_Pi(phi_2) U ... R_Pi(phi_d) U.
```

For `s=1` it realizes `U_(-Phi)`. The displayed parity, the first chronological
call `U`, and the reversed traversal of the phase vector are deliberate.
For example, `d=2` means chronological `U; R_Pi(phi_2); U†; R_Pi(phi_1)`.

A concrete scalar review fixture is `U_x=R(x)` and `Pi=|0><0|`.
For `d=1`, `Phi=(0)` has successful block `x`. For `d=3`,
`Phi=(pi,pi/2,pi/2)` gives `U_Phi=U_x Z U_x Z U_x`, whose top-left
entry is `4x^3-3x`; the opposite phase list gives the same real entry.
These identities expose the ordering and phase convention for a later
independent check. They are mathematical fixtures, not Qleisli executions.
Away from inputs with unit success probability, the complementary block
still carries amplitude and the encoding ancilla cannot be purely released.

## 3. Visible alternating body and observation

`zero_projector_phase<a>(theta)` is a proposed static operation on the
ancilla register, `exp(i theta (2|0^a><0^a|-I))`. It leaves every ancilla
basis label unchanged. Its controlled use below has the exact branch phases
shown, with no discarded global-phase offset. `qif` here accepts static
operation descriptions, unlike the current fixed-name form.

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

The extra selector requires controlled **phase** access. `U` and `U†` act
identically on both selector branches, so this construction does not assume
controlled access to `U`. A future QPE around this entire dilation would
require additional access and a separately specified unitary input interface.

## 4. Complete instrument, references, and cleanup

Before initialization, the unitary part on the selector and block register is

```text
V_Phi = (H tensor I)
        (|0><0| tensor U_Phi + |1><1| tensor U_(-Phi))
        (H tensor I).
```

For output selector `s` and measured encoding ancilla label `b`, define an
operator on the data space by

```text
K_(s,b) = (<s| tensor <b| tensor I_data)
          V_Phi (|0> tensor E).
```

For arbitrary data/reference state `rho_DR`, the unnormalized output branch
is `(K_(s,b) tensor I_R) rho_DR (K_(s,b)† tensor I_R)`.
The branch probability is its trace. Completeness of the measurement and
unitarity of `V_Phi` give `sum_(s,b) K_(s,b)† K_(s,b) = I_data`.
Thus failure is a real output branch, not an omitted normalization factor.

With exact encoding and exact phase evidence, the successful branch satisfies

```text
K_(0,0^a) = T_p(B),
Pr[success | psi] = ||T_p(B)|psi>||^2.
```

For a normalized pure data input with nonzero success probability, the
conditional successful data state is `T_p(B)|psi>/||T_p(B)|psi>||`.
It is undefined if that probability is zero. This nonlinear conditional
description is not an unconditional pure API. On an entangled input, use
the branch CP map above rather than assuming an independent data vector.
Coarsening all other outcomes to `Failure` sums their CP maps, retaining the
returned data owner on every branch. The `sample` wrapper instead consumes
that data by measurement even on failure.

The allocated selector and encoding ancillas generally retain amplitudes
outside the successful subspace. They are explicitly measured and consumed;
they are **not** private workspace proven to return to zero. Even an accurate
block approximation provides no such zero-return theorem. Internal workspace
used to implement `U`, `U†`, or a projected phase has a separate exact cleanup
obligation. A possible phase implementation computes the total predicate
`is_zero:Bits<a> -> Bit`, applies its phase while preserving the tested
register's labels, and uncomputes the predicate. That local diagonal structure
can support exact cleanup evidence even for an approximated angle; the
generalized evidence rule and its implementation still need specification.

## 5. Error, success, host work, and resource accounting

An intended function `f` needs an explicitly normalized target, the same
chosen parity interpretation, and a uniform approximation bound
`sup_(x in [0,1]) |p(x)-f(x)| <= epsilon_poly`. For a bound on all allowed
inputs, this implies the corresponding singular-transform operator bound.
A smaller spectral interval requires a separately recorded input/spectrum
promise. Applications such as inversion also need a gap and scale contract;
they do not follow from the QSVT signature.

If the scalar phase certificate allows `epsilon_synth`, and the actual
implemented unitary differs from the ideal dilation by operator norm at
most `epsilon_circuit`, then the successful block differs from the target
by at most `epsilon_poly + epsilon_synth + epsilon_circuit`. This is an
unnormalized block bound, including extension by any reference identity.
For actual and target blocks that are contractions, an operator error
`epsilon` bounds their success probabilities on normalized inputs by
`2 epsilon`. Conditional normalized-state error can be much larger when
success probability is small; no uniform conditional error is claimed.

A sufficient circuit estimate, when separately justified in this exact
phase convention, is `epsilon_circuit <= d delta_U + sum_j delta_phi_j`
plus errors of other implemented gates. Here `delta_U` bounds the operator
error of each actual `U` or inverse call and `delta_phi_j` bounds each angle
error in radians. The estimate is a telescoping bound for unitary factors.
An error bound only on `E† U E` does not imply the same bound on the entire
`U`; replacing it by `d` times a block-encoding error is not justified here.
Robustness for inexact block encodings remains an extension obligation.

The circuit makes exactly `d` signal calls: `ceil(d/2)` to `U` and
`floor(d/2)` to `U†`, and `d` signed projector phases. It has `n+a+1`
logical wires plus provider workspace, two selector Hadamards, and
`a+1` measurements for `observe` (another `n` for `sample`). Computing a
zero predicate or synthesizing its controlled phase has nonzero cost.
Finite elaboration requires `O(d)` sequence records before provider expansion;
no bound on classical phase-synthesis cost is adopted without an algorithm
and accuracy representation. Input preparation, loading `A`, proving its
encoding, phase planning, and gate synthesis are separate costs.

The success probability is input dependent and may be zero. Repetition is
allowed only from a fresh preparation capability for the required input
state; the caller cannot retry by copying its unknown consumed input.
No finite expected retry count or amplitude-amplification improvement is
claimed without an additional nonzero success lower bound and access proof.

## 6. Proposed facilities and intended acceptance boundaries

All entries are **proposed, unimplemented**. Their IDs can be mapped to the
shared requirements without adding these APIs to the current stdlib ledger.

| ID / facility / classification | Types, ownership, effect, and intended IR route | Intended acceptance and rejection |
| --- | --- | --- |
| QSVT-1: sized registers, operation/plan parameters and finite fold; language forms | Static `UnitaryOp<(Bits<a>,Bits<n>)>` and checked `VerifiedPhasePlan<d>`; each application consumes/returns the complete owner. Carry retains selector and block. Specialize checked finite operations, bounds, and axis layouts. | Accept finite positive `d`, a phase vector of length `d`, and no captured live owners. Reject parity/length mismatch, duplicate selector/target ownership, omission of carried data, or a zero-degree plan under this body. |
| QSVT-2: exact block encoding; unresolved evidence schema, supplied by an ordinary implementation | `U:Q<(Bits<a>,Bits<n>)> -> Q<(Bits<a>,Bits<n>)>`, `Unitary`; retain `alpha`, `E`, and actual `E† U E=A/alpha` binding in independently checked IR evidence. | Accept an explicit normalized encoding and adjoint capability. Reject treating `A` as unitary, erasing its scale, or substituting a different padded/axis layout. |
| QSVT-3: phase planning and scalar verification; host-only processing, evidence schema unresolved | Total budgeted `plan_real_qsvt -> Result<PhasePlan,SynthesisError>`; no quantum owners or quantum effect. Retain coefficient/parity/bound evidence, phase convention, and verified uniform error in elaborated metadata. | Accept an independently verified exact or bounded-error plan. Reject a floating list without evidence, point-sampled agreement as an interval proof, or an optimizer failure silently treated as a circuit. |
| QSVT-4: exact projected phases; ordinary definition over an unresolved phase primitive | `zero_projector_phase:Q<Bits<a>> -> Q<Bits<a>>`, `Unitary`; `signed_projector_phase` returns selector and block. Lower exact diagonal branch phases and optional proved predicate uncomputation. Arbitrary-angle primitive/synthesis classification remains unresolved. | Accept the stated `exp(i theta(2Pi-I))` convention with both branches' phases. Reject replacing it by `exp(2i theta Pi)` while dropping the branch-dependent factor, or reversing `phi` traversal without changing evidence. |
| QSVT-5: register initialization and consuming readout; ordinary definitions over sealed primitives | Fresh zero initialization is `Iso`; `measure_bits` is `Observe`. `real_qsvt_observe` returns every residual data owner and every measured flag, with explicit complete CP outcomes in IR. | Accept failure plus its surviving data. Reject pure release of encoding ancillas, postselection without a failure result, or implicit discard of returned data. |
| QSVT-6: approximation and success contracts; unresolved evidence schema | Retain operator/scalar error metrics, intervals, probability premises, reference extension, and implementation identities alongside exact resource/cleanup evidence. | Accept unnormalized-block error with its assumptions. Reject interpreting a small leakage bound as exact zero return, treating parity-even output as left-space output, or promising normalized output accuracy without a success bound. |

## 7. Open questions and review targets

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

The draft, its input model, and its explicit unresolved obligations are
recorded. Future specification, API adoption, implementation, independent
IR verification, execution validation, and formal proof remain separate
pending stages.
