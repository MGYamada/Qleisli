# Imaginary Qleisli 1.0: quantum phase estimation

Status: **initial design draft; not accepted `.qli`, not compiled or executed**
(2026-09-27). This is an original Qleisli design exercise under the
[language evolution framework](../language-evolution.md), not a new public API.
The existing fixed-width [QPE and static-operation contracts](../static-operations.md)
remain the implemented regression baseline. General source and IR rules, their
implementation, and implementation soundness proofs remain separate work.

The user selected the spelling `CBits<m>` on 2026-09-28; the earlier
`CWord<m>` spelling remains only in preserved first-attempt records. This
is still design notation until its source extension is implemented.

## Interface and conventions

The proposed ordinary algorithm has this interface:

```text
observe fn qpe<n,m>(static U: UnitaryOp<Bits<n>>,
                    target: Q<Bits<n>>) -> (CBits<m>, Q<Bits<n>>)
```

Here `n >= 1` and `m >= 1` are finite static integers, `M = 2^m`, and bit `k`
has integer weight `2^k`. `CBits<m>` is a proposed copyable classical vector of
exactly `m` measured bits; `decode_word(y) = sum_k 2^k y[k]`. This classical
vector is not a live register. Its serialization must preserve that ordering.
`U` is a reusable static description, captures no live quantum owners, fixes
the entire operator phase, and supplies controlled binary-power access.

For an eigenvector, write `U |psi> = exp(+2 pi i phi) |psi>` with
`phi in [0,1)`. The positive Fourier convention is

```text
F_M |j> = (1/sqrt(M)) sum_(y=0)^(M-1) exp(+2 pi i j*y/M) |y>.
```

QPE applies `F_M`'s inverse. The `qft<m>` interface below includes the final
bit reversal; callers do not silently reverse a measured word. Eigenstate
input is a premise of the single-phase accuracy claim, not an ownership or
type-checking premise. General inputs, including correlations with a reference,
are accepted by the intended instrument contract.

## Visible algorithm and ownership routing

All code blocks in this draft use **imaginary, unimplemented notation**.
`for static ... carry` denotes an ordered finite fold, and `yield` returns
every carried owner. The control helper consumes the entire phase register;
it never obtains an alias while leaving a whole-register owner usable.

```text
// IMAGINARY QLEISLI 1.0 — not current source syntax.
unitary fn controlled_on_bit<n,m>(
    static U: UnitaryOp<Bits<n>>, static k: UInt,
    phase: Q<Bits<m>>, target: Q<Bits<n>>
) -> (Q<Bits<m>>, Q<Bits<n>>)
requires k < m, Controlled(U) {
    let (control, remainder) = take_bit<m,k>(phase);
    let (control, target) = controlled(U)(control, target);
    let phase = put_bit<m,k>(control, remainder);
    (phase, target)
}

observe fn qpe<n,m>(static U: UnitaryOp<Bits<n>>,
                    target: Q<Bits<n>>) -> (CBits<m>, Q<Bits<n>>)
requires n >= 1, m >= 1, ControlledBinaryPowers(U,m) {
    let phase = init_zero<m>();
    let phase = for static k in 0..m carry phase = phase {
        yield on_bit(phase, k, H);
    };
    let (phase, target) =
        for static k in 0..m carry pair = (phase, target) {
            let (phase, target) = pair;
            let static Uk = power(U, 2^k);
            yield controlled_on_bit<n,m>(Uk, k, phase, target);
        };
    let phase = adjoint(qft<m>())(phase);
    let word = measure_bits<m>(phase);
    (word, target)
}
```

`take_bit<m,k>` returns `(Q<Bit>, Q<Bits<m-1>>)`: the selected axis and all
other axes in increasing original-index order. `put_bit<m,k>` reinserts that
axis at exactly `k`. Both are proposed ownership-structure operations of effect
`Unitary`; they do not assert separability. The register with zero remaining
axes when `m=1` still has a linear owner. The helper's complete operator is

```text
sum_(z=0)^(M-1) |z><z|_phase tensor U^(z[k])_target,
```

with identity on every external reference. It returns the same ordered phase
and target interfaces. Passing overlapping owners, losing `remainder`, using
the old `phase`, or omitting the returned target is invalid.

To expose the Fourier building block as well, one possible ordinary static
definition is the following. `descending(m)` means `m-1,...,0` and is empty for
`m=0`; `controlled_phase_pair(q,j,k,theta)` returns the entire register and
acts as `diag(1,1,1,exp(i theta))` on the two designated, distinct axes.

```text
// IMAGINARY QLEISLI 1.0 — proposed ordinary operation builder.
static fn qft<m>() -> UnitaryOp<Bits<m>> {
    unitary_op |q| {
        let q = for static j in descending(m) carry q = q {
            let q = on_bit(q, j, H);
            yield for static k in descending(j) carry q = q {
                yield controlled_phase_pair(q, k, j, 2*pi / 2^(j-k+1));
            };
        };
        for static k in 0..floor(m/2) carry q = q {
            yield swap_axes(q, k, m-1-k);
        }
    }
}
```

The last swaps change the operator's output-axis convention. Their physical
cost depends on routing; even if represented as an interface permutation, the
permutation must survive later composition and measurement. Exact symbolic
dyadic phase rotations in this code are proposed capabilities. Arbitrary
precision here must not be inferred from the current H/X/Z/T gate set.

## Mathematical instrument and accuracy

Before measuring the phase register, the ideal circuit maps

```text
|psi> -> sum_(y=0)^(M-1) |y> tensor K_y |psi>,
K_y = (1/M) sum_(j=0)^(M-1) exp(-2 pi i j*y/M) U^j.
```

This is a derivation from the displayed circuit: Hadamards give the uniform
sum of `|j>`, controlled binary powers apply `U^j`, and the inverse Fourier
matrix supplies the coefficient. Orthogonality of the Fourier characters
gives `sum_y K_y† K_y = I`. For an arbitrary joint input `rho_TR`, the result
of outcome `y` is the unnormalized residual state

```text
E_y(rho_TR) = (K_y tensor I_R) rho_TR (K_y† tensor I_R).
p_y = trace(E_y(rho_TR)).
```

The return type carries the target owner for that branch. The sum of these
maps is trace preserving. On a superposition, observing `y` generally changes
the target and its reference correlations; QPE does not promise an unchanged
target or silently replace it with a classical eigenvalue label. Conditional
normalization is meaningful only for `p_y > 0`.

On a normalized eigenvector the scalar is
`D_M(phi-y/M) = (1/M) sum_j exp(2 pi i j*(phi-y/M))`. Thus the result
probability is `|D_M(phi-y/M)|^2`; if `M*phi` is integral, its corresponding
word occurs with probability one in the ideal circuit. The returned eigenstate
is unchanged up to its branch scalar. In general the nearest grid point has
circular error at most `1/(2M)` and probability at least `4/pi^2`. This is a
single-shot statement, not a configurable confidence guarantee. The Fourier
and phase-estimation construction and this bound are described in sections
4–5 of [Cleve, Ekert, Macchiavello and Mosca](https://arxiv.org/abs/quant-ph/9708016).

For later approximate synthesis, one possible contract is
`||V_impl - V_ideal||_op <= eta` for the complete premeasurement isometry.
It implies output trace distance at most `min(1,eta)` on any joint normalized
input, hence the same upper bound on the change in outcome probabilities as
total variation distance. The desired `eta`, certificate language, and gate
error allocation are unresolved. Statistical phase error, gate-synthesis error,
and exact clean-auxiliary obligations are different quantities.

## Capabilities, effects, and implementation obligations

Initialization is `Iso`, all coherent steps are `Unitary`, and measuring the
phase register makes `qpe` `Observe`. The phase bits are consumed by measurement,
not purely freed. The target must be returned. Any scratch hidden inside the
power or Fourier implementation must satisfy

```text
W (|psi> tensor |0_work>) = (U_logical |psi>) tensor |0_work>
```

for every input and reference, with exactly fixed phase and output order.
Small scratch leakage is never permission for pure release. A backend lacking
the required rotations or controlled implementation must report unsupported
capability or a separately specified approximation result.

| Local requirement | Classification and intended interface | Acceptance / rejection and proposed IR route |
| --- | --- | --- |
| QPE-SIZE | `Bits<n>`, `CBits<m>`, static naturals/folds: proposed language forms; quantum values remain linear, classical words copyable. | Accept finite checked dimensions and complete carried ownership; reject unknown static bounds or silently truncated dimensions. Elaborate to explicit ordered interfaces, with checked expansion/sharing limits. |
| QPE-ACCESS | `UnitaryOp<A>`, `ControlledBinaryPowers(U,m)`, `power`, `adjoint`, `controlled`: classification unresolved between language forms and static evidence builders. | Accept evidence tied to phase-fixed actual implementations; reject a bare black-box `U` without controlled access or a descriptor capturing a live owner. Retain implementation bindings and transformation evidence through final IR. |
| QPE-AXIS | `take_bit/put_bit`, `on_bit`, `swap_axes`: proposed language forms for ownership routing; `controlled_on_bit` is an ordinary definition. | Accept distinct axes and return the complete remainder; reject aliases, out-of-range indices, or changed order. Lower to explicit axis permutations and controlled actions, rechecked independently. |
| QPE-FOURIER | `qft` and `controlled_phase_pair`: proposed ordinary definitions over a phase-rotation capability whose primitive/synthesis classification is unresolved. | Accept the positive Fourier matrix with explicit reversal; reject dropping reversal or using a negative transform under the same contract. Exact or approximate evidence must name its ring/metric and actual circuit. |
| QPE-OBSERVE | `init_zero` and `measure_bits`: proposed ordinary folds of initialization and consuming Z measurement; `qpe` is an ordinary `Observe` definition. | Accept general correlated inputs and return the residual owner; reject use in a unitary caller or target loss. Lower to fresh initialization, coherent actions, measurements, and the complete instrument interface. |
| QPE-DECODE | `decode_word: CBits<m> -> UInt`: proposed ordinary classical definition, exact and total by the weighted-bit sum. | Accept every word; reject a mismatched width/serialization convention. Preserve the word-to-integer layout at the host boundary. |

These are requirements, not implemented acceptance/rejection tests. Every
proposed interface needs explicit current-to-future specification work before
implementation. The [shared requirements index](requirements.md) tracks overlap
with the other drafts.

## Costs, review cases, and unresolved work

QPE needs `m+n` live public qubits plus implementation scratch, `m` binary-power
calls, `m` phase measurements, `2m` Hadamards including QFT, `m(m-1)/2`
controlled phase rotations, and `floor(m/2)` Fourier swaps. If only elementary
controlled-`U` access is available, powers cost `2^m-1` such uses, not `m`.
Efficient modular powers in [Shor](shor.md) are a separate implementation
capability. Elaboration work, gate synthesis, physical routing, and sampling
cost must be reported independently.

Review targets include phases `0`, `1/2`, and non-dyadic `1/3`, a target
correlated with a reference, the `m=1` empty remainder, a deliberately reversed
measurement layout, and controlled implementations that differ by `-1`.
The latter two should fail the claimed contract rather than be hidden by an
eigenstate-only probability check. Existing fixed-size checks are regressions,
not execution of this code.
The independent [finite mathematical checks](../../scripts/check_imaginary_v1_examples.py)
exercise selected conventions and counterexamples directly; they do not parse,
compile, or execute this imaginary source.

Unresolved: static parameter inference and capacity rules; evidence for generic
axis routing; efficient access declarations; exact phase representation versus
approximate synthesis; instrument certificates retained through compilation;
host sampling and classical word ABI. Choosing a confidence-boosting QPE
variant is also future work. This draft fixes conventions and displays the
composition, but specifies no new accepted grammar and proves no compiler
adequacy theorem.
