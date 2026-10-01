# Imaginary Qleisli 1.0: quantum phase estimation

Imaginary design, not accepted syntax or a generalized implementation. Existing [finite QPE](../static-operations.md) and [bounded sized pipeline](../sized-corpus-source.md) are separate. CBits is copyable measured data; capabilities and evidence do not follow from a type name.

## Interface and conventions

Finite n, m>=1, M=2^m; bit k has weight 2^k. The phase-fixed U captures no owners and provides controlled binary powers. U|psi>=exp(+2pi i phi)|psi>, phi in [0, 1). Use positive Fourier including final reversal and apply its inverse. Eigenstate is an accuracy premise, not an ownership requirement; the full instrument accepts correlated general inputs.

```text
observe fn qpe<n,m>(static U: UnitaryOp<Bits<n>>,
                    target: Q<Bits<n>>) -> (CBits<m>, Q<Bits<n>>)
```

```text
F_M |j> = (1/sqrt(M)) sum_(y=0)^(M-1) exp(+2 pi i j*y/M) |y>.
```

## Visible algorithm and ownership routing

Take/put moves the complete owner, returns the increasing-order remainder and reinserts at k. Q<Unit> remains owned for m=1. Distinct axes, complete remainder/target and reversal must survive IR/measurement. Proposed folds check even zero bodies; symbolic dyadic rotations require a separate supported realization contract.

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

```text
sum_(z=0)^(M-1) |z><z|_phase tensor U^(z[k])_target,
```

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

## Mathematical instrument and accuracy

Fourier orthogonality gives sum K_y†K_y=I. Conditional output normalizes only for p_y>0; general targets/references change by the actual branch. Eigenphase probabilities are |D_M(phi-y/M)|²; exact-grid results are deterministic, nearest circular error <=1/(2M) has probability >=4/pi². This is single-shot, not configurable confidence. A justified complete-isometry operator error eta gives joint trace distance/total variation <=min(1, eta). [Primary construction](https://arxiv.org/abs/quant-ph/9708016) fixes conventions.

```text
|psi> -> sum_(y=0)^(M-1) |y> tensor K_y |psi>,
K_y = (1/M) sum_(j=0)^(M-1) exp(-2 pi i j*y/M) U^j.
```

```text
E_y(rho_TR) = (K_y tensor I_R) rho_TR (K_y† tensor I_R).
p_y = trace(E_y(rho_TR)).
```

## Capabilities, effects, and implementation obligations

Initialization Iso, coherent steps Unitary, readout Observe consumes phase and returns target. Every hidden workspace needs exact phase/order/reference zero factorization; approximation never permits release. The table records proposed responsibilities, not compiler acceptance.

```text
W (|psi> tensor |0_work>) = (U_logical |psi>) tensor |0_work>
```

| Local requirement | Classification and intended interface | Acceptance / rejection and proposed IR route |
| --- | --- | --- |
| QPE-SIZE | `Bits<n>`, `CBits<m>`, static naturals/folds: proposed language forms; quantum values remain linear, classical words copyable. | Accept finite checked dimensions and complete carried ownership; reject unknown static bounds or silently truncated dimensions. Elaborate to explicit ordered interfaces, with checked expansion/sharing limits. |
| QPE-ACCESS | `UnitaryOp<A>`, `ControlledBinaryPowers(U,m)`, `power`, `adjoint`, `controlled`: classification unresolved between language forms and static evidence builders. | Accept evidence tied to phase-fixed actual implementations; reject a bare black-box `U` without controlled access or a descriptor capturing a live owner. Retain implementation bindings and transformation evidence through final IR. |
| QPE-AXIS | `take_bit/put_bit`, `on_bit`, `swap_axes`: proposed language forms for ownership routing; `controlled_on_bit` is an ordinary definition. | Accept distinct axes and return the complete remainder; reject aliases, out-of-range indices, or changed order. Lower to explicit axis permutations and controlled actions, rechecked independently. |
| QPE-FOURIER | `qft` and `controlled_phase_pair`: proposed ordinary definitions over a phase-rotation capability whose primitive/synthesis classification is unresolved. | Accept the positive Fourier matrix with explicit reversal; reject dropping reversal or using a negative transform under the same contract. Exact or approximate evidence must name its ring/metric and actual circuit. |
| QPE-OBSERVE | `init_zero` and `measure_bits`: proposed ordinary folds of initialization and consuming Z measurement; `qpe` is an ordinary `Observe` definition. | Accept general correlated inputs and return the residual owner; reject use in a unitary caller or target loss. Lower to fresh initialization, coherent actions, measurements, and the complete instrument interface. |
| QPE-DECODE | `decode_word: CBits<m> -> UInt`: proposed ordinary classical definition, exact and total by the weighted-bit sum. | Accept every word; reject a mismatched width/serialization convention. Preserve the word-to-integer layout at the host boundary. |

## Costs, review cases, and unresolved work

Costs: m+n data plus scratch, m binary powers and measurements, 2m Hadamards, m(m-1)/2 phases and floor(m/2) swaps. Elementary controlled U gives 2^m-1 uses; efficient power providers are separate. Review off-grid phases, entangled target, empty remainder, reversed bits and controlled scalar -1. Generic routing, capabilities, domain/synthesis, instrument preservation and host confidence/ABI remain open.
