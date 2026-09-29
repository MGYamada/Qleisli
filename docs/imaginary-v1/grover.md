# Imaginary Qleisli 1.0: Grover and amplitude amplification

Status: **initial design draft, unimplemented and noncompiling** (2026-09-27).
This original design code follows the [future-language framework](../language-evolution.md).
It is not accepted v0 syntax, a new public API, or executable v1 evidence.
The current [finite Grover example](../algorithm-routines.md#grover-オラクル反射有限反復)
remains a regression baseline. The shared iterate below is also used by the
[amplitude-estimation draft](amplitude-estimation.md).

## Algorithm body

`n >= 1` and `k >= 0` are finite static parameters. `A` is a phase-fixed
unitary description on the entire `Bits<n>` space, with apply and inverse
access; it prepares `psi = A|0^n>`. `good` is a total basis predicate
`Bits<n> -> Bit`. The proposed `BasisFn` type, static builders, and operation
closures below capture only classical/static descriptions, never live `Q`
owners. `unitary_op` denotes a proposed builder of a checked, phase-fixed
`UnitaryOp` description; its quantum body must be checked before use.

```text
// IMAGINARY QLEISLI 1.0 — DESIGN CODE, NOT CURRENT SOURCE SYNTAX

static fn phase_oracle<n>(
    static good: BasisFn<Bits<n>, Bit>
) -> UnitaryOp<Bits<n>> {
    unitary_op |q: Q<Bits<n>>| {
        with_computed(q, good) { |flag| z(flag) }
    }
}

static fn zero_reflection<n>() -> UnitaryOp<Bits<n>> {
    // +1 at zero; -1 at every other basis value.
    phase_oracle<n>(basis |x: Bits<n>| nonzero<n>(x))
}

static fn preparation_reflection<n>(
    static A: UnitaryOp<Bits<n>>
) -> UnitaryOp<Bits<n>> {
    let R0 = zero_reflection<n>();
    unitary_op |q: Q<Bits<n>>| {
        let q = adjoint(A)(q);
        let q = R0(q);
        A(q)
    }
}

static fn grover_iterate<n>(
    static A: UnitaryOp<Bits<n>>,
    static good: BasisFn<Bits<n>, Bit>
) -> UnitaryOp<Bits<n>> {
    let O = phase_oracle<n>(good);
    let R = preparation_reflection<n>(A);
    unitary_op |q: Q<Bits<n>>| {
        let q = O(q);
        R(q)
    }
}

iso fn amplify<n,k>(
    static A: UnitaryOp<Bits<n>>,
    static good: BasisFn<Bits<n>, Bit>
) -> Q<Bits<n>> {
    let G = grover_iterate<n>(A, good);
    let prepared = A(init_zero<n>());
    for static j in 0..k carry q = prepared {
        yield G(q);
    }
}

observe fn grover_sample<n,k>(
    static A: UnitaryOp<Bits<n>>,
    static good: BasisFn<Bits<n>, Bit>
) -> CBits<n> {
    let q = amplify<n,k>(A, good);
    measure_bits<n>(q)
}

// HOST PSEUDOCODE — A SEPARATE, PROPOSED EXECUTION BOUNDARY
host fn search<n,k>(A, good, attempts: UInt)
    -> Result<CBits<n>, SearchFailure> {
    for attempt in 0..attempts {
        let candidate = sample(grover_sample<n,k>(A, good))?;
        if eval_basis(good, candidate) {
            return Ok(candidate);
        }
    }
    Err(AttemptsExhausted)
}
```

For conventional Grover search over `2^n` candidates, supply a reusable
Hadamard-layer description for `A`. General amplitude amplification permits
another specified preparation unitary. The iteration count is supplied by an
explicit policy; this body does not discover a suitable `k` from an unknown
success probability. Host attempts reuse descriptions and prepare fresh states.
`sample` propagates execution failure rather than treating it as an unmarked
candidate. `AttemptsExhausted` does not assert that no marked value exists.

`nonzero<n>(x)` is the total Boolean function that is zero exactly at `0^n`.
`eval_basis` evaluates the same predicate on the measured classical bit word;
it does not inspect an unmeasured quantum register. Its source/host agreement
is a required future contract, not assumed from an identical function name.

## Meaning, ownership, and effects

The exact signs are shared with the existing standard-library plan:

```text
Pi_good = sum_{x: good(x)=1} |x><x|
O_good  = I - 2 Pi_good
R0      = 2 |0^n><0^n| - I
R_psi   = A R0 A† = 2 |psi><psi| - I
G       = R_psi O_good
amplify output = G^k A |0^n>.
```

Statements apply `O_good` first and `R_psi` second. The two reflections are
ordinary checked compositions, with exactly these operators on the entire
register space. For `0 < p < 1`, let `p = <psi|Pi_good|psi> = sin²(theta)`,
and normalize the good and bad projections to `|g>` and `|b>`. In that order,
the invariant plane has the following direct matrix calculation:

```text
|psi> = sin(theta)|g> + cos(theta)|b>
G = [[cos(2 theta), sin(2 theta)],
     [-sin(2 theta), cos(2 theta)]]
G^k|psi> = sin((2k+1)theta)|g> + cos((2k+1)theta)|b>.
```

Thus the ideal marked-outcome probability is `sin²((2k+1)theta)`, including
the endpoint limits `p=0` and `p=1`. This is the amplitude-amplification
construction of Brassard, Hoyer, Mosca, and Tapp, with its leading minus sign
absorbed into our positive preparation reflection.
[Primary reference, Section 2](https://arxiv.org/pdf/quant-ph/0005055).
The equal-superposition specialization is
[Grover's original search algorithm](https://arxiv.org/abs/quant-ph/9605043).

`phase_oracle`, `preparation_reflection`, and `grover_iterate` build static
descriptions; their applications have effect `Unitary` and type
`Q<Bits<n>> -> Q<Bits<n>>`. Every input owner is consumed once and its successor
is returned. `amplify` has effect `Iso`, creates one data register, and returns
it. `grover_sample` has effect `Observe` and consumes that register completely.
There is no surviving quantum output in the host workflow. A caller that uses
`amplify` alone must subsequently use, return, measure, or explicitly
`discard(q)` with effect `Observe`; it cannot abandon the returned owner.

The phase oracle's private flag uses reversible XOR computation `C_good`,
followed by Z and the inverse computation. Its pure release requires the exact
equation, for arbitrary data and arbitrary reference `R`,

```text
E0 : H(D) -> H(D) tensor H(Bit),   E0|x> = |x,0>
C_good† (I_D tensor Z) C_good E0 = E0 O_good
```

Tensor this entire map equality with `I_R`, giving the explicit output order
data, flag, reference; implementations must preserve that order or certify
their corresponding permutation. Any additional synthesis scratch has the same
zero-and-separation obligation. A lexical `with_computed` scope, a borrowed
lifetime, or a numerical near-zero flag is insufficient. Retain the original
implementation and checked meaning through final IR, including control used
by amplitude estimation. An `Iso` initializer cannot replace invertible `A`.

For a general input state `rho_DR`, the sample portion after an existing
register has Kraus operators `K_x = <x| G^k` on D, extended by identity on R.
The closed trial first prepares `A|0^n>`. Classical validation merely labels
each complete outcome as marked or unmarked; it does not remove probability
mass. All repeated trials, including failure and exhaustion, remain visible.

## Accuracy, assumptions, and costs

The displayed law assumes exact preparation, oracle, reflection, and execution.
An iteration policy must state the information used to select `k`; repeated
amplification can overshoot, and more iterations need not improve success.
For independent ideal trials with fixed success `s`, the probability of
exhausting `b` attempts is `(1-s)^b`. This statement needs fresh identical
preparations and the specified sampler; it is not a hardware guarantee.

One trial uses `k` oracle applications, `k` applications each of `A†` and `R0`,
and `k+1` applications of `A`, followed by n-bit measurement. The shown oracle
implementation computes and uncomputes its predicate once per application;
predicate and zero-test synthesis costs remain explicit. Host validation costs
one predicate evaluation per successful execution. Static expansion may grow
with `k` and circuit size; shared IR is an unresolved implementation option.
No whole-space truth table or precomputed marked answer is assumed efficient.

Approximate realizations require additional phase-sensitive operator/channel
error contracts and a separate success analysis. They never weaken exact
private-scratch cleanup. A predicate check guarantees that a returned candidate
is marked only when its classical evaluation implements the same total `good`.

## Proposed facilities and acceptance records

All entries are **proposals**, with no generalized implementation or compiler
acceptance tests.

| ID / facility | Classification and intended type/effect | Acceptance / rejection and proposed IR responsibility |
| --- | --- | --- |
| GR-1 sized predicate and static builders | Language-form candidates: `BasisFn<Bits<n>,Bit>`, `static fn`, basis/unitary closures and static parameters. No runtime quantum capture. | Accept total predicates and finite descriptions; reject nontermination or captured live owners. Resolve dependencies and types before lowering. Closure grammar and capability representation remain unresolved. |
| GR-2 `phase_oracle`, `zero_reflection` | Ordinary-definition candidates: builder to `UnitaryOp<Bits<n>>`; applications are `Unitary`. `nonzero` is an ordinary total basis definition. | Accept exact computed-flag cleanup; reject a flag modified without a valid inverse/meaning certificate. Generalize checked computed regions with all axes and actual body retained. |
| GR-3 `preparation_reflection`, `grover_iterate` | Ordinary-definition candidates with A apply/inverse access. Controlled use additionally needs justified phase-fixed control access. | Accept full-space unitary A and the positive R0 convention; reject reversing an initializer or replacing G by −G under control. Compose independent evidence through inverse and final IR. |
| GR-4 `amplify`, `grover_sample`, register helpers | Ordinary-definition candidates; `amplify: () -> Q<Bits<n>>` is `Iso`; sampling returns `CBits<n>` with `Observe`. `init_zero`/`measure_bits` derive from sealed single-bit primitives. | Accept each owner exactly once; reject implicit disposal or a measurement inside a unitary. Fold/group resource creation and consuming measurements with fixed bit order. |
| GR-5 static carry loop | Language-form candidate; carry `Q<Bits<n>>` through a finite same-interface body. | Accept k=0 with body checking and identity ownership transfer; reject duplicate owners or unchecked zero-iteration bodies. Enforce generation budgets and reverify generated IR. |
| GR-6 host search and `eval_basis` | Host-only proposal; `sample` returns classical execution results, predicate evaluation returns Boolean, search returns candidate or failure. | Accept fresh attempts, exact classical validation and explicit exhaustion; reject simulator-distribution access, unvalidated candidates, or treating failure as proof of absence. Host ABI and predicate-artifact binding are unresolved. |

Useful review cases are k=0, empty/all-marked predicates, all single marked
values at small n, nonuniform A, overshooting k, exact inverse/control with a
reference, and zero attempts. A controlled comparison must distinguish G from
−G even though isolated basis-output probabilities can coincide. These are
planned checks, not results from running this imaginary code.

Open work includes operation capabilities and evidence schemas, scalable
predicate/reflection construction, runtime choice versus static specialization
of k, host execution semantics, and supported sizes and budgets. The ordinary
definitions should undergo the [standard adoption process](../stdlib-roadmap.md#5-標準への採用とaiからの還流)
only after real multi-context implementation and verification. This draft adds
no current compiler guarantee or proof of general implementation correctness.
