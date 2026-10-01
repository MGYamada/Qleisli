# Imaginary Qleisli 1.0: Grover and amplitude amplification

Imaginary uncompiled design; no new syntax/API or executable v1 evidence. [Finite routines](../algorithm-routines.md) remain the regression baseline. Shared G also serves [amplitude estimation](amplitude-estimation.md).

## Algorithm body

n>=1, k>=0 static; phase-fixed whole-space unitary A has apply/inverse access and good is total. Builders capture static/classical descriptions, no live owners. Fresh attempts use an explicit k/budget; runtime errors propagate, exhaustion proves no absence. Classical eval_basis must agree with the same quantum predicate.

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

## Meaning, ownership, and effects

Execute oracle then positive preparation reflection. Good/bad-plane equations fix the scalar shared under control. Unitary applications return all owners; amplify creates Iso ownership; sampling is Observe. Exact compute/Z/uncompute cleanup extends by identity to all references and retains data/flag/reference order. Initializers cannot replace invertible A. Arbitrary-input sampling has Kraus <x|G^k and closed trials prepend preparation. [Amplification construction](https://arxiv.org/abs/quant-ph/0005055) supplies the ideal law.

```text
Pi_good = sum_{x: good(x)=1} |x><x|
O_good  = I - 2 Pi_good
R0      = 2 |0^n><0^n| - I
R_psi   = A R0 A† = 2 |psi><psi| - I
G       = R_psi O_good
amplify output = G^k A |0^n>.
```

```text
|psi> = sin(theta)|g> + cos(theta)|b>
G = [[cos(2 theta), sin(2 theta)],
     [-sin(2 theta), cos(2 theta)]]
G^k|psi> = sin((2k+1)theta)|g> + cos((2k+1)theta)|b>.
```

```text
E0 : H(D) -> H(D) tensor H(Bit),   E0|x> = |x,0>
C_good† (I_D tensor Z) C_good E0 = E0 O_good
```

## Accuracy, assumptions, and costs

Success sin²((2k+1)theta) can overshoot; independent identical trials of success s exhaust b attempts with (1-s)^b. Each trial uses k oracles/A†/R0 and k+1 A, n measurements plus predicate synthesis/validation. Count generation, provider scratch and routing separately; whole-space tables are not scalable synthesis. Approximation needs its own phase-sensitive success analysis, while scratch stays exact.

## Proposed facilities and acceptance records

Table entries are proposed obligations. Review k=0, empty/all-marked, small predicates, nonuniform A, inverse/reference/control, zero attempts and -G. Capabilities, scalable synthesis, staging, host execution and budgets remain open; multi-context evidence precedes stdlib adoption.

| ID / facility | Classification and intended type/effect | Acceptance / rejection and proposed IR responsibility |
| --- | --- | --- |
| GR-1 sized predicate and static builders | Language-form candidates: `BasisFn<Bits<n>,Bit>`, `static fn`, basis/unitary closures and static parameters. No runtime quantum capture. | Accept total predicates and finite descriptions; reject nontermination or captured live owners. Resolve dependencies and types before lowering. Closure grammar and capability representation remain unresolved. |
| GR-2 `phase_oracle`, `zero_reflection` | Ordinary-definition candidates: builder to `UnitaryOp<Bits<n>>`; applications are `Unitary`. `nonzero` is an ordinary total basis definition. | Accept exact computed-flag cleanup; reject a flag modified without a valid inverse/meaning certificate. Generalize checked computed regions with all axes and actual body retained. |
| GR-3 `preparation_reflection`, `grover_iterate` | Ordinary-definition candidates with A apply/inverse access. Controlled use additionally needs justified phase-fixed control access. | Accept full-space unitary A and the positive R0 convention; reject reversing an initializer or replacing G by −G under control. Compose independent evidence through inverse and final IR. |
| GR-4 `amplify`, `grover_sample`, register helpers | Ordinary-definition candidates; `amplify: () -> Q<Bits<n>>` is `Iso`; sampling returns `CBits<n>` with `Observe`. `init_zero`/`measure_bits` derive from sealed single-bit primitives. | Accept each owner exactly once; reject implicit disposal or a measurement inside a unitary. Fold/group resource creation and consuming measurements with fixed bit order. |
| GR-5 static carry loop | Language-form candidate; carry `Q<Bits<n>>` through a finite same-interface body. | Accept k=0 with body checking and identity ownership transfer; reject duplicate owners or unchecked zero-iteration bodies. Enforce generation budgets and reverify generated IR. |
| GR-6 host search and `eval_basis` | Host-only proposal; `sample` returns classical execution results, predicate evaluation returns Boolean, search returns candidate or failure. | Accept fresh attempts, exact classical validation and explicit exhaustion; reject simulator-distribution access, unvalidated candidates, or treating failure as proof of absence. Host ABI and predicate-artifact binding are unresolved. |
