# Imaginary Qleisli 1.0: a Szegedy quantum walk

Status: **initial design draft; uncompiled imaginary code** (2026-09-27).
No syntax, operation parameter, sized type, or API introduced here belongs to
the current language. This draft uses the [shared future notation](../language-evolution.md)
and preserves the current [ownership and effect constraints](../language-spec.md).
It supplies a walk body and requirements for the pre-0.2.0 design corpus;
it is not an implementation, a compiler test, or a speedup claim.

## 1. Chosen task and input model

The task is to sample the two vertex labels after a specified finite number
of steps of a **two-reflection Szegedy walk for a symmetric stochastic matrix**.
It is a baseline on which a later marked-set detection or spectral algorithm
could be built. Sampling this walk is not itself a claim to solve a hitting-time
problem or to sample the classical distribution after the same number of steps.

Let `1 <= N <= 2^n`, with finite static `n`, and let `P` be an `N x N` real
matrix with nonnegative entries, each row summing to one, and `P = P^T`.
The two registers have basis `Bits<n>` in the order `(left, right)`; bit `k`
has weight `2^k`. Define the transition on the entire register alphabet by

```text
Pbar[x,y] = P[x,y]   if x < N and y < N,
            1       if x = y and x >= N,
            0       otherwise.
```

The required access is a phase-fixed unitary `Urow` on both registers,
including a unitary extension outside the zero-input subspace, with

```text
Urow |x,0^n> = |x> sum_y sqrt(Pbar[x,y]) |y> = E_A |x>,
Urow = sum_x |x><x| tensor T_x,       T_x unitary.
```

The amplitudes in this equation are the nonnegative square roots with exactly
the stated phase. Classical sampling access to a row does not provide this
coherent operation, its inverse, or an efficient circuit. The provider must
supply an implementation and its access/cost contract. A `VertexPrep` unitary
on `Bits<n>` prepares `sum_(x<N) beta_x |x>` from zero, with
`sum_x |beta_x|^2 = 1`. The initial edge state is `E_A sum_x beta_x |x>`.
The entry support is a semantic premise, not something inferred from the
register width or from separate ownership of its components.

This specialization follows the reflection order in Szegedy's
[Definition 1, Sections 3 and 6](https://arxiv.org/pdf/quant-ph/0401053):
the first row-subspace reflection is followed by the swapped-subspace
reflection. The code and the padding, ownership, and observation contracts
below are this project's design, not source code supplied by that paper.

## 2. Visible preparation, reflections, iteration, and observation

`UnitaryOp` parameters are static descriptions without captured live quantum
owners. `split` and `join` below explicitly move between one product owner and
its component owners; they do not create aliases or assert separability.
`reflect_zero_plus<n>` means `2|0^n><0^n| - I`, including its sign.

```text
// IMAGINARY QLEISLI 1.0 — does not compile in v0.1.2.
// Ordinary definitions parameterized at elaboration time.

unitary fn reflect_row[static n,
    static Urow: UnitaryOp<(Bits<n>, Bits<n>)>]
    (edge: Q<(Bits<n>, Bits<n>)>) -> Q<(Bits<n>, Bits<n>)> {
    let edge = adjoint(Urow)(edge);
    let (left, right) = split(edge);
    let right = reflect_zero_plus<n>(right);
    Urow(join(left, right))
}

unitary fn swap_halves[static n]
    (edge: Q<(Bits<n>, Bits<n>)>) -> Q<(Bits<n>, Bits<n>)> {
    let (left, right) = split(edge);
    join(right, left)
}

unitary fn walk_step[static n,
    static Urow: UnitaryOp<(Bits<n>, Bits<n>)>]
    (edge: Q<(Bits<n>, Bits<n>)>) -> Q<(Bits<n>, Bits<n>)> {
    let edge = reflect_row[n, Urow](edge);  // R_A
    let edge = swap_halves[n](edge);       // S
    let edge = reflect_row[n, Urow](edge);  // R_A in swapped coordinates
    swap_halves[n](edge)                   // S: together R_B R_A
}

iso fn prepare_edge[static n,
    static VertexPrep: UnitaryOp<Bits<n>>,
    static Urow: UnitaryOp<(Bits<n>, Bits<n>)>]()
    -> Q<(Bits<n>, Bits<n>)> {
    let left = VertexPrep(init_zero<n>());
    let right = init_zero<n>();
    Urow(join(left, right))
}

observe fn sample_walk[static n, static steps,
    static VertexPrep: UnitaryOp<Bits<n>>,
    static Urow: UnitaryOp<(Bits<n>, Bits<n>)>]()
    -> (CBits<n>, CBits<n>) {
    let edge = prepare_edge[n, VertexPrep, Urow]();
    let edge = for static k in 0..steps carry current = edge {
        yield walk_step[n, Urow](current);
    };
    let (left, right) = split(edge);
    let x = measure_bits(left);
    let y = measure_bits(right);
    (x, y)
}
```

`steps` is a finite static natural; zero steps still require all operation
bodies and contracts to be checked. `init_zero<n>` and `measure_bits` are
proposed ordinary register definitions over fresh preparation and consuming
single-bit measurement. `CBits<n>` is the proposed classical measured bit
vector; `Bits<n>` is a basis type and `Q<Bits<n>>` denotes ownership.
Their detailed future typing rules remain a specification question.

## 3. Exact operator and outcome contracts

Let `Pi0 = I_left tensor |0^n><0^n|_right`, let `S|x,y> = |y,x>`, and set

```text
Pi_A = E_A E_A† = Urow Pi0 Urow†,
Pi_B = S Pi_A S,
R_A = 2 Pi_A - I = Urow (2 Pi0 - I) Urow†,
R_B = S R_A S,
W = R_B R_A = S R_A S R_A.
```

Statements execute top to bottom, so `walk_step` has exactly this operator
order. Since both projectors are orthogonal, each reflection is a unitary
involution and `W† = R_A R_B`. Returning registers in swapped order is part
of the operator; a later inverse or coherent control must retain that
permutation. Replacing one reflection by its negative changes `W` to `-W`
and changes a later controlled walk. This draft fixes both signs even though
this closed sampling experiment cannot observe the global sign alone.

The formulas define the action on **all** `2^(2n)` basis states, including
padded labels. They do not make unspecified states disappear. The span of
`|x,y>` with `x,y<N` is invariant under both reflections: padded row states
are orthogonal to it, and each valid row state lies in it. It follows that
the specified preparation produces no padded-label outcomes. This conclusion
requires the exact support and row-preparation equations. It is not implied
by the source signature.

For an arbitrary edge density operator `rho_ER`, including entanglement with
a reference `R`, the step contract is

```text
rho_ER -> (W tensor I_R) rho_ER (W† tensor I_R).
```

Here the pure meaning-contract embeddings are identities on the entire edge
register. For preparation, the isometric embedding is `E_A`; its specified
zero-input equation must be bound to the actual `Urow`. After `t` steps and
measurement of both labels, the unnormalized reference output for `(x,y)` is

```text
K_xy = (<x,y| W^t) tensor I_R,
E_xy(rho_ER) = K_xy rho_ER K_xy†,
sum_(x,y) K_xy† K_xy = I_ER.
```

For the closed preparation, the reported probability is
`|<x,y| W^t E_A sum_z beta_z|z>|^2`. If only the left label is reported,
the right label is hidden by summing its CP branches; it must still be measured
or explicitly discarded. A caller may classify `x` using a total classical
predicate, but that does not add a marked-set detection guarantee.

The two edge registers are live data throughout. In particular, applying
`Urow†` inside a reflection does **not** show that the right register becomes
zero on arbitrary walk states. No edge owner is purely released. Any private
workspace in `T_x`, `VertexPrep`, or a zero-reflection implementation needs its
own exact factorization with zero output for every admitted input and reference.
The final two measurements are `Observe`, consuming all edge ownership.

## 4. Access, approximation, and cost

One step uses two `Urow` calls, two `Urow†` calls, two zero reflections, and
two swaps of `n`-bit halves. Preparation adds one `VertexPrep` and one `Urow`.
Thus `t` steps use `2t+1` forward row calls and `2t` inverse calls, followed
by `2n` measurements. The abstract logical width is `2n`, plus the separately
declared workspace of the providers. Swaps can become wire permutations in
IR; physical routing cost is backend dependent and must not be called zero
merely because the source uses `join` in a different order.

Circuit generation must account for the finite fold and provider expansion.
Neither an arbitrary dense `P` nor its square roots have a free preparation
algorithm. Classical storage, loading, amplitude synthesis, and gate precision
are provider costs. This draft makes no oracle separation or asymptotic
speedup claim.

The primary contract is exact. For a separately justified approximate unitary
implementation with `||Wtilde-W|| <= eta` in operator norm, telescoping gives
`||Wtilde^t-W^t|| <= t eta`. If the prepared normalized state differs by at
most `epsilon_prep` in Euclidean norm, the measured distributions differ by
at most `epsilon_prep + t eta` in total variation (capped at one). Deriving
`eta` from a concrete preparation or gate compiler is a separate obligation.
Small probability on padded labels or small workspace leakage does not prove
exact support or authorize pure workspace release. This sampling task has no
additional success/failure promise; a search task would need one.

## 5. Proposed facilities and intended acceptance boundaries

All statuses in this table are **proposed, unimplemented**. These local IDs
are requirements for later language/API selection, not additions to the
current standard-library contract ledger.

| ID / facility / classification | Types, ownership, effect, and intended IR route | Intended acceptance and rejection |
| --- | --- | --- |
| WALK-1: sizes, static operation parameters and ownership fold; language forms | `Bits<n>`, static `UnitaryOp<A>`, finite `carry`; retain the complete ordered interface. Specialize finite bodies or retain a future checked loop representation, with explicit budgets. | Accept finite `n,t` and closed operation descriptions. Reject captured live owners, dynamic/unbounded steps in this pure fold, duplicate axes, or a body that drops part of its carried owner. |
| WALK-2: row access; ordinary implementation plus unresolved evidence schema | `Q<(Bits<n>,Bits<n>)> -> Q<(Bits<n>,Bits<n>)>`, `Unitary`; actual phase-fixed `Urow`, its adjoint, and `Urow E0 = E_A` evidence. Expand/verify the provider and retain its binding in final IR. | Accept a unitary row preparation satisfying the full padding contract. Reject a classical randomized sampler, a one-way `Iso`, or an inverse claim based only on the name `prepare`. |
| WALK-3: zero reflection and swaps; ordinary definitions | `reflect_zero_plus:Q<Bits<n>> -> Q<Bits<n>>`, `Unitary`, plus `swap_halves` above. Expand reversible total zero-testing/phase/uncomputation and complete axis permutations. `nonzero:Bits<n> -> Bit` is total and true exactly away from zero. | Accept `+1` on zero and `-1` elsewhere. Reject the opposite sign as satisfying this contract, an incomplete padded table, or treating a same-width output permutation as identity. |
| WALK-4: preparation and observation; ordinary definitions over sealed primitives | `init_zero:Unit -> Q<Bits<n>>` is `Iso`; `measure_bits:Q<Bits<n>> -> CBits<n>` is `Observe`. Expand fresh initialization and consuming measurements, keeping little-endian label decoding. | Accept both output labels, or an explicit observation/discard of an unused label. Reject reuse of measured ownership or omission of the right register at function exit. |
| WALK-5: support and accuracy evidence; unresolved evidence schema | Record `N`, exact row/support equations, implementation identity, reference extension, and optional operator-norm bounds independently of ownership. Verify at the source/IR boundary; bounds must name the actual operator. | Accept a valid-domain preparation with a full-space step. Reject inferring coherent access from probabilities, treating approximate support as exact cleanup, or inferring a search speedup from `P=P^T`. |

## 6. Open questions and review targets

- **WALK-O1:** Select a representation and independent checker for symbolic
  stochastic matrices, square roots, coherent row access, and valid support.
  The finite v0 contract checker does not automatically cover these objects.
- **WALK-O2:** Specify finite size/elaboration bounds and the wire-routing
  contract. The signature alone does not give efficient `Urow` synthesis.
- **WALK-O3:** A nonsymmetric chain needs a separately specified second family
  of row states or a time-reversal contract. Substituting an arbitrary chain
  while retaining this symmetric-input promise is outside this draft.
- **WALK-O4:** If a later draft adds marked-set detection, record its stationary
  state, gap, marked-weight, query-access, accuracy, and failure assumptions.
  The present sampler provides none of those performance conclusions.
- **WALK-O5:** Review at least a one-state chain, a two-state deterministic
  swap, padded labels, `t=0`, entangled input edges, and one sign-flipped
  reflection under control. These are proposed future checks, not checks
  executed by this document.

The draft body and mathematical obligations are recorded; general syntax,
API adoption, lowering, independent evidence validation, implementation,
execution tests, and formal proofs remain pending.
