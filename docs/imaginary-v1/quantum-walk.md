# Imaginary Qleisli 1.0: a Szegedy quantum walk

Imaginary uncompiled symmetric-chain Szegedy walk sampler. It is not a classical-walk sampler, hitting-time/search result, speedup claim or current API.

## 1. Chosen task and input model

Finite 1<=N<=2^n; nonnegative row-stochastic symmetric P. Registers ordered left/right with low-weight-first labels. Pad by identity rows outside N. Coherent phase-fixed controlled-row Urow and inverse/full-space extension are supplied implementations, not free classical-sampling access. VertexPrep prepares normalized support x<N; width/ownership alone proves no support promise. [Szegedy](https://arxiv.org/abs/quant-ph/0401053) fixes reflection order.

```text
Pbar[x,y] = P[x,y]   if x < N and y < N,
            1       if x = y and x >= N,
            0       otherwise.
```

```text
Urow |x,0^n> = |x> sum_y sqrt(Pbar[x,y]) |y> = E_A |x>,
Urow = sum_x |x><x| tensor T_x,       T_x unitary.
```

## 2. Visible preparation, reflections, iteration, and observation

Static descriptions capture no owners. Split/join/swap move full interfaces without separability. Every finite fold, including steps=0, checks bodies. Fresh preparation is Iso; both consuming measurements make the sampler Observe.

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

## 3. Exact operator and outcome contracts

Execute R_A then swapped R_A, giving W=R_B R_A. Signs/output permutation matter under later control; W†=R_A R_B. Exact support and row equations make valid-label subspace invariant; all padded states retain defined meaning. Whole-space/reference evolution and complete K_xy measurement branches follow the displayed equations. Hide a label only by summing measured branches or explicit discard. Neither live edge register is clean on arbitrary walk states; provider scratch has a separate exact factorization.

```text
Pi_A = E_A E_A† = Urow Pi0 Urow†,
Pi_B = S Pi_A S,
R_A = 2 Pi_A - I = Urow (2 Pi0 - I) Urow†,
R_B = S R_A S,
W = R_B R_A = S R_A S R_A.
```

```text
rho_ER -> (W tensor I_R) rho_ER (W† tensor I_R).
```

```text
K_xy = (<x,y| W^t) tensor I_R,
E_xy(rho_ER) = K_xy rho_ER K_xy†,
sum_(x,y) K_xy† K_xy = I_ER.
```

## 4. Access, approximation, and cost

Each step uses two Urow, two Urow†, two zero reflections and two swaps; preparation uses VertexPrep and Urow once. Include 2n plus scratch, provider loading/synthesis/routing and generation. For justified operator error eta and preparation-vector error epsilon, t steps differ in outcome TV <=min(1, epsilon+t eta). Approximate support/leakage proves no exact cleanup, and no extra sampling success guarantee is claimed.

## 5. Proposed facilities and intended acceptance boundaries

Proposed facilities and acceptance obligations, without compiler/adoption claims.

| ID / facility / classification | Types, ownership, effect, and intended IR route | Intended acceptance and rejection |
| --- | --- | --- |
| WALK-1: sizes, static operation parameters and ownership fold; language forms | `Bits<n>`, static `UnitaryOp<A>`, finite `carry`; retain the complete ordered interface. Specialize finite bodies or retain a future checked loop representation, with explicit budgets. | Accept finite `n,t` and closed operation descriptions. Reject captured live owners, dynamic/unbounded steps in this pure fold, duplicate axes, or a body that drops part of its carried owner. |
| WALK-2: row access; ordinary implementation plus unresolved evidence schema | `Q<(Bits<n>,Bits<n>)> -> Q<(Bits<n>,Bits<n>)>`, `Unitary`; actual phase-fixed `Urow`, its adjoint, and `Urow E0 = E_A` evidence. Expand/verify the provider and retain its binding in final IR. | Accept a unitary row preparation satisfying the full padding contract. Reject a classical randomized sampler, a one-way `Iso`, or an inverse claim based only on the name `prepare`. |
| WALK-3: zero reflection and swaps; ordinary definitions | `reflect_zero_plus:Q<Bits<n>> -> Q<Bits<n>>`, `Unitary`, plus `swap_halves` above. Expand reversible total zero-testing/phase/uncomputation and complete axis permutations. `nonzero:Bits<n> -> Bit` is total and true exactly away from zero. | Accept `+1` on zero and `-1` elsewhere. Reject the opposite sign as satisfying this contract, an incomplete padded table, or treating a same-width output permutation as identity. |
| WALK-4: preparation and observation; ordinary definitions over sealed primitives | `init_zero:Unit -> Q<Bits<n>>` is `Iso`; `measure_bits:Q<Bits<n>> -> CBits<n>` is `Observe`. Expand fresh initialization and consuming measurements, keeping little-endian label decoding. | Accept both output labels, or an explicit observation/discard of an unused label. Reject reuse of measured ownership or omission of the right register at function exit. |
| WALK-5: support and accuracy evidence; unresolved evidence schema | Record `N`, exact row/support equations, implementation identity, reference extension, and optional operator-norm bounds independently of ownership. Verify at the source/IR boundary; bounds must name the actual operator. | Accept a valid-domain preparation with a full-space step. Reject inferring coherent access from probabilities, treating approximate support as exact cleanup, or inferring a search speedup from `P=P^T`. |

## 6. Open questions and review targets

Open review items below remain pending. Nonsymmetric/time-reversal, marked-set detection, generic evidence and efficient access require separately selected contracts.

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
