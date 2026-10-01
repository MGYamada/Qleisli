# Imaginary Qleisli 1.0: Shor factoring through shared QPE

Imaginary uncompiled factoring through shared [QPE](qpe.md); fixed N=15 experiments are separate. General arithmetic, power providers and full host guarantees remain future work.

## Inputs and successful results

Exact N>=2 and finite budget B>=0; return verified nontrivial divisors or explicit exhaustion, never a primality claim. Handle even/perfect powers first. Exact integer n=ceil(log2 N), m=2n+1, M>2N² specialize the circuit; low-weight-first phase bits. No quantum owner crosses the closed host boundary.

## Full-space reversible multiplication

Total coprime modular multiplication fixes every padded label x>=N with phase +1; its inverse uses b_inv and the same padding. An inverse witness alone proves no actual circuit/cleanup. Efficient controlled arithmetic and every required binary-power identity must be independently bound; no truth-table or repeated-query scaling shortcut. Fresh target and explicit residual discard are Observe; internal scratch returns exactly zero for all inputs/references.

```text
f_(b,N)(x) = b*x mod N, if 0 <= x < N;
             x,         if N <= x < 2^n.
U_(b,N) |x> = |f_(b,N)(x)> with amplitude exactly +1.
```

```text
// IMAGINARY QLEISLI 1.0 — static design builders, not compiler APIs.
static fn modmul<n>(b: UInt, N: UInt) -> UnitaryOp<Bits<n>>
requires 1 <= b < N <= 2^n, gcd(b,N) == 1 {
    let b_inv = inverse_mod(b,N);  // exact extended-Euclid contract
    reversible_permutation(
        forward = basis |x: Bits<n>| {
            encode<n>(if decode(x) < N { b*decode(x) mod N }
                      else { decode(x) })
        },
        inverse = basis |x: Bits<n>| {
            encode<n>(if decode(x) < N { b_inv*decode(x) mod N }
                      else { decode(x) })
        },
        implementation = clean_modular_arithmetic(b,b_inv,N)
    )
}

observe fn order_sample<n,m>(static a: UInt, static N: UInt) -> CBits<m>
requires n >= 1, m >= 1, gcd(a,N) == 1, 1 < a < N, N <= 2^n {
    let static U = with_binary_powers<m>(
        modmul<n>(a,N),
        static k => modmul<n>(pow_mod(a,2^k,N),N)
    );
    let target = on_bit(init_zero<n>(), 0, X);  // |1>
    let (word, residual_target) = qpe<n,m>(U, target);
    discard(residual_target);
    word
}
```

## Classical extraction and actual sampled trials

Host pseudocode uses exact integers/no silent overflow, exact bit-length bounds and capped exponentiation for root tests. Convergents test q<N without assuming minimal order or combining samples. Propagate InvalidInput/RetryBudgetExhausted/RandomnessError/CompileError/ExecutionError/SamplingError; failed jobs close resources. Uniform inclusive random bases and fresh single draws need their declared execution contract, not full simulator distributions.

```text
// IMAGINARY QLEISLI 1.0 — classical host procedures.
host fn gcd(u: UInt, v: UInt) -> UInt {
    while v != 0 { (u,v) = (v,u mod v); }
    u
}

host fn pow_mod(a: UInt, e: UInt, N: UInt) -> UInt requires N >= 2 {
    let result = 1;
    let base = a mod N;
    while e > 0 {
        if e mod 2 == 1 { result = (result*base) mod N; }
        base = (base*base) mod N;
        e = e div 2;
    }
    result
}

host fn convergent_denominators(y: UInt, M: UInt, N: UInt) -> List<UInt> {
    let (num,den) = (y,M);
    let (q_older,q_old) = (1,0);
    let candidates = [];
    while den != 0 {
        let a = num div den;
        let q = a*q_old + q_older;
        if q >= N { break; }
        if q > 0 { candidates.push(q); }
        (q_older,q_old) = (q_old,q);
        (num,den) = (den,num mod den);
    }
    candidates
}

host fn factor_candidate(a: UInt, N: UInt, q: UInt)
    -> Option<(UInt,UInt)> {
    if q == 0 or q mod 2 == 1 { return None; }
    if pow_mod(a,q,N) != 1 { return None; }
    let z = pow_mod(a,q div 2,N);
    if z == 1 or z == N-1 { return None; }
    for value in [z-1,z+1] {
        let d = gcd(value,N);
        if 1 < d < N and N mod d == 0 {
            return Some((d,N div d));
        }
    }
    None
}
```

```text
// IMAGINARY QLEISLI 1.0 — exact bounded preprocessing.
host fn perfect_power_divisor(N: UInt) -> Option<UInt> {
    for e in 2..=floor(log2(N)) {
        let (lo,hi) = (1,N);
        while lo+1 < hi {
            let mid = (lo+hi) div 2;
            if pow_capped(mid,e,N) <= N { lo = mid; }
            else { hi = mid; }
        }
        if lo > 1 and pow_capped(lo,e,N) == N { return Some(lo); }
    }
    None
}

host fn shor_factor(N: UInt, budget: UInt)
    -> Result<(UInt,UInt), FactorFailure> {
    if N < 2 { return Error(InvalidInput); }
    if N < 4 { return Error(RetryBudgetExhausted); }
    if N mod 2 == 0 { return Ok((2,N div 2)); }
    if let Some(b) = perfect_power_divisor(N) {
        return Ok((b,N div b));
    }
    let n = ceil(log2(N));
    let m = 2*n+1;
    for attempt in 0..budget {
        let a = uniform_integer(2,N-2)?;
        let g = gcd(a,N);
        if g > 1 { return Ok((g,N div g)); }
        let job = specialize(order_sample<n,m>, a=a, N=N)?;
        let word = run_sample(job)?;  // one draw, not the whole distribution
        let y = decode_word(word);
        for q in convergent_denominators(y,2^m,N) {
            if let Some(pair) = factor_candidate(a,N,q) {
                return Ok(pair);
            }
        }
    }
    Error(RetryBudgetExhausted)
}
```

## Mathematical contract and failure events

QPE on |1> mixes orbit eigenphases with the displayed distribution. On nearest-grid and gcd(s, r)=1, error <1/(2r²) yields the order as a convergent. Positive checked periods need not be minimal; factor checks remain exact. Odd/trivial-half-power/bad-convergent events retry. Conditional usable-base success >=(4/pi²)phi(r)/r is not a global p(N) or budget guarantee; independent attempts with success p exhaust with (1-p)^B. [Shor](https://arxiv.org/abs/quant-ph/9508027) is the primary reduction.

```text
|psi_s> = (1/sqrt(r)) sum_(j=0)^(r-1) exp(-2 pi i s*j/r) |a^j mod N>.
U_(a,N) |psi_s> = exp(+2 pi i s/r) |psi_s>.
|1> = (1/sqrt(r)) sum_(s=0)^(r-1) |psi_s>.
P(Y=y) = (1/r) sum_(s=0)^(r-1) |D_M(s/r-y/M)|^2.
```

## Proposed facilities and evidence boundary

All facilities are proposed, not adopted because a finite multiplier exists. Actual phase/axes/source/provider identity and full-space clean arithmetic need retained evidence.

| Local requirement | Classification and intended interface | Acceptance / rejection and proposed IR route |
| --- | --- | --- |
| SHOR-MUL | `modmul<n>(b,N): UnitaryOp<Bits<n>>`: proposed ordinary static builder; arithmetic synthesis/evidence classification unresolved. Basis maps are total `Bits<n> -> Bits<n>`. | Accept coprime b with inverse witness and an actual phase-fixed clean implementation; reject noncoprime b, an undefined out-of-range action, or x=N mapping to 0. Retain full-space semantic and scratch-return evidence in final IR. |
| SHOR-POW | `with_binary_powers`: proposed ordinary static evidence builder over the operation-access mechanism. | Accept independently checked identities for every required k and controlled implementation; reject unchecked rewrite rules or unit-cost claims for repeated black-box queries. Recheck implementation substitution under coherent control. |
| SHOR-QPE | `order_sample`: ordinary `Observe` definition composing shared QPE, fresh preparation, and explicit discard. | Accept exact width/layout agreement and consuming residual target; reject omitted disposal or a hidden success-only measurement. Lower to QPE's full instrument plus partial trace. |
| SHOR-CLASSICAL | `gcd`, `pow_mod`, convergents, floor roots, perfect-power and factor checks: ordinary host algorithms with exact integer types. `inverse_mod` requires an extended-Euclid witness `b*b_inv mod N=1`. | Accept bounded loops, exact arithmetic and verified factors; reject overflow, floating-point reconstruction, or treating an unchecked denominator as the order. Classical trace/result contracts remain distinct from quantum IR evidence. |
| SHOR-SAMPLE | `specialize`, `run_sample`, `uniform_integer`, host loops/results: host-only processing; their language/runtime classification is unresolved. | Accept one actual sample per fresh invocation, a finite retry budget, and explicit host-error propagation; reject enumerating all branches as sampled trials or silently conditioning on success. Bind jobs to their checked source/IR and record sampling assumptions. |

## Costs, review cases, and unresolved work

One attempt uses m+n+W_mul peak data/workspace, m controlled multipliers, O(m²) Fourier work, m measurements and discard; cost O(m C_mul+m²) excludes separate routing/synthesis/host generation and at most B trials. Review N=15/a=2, off-grid N=21, padded x, N=9, prime and zero budget. Efficient clean synthesis, provider binding, approximation, host limits/sampling and multi-sample confidence remain open.
