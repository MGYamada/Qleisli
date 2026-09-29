# Imaginary Qleisli 1.0: Shor factoring through shared QPE

Status: **initial design draft; not accepted `.qli`, not compiled or executed**
(2026-09-27). This original design uses the shared [QPE draft](qpe.md) and
[language evolution framework](../language-evolution.md). It generalizes the
structure of the existing [fixed N=15 example](../arithmetic-order-finding.md)
as a proposal. General modular synthesis, host sampling, and retries remain
unimplemented; the current simulator's enumeration of a distribution is not
an execution of the host sampler proposed here.

## Inputs and successful results

The proposed host routine takes an exact integer `N >= 2` and a finite retry
budget `B >= 0`. It returns either `Factors(d, N/d)` with exact checks
`1 < d < N` and `N mod d = 0`, or `RetryBudgetExhausted`. Inputs below two
are rejected. Factors need not be prime; recursively factoring them is a
separate classical orchestration. Prime inputs can exhaust the budget; this
routine does not report exhaustion as a proof of primality. A primality
precheck may be added later as a separately contracted classical algorithm.

Even inputs and perfect powers are handled classically before the quantum
loop. For the quantum stage choose `n = ceil(log2 N)` and `m = 2n+1`, so
`M = 2^m > 2N^2`. These are host-computed integers that become static circuit
parameters at an explicit specialization boundary. Bit `k` has weight `2^k`
in both registers; the returned QPE word decodes to `y` in `[0,M)`.

## Full-space reversible multiplication

For `1 <= b < N`, `gcd(b,N)=1`, and `N <= 2^n`, define the total basis map

```text
f_(b,N)(x) = b*x mod N, if 0 <= x < N;
             x,         if N <= x < 2^n.
U_(b,N) |x> = |f_(b,N)(x)> with amplitude exactly +1.
```

The inverse on residues multiplies by the modular inverse `b_inv`; it fixes
the same out-of-range values. Since the two regions are invariant and each is
permuted bijectively, this defines a unitary on the entire register space.
Forgetting the out-of-range branch would identify `N` with `0` and invalidate
an otherwise plausible modular implementation.

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

`reversible_permutation` is an unresolved synthesis/evidence facility, not
permission to assume arbitrary efficient unitary gates. It must check the
actual implementation against the displayed total maps. Its mathematical
inverse witness is necessary but does not establish the correctness, phase,
or scratch cleanup of a supplied circuit. `clean_modular_arithmetic` names
the missing arithmetic implementation capability, not an existing function.
An efficient construction must expose its add/compare/reduce/uncompute stages
when selected for implementation; enumerating all `2^n` basis values would
not satisfy the intended polynomial-cost requirement.

The static evidence builder `with_binary_powers` supplies the family
`U_(a,N)^(2^k) = U_(a^(2^k) mod N,N)`, including exact phase and the
out-of-range identity. Repeated squaring computes each multiplier. Controlled
implementations require a clean, phase-fixed controlled arithmetic circuit;
access to uncontrolled multiplication alone is insufficient. The shared QPE
body still calls `power(U,2^k)` through this evidence-backed access family.
Only `0 <= k < m` is required by this specialization. Pure exact classical
helpers such as `pow_mod` may run during static elaboration as well as host
postprocessing; their use here does not introduce host I/O into a unitary.

`order_sample` allocates a fresh target for every invocation, consumes its
phase register through QPE's measurement, and explicitly discards the returned
target. This discard is `Observe` and means partial trace, not certified pure
cleanup. All hidden arithmetic scratch requires exact clean return for every
register input and arbitrary reference before it can be released.

## Classical extraction and actual sampled trials

The following exact arithmetic helpers show the important postprocessing
decisions. Integer arithmetic has no silent overflow. `div` is floor division;
lists and mutable classical loop variables are host-only design notation.
The `host fn` examples for `gcd` and `pow_mod` specify deterministic pure
classical algorithms; the same algorithms may be evaluated by the static
specializer on known inputs. They require no random sampling, device call, or
other host I/O. A future specification must define that staging interface.
`convergent_denominators` deliberately does not try multiples or combine
different samples. A denominator is tested as a candidate period; it is never
assumed to be the minimal order.

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

The even-perfect-power preprocessing can also be written without hiding a
factoring routine. `pow_capped(b,e,N)` means `min(b^e,N+1)` computed by repeated
squaring, capping each intermediate product at `N+1`; it is exact for every
comparison/equality used below. The binary search terminates with
`lo^e <= N < hi^e`, so `lo` is the integer floor root.

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

`FactorFailure` is the proposed tagged host error type
`InvalidInput | RetryBudgetExhausted | RandomnessError | CompileError |
ExecutionError | SamplingError`. `?` propagates each nonalgorithmic error,
preserving its diagnostic; it does not turn the error into a measured word or
silently retry it. `uniform_integer`, `specialize`, and `run_sample` return
their respective `Result` values. Runtime or device failure after allocation
must close the failed job's resources through the host/backend error contract;
the host cannot resume with a live partial quantum result.

All logarithms used to choose integer loop bounds/widths denote exact integer
bit-length calculations, not floating-point logs. The random base is sampled
uniformly from the finite inclusive range. A later sampler must either provide
that distribution with its randomness assumptions or disclose a different
policy. `run_sample` executes one newly initialized experiment and returns one
outcome. Compile, device, and transport failures are propagated as distinct
host errors rather than counted as algorithmic samples.

No quantum owner crosses this host boundary: `order_sample` has only a
classical result. A failed classical candidate therefore retains no quantum
state to reuse on the next attempt. In particular, neither the unknown target
state nor its postmeasurement residual is cloned between trials.

## Mathematical contract and failure events

Let `r` be the least positive integer satisfying `a^r mod N=1`. On the orbit
of `|1>`, define

```text
|psi_s> = (1/sqrt(r)) sum_(j=0)^(r-1) exp(-2 pi i s*j/r) |a^j mod N>.
U_(a,N) |psi_s> = exp(+2 pi i s/r) |psi_s>.
|1> = (1/sqrt(r)) sum_(s=0)^(r-1) |psi_s>.
P(Y=y) = (1/r) sum_(s=0)^(r-1) |D_M(s/r-y/M)|^2.
```

These identities follow by shifting the orbit index and using orthogonality.
They connect the actual fresh input and measurement distribution to the shared
QPE instrument; they do not require preparing a known eigenstate. Conditional
target states are generally different, and discarding them preserves the full
classical marginal rather than postselecting a successful spectral component.

On a nearest-grid event and `gcd(s,r)=1`, the reduced fraction `s/r` is a
continued-fraction convergent of `y/M`: its error is at most `1/(2M)`, strictly
below `1/(2r^2)` because `r < N` and `M > N^2`. Such a sample exposes the true
order among the candidates. The order-finding reduction, rational
reconstruction, and randomized factor extraction originate in
[Shor's factoring paper](https://arxiv.org/abs/quant-ph/9508027); the shared-QPE
organization is explained in section 6 of
[Cleve et al.](https://arxiv.org/abs/quant-ph/9708016).

When `s` and `r` share a divisor, reconstruction may give a proper divisor of
`r`, which the modular-exponentiation check rejects. An odd order, a half-power
equal to `+1` or `-1` modulo `N`, an inaccurate phase sample, or an unhelpful
convergent can require another attempt. A verified positive period need not be
minimal: the subsequent gcd and exact divisibility checks are sufficient for
the correctness of a returned pair. This avoids a circular assumption that
recovering a rational denominator already proves order finding succeeded.

For a fixed coprime base with usable even order and nontrivial half-power,
the nearest-grid/coprime-numerator event has probability at least
`(4/pi^2) * phi(r)/r` in the ideal model, where `phi` is Euler's totient.
This conditional lower bound is derived by summing QPE's per-eigenphase bound
over the `phi(r)` usable spectral labels. It is not a uniform per-base constant
or a guarantee that an arbitrary finite budget succeeds. If independent full
attempts have success probability `p`, exhausting `B` attempts has probability
`(1-p)^B`; this draft does not supply a certified global `p(N)` bound for the
selected base policy or noisy hardware. Every returned factor remains checked
by exact classical arithmetic even if phase accuracy is poor.

## Proposed facilities and evidence boundary

| Local requirement | Classification and intended interface | Acceptance / rejection and proposed IR route |
| --- | --- | --- |
| SHOR-MUL | `modmul<n>(b,N): UnitaryOp<Bits<n>>`: proposed ordinary static builder; arithmetic synthesis/evidence classification unresolved. Basis maps are total `Bits<n> -> Bits<n>`. | Accept coprime b with inverse witness and an actual phase-fixed clean implementation; reject noncoprime b, an undefined out-of-range action, or x=N mapping to 0. Retain full-space semantic and scratch-return evidence in final IR. |
| SHOR-POW | `with_binary_powers`: proposed ordinary static evidence builder over the operation-access mechanism. | Accept independently checked identities for every required k and controlled implementation; reject unchecked rewrite rules or unit-cost claims for repeated black-box queries. Recheck implementation substitution under coherent control. |
| SHOR-QPE | `order_sample`: ordinary `Observe` definition composing shared QPE, fresh preparation, and explicit discard. | Accept exact width/layout agreement and consuming residual target; reject omitted disposal or a hidden success-only measurement. Lower to QPE's full instrument plus partial trace. |
| SHOR-CLASSICAL | `gcd`, `pow_mod`, convergents, floor roots, perfect-power and factor checks: ordinary host algorithms with exact integer types. `inverse_mod` requires an extended-Euclid witness `b*b_inv mod N=1`. | Accept bounded loops, exact arithmetic and verified factors; reject overflow, floating-point reconstruction, or treating an unchecked denominator as the order. Classical trace/result contracts remain distinct from quantum IR evidence. |
| SHOR-SAMPLE | `specialize`, `run_sample`, `uniform_integer`, host loops/results: host-only processing; their language/runtime classification is unresolved. | Accept one actual sample per fresh invocation, a finite retry budget, and explicit host-error propagation; reject enumerating all branches as sampled trials or silently conditioning on success. Bind jobs to their checked source/IR and record sampling assumptions. |

The [shared requirements index](requirements.md) links these obligations to
QPE and the other drafts. New host syntax, integers, static parameters,
operation descriptors, and arithmetic synthesis are all proposals. They are
not covered merely because fixed `mul2_mod15` already works.

## Costs, review cases, and unresolved work

Each quantum attempt uses `m+n` public qubits plus modular-arithmetic scratch,
`m` controlled modular multiplications, `O(m^2)` Fourier operations under the
stated exact-rotation model, `m` phase measurements, and target discard. If a
clean controlled multiplication costs `C_mul(n)` gates and `W_mul(n)` scratch,
report `O(m C_mul(n) + m^2)` gates and `m+n+W_mul(n)` peak qubits, plus routing
and synthesis costs. No particular arithmetic circuit or scaling for `C_mul`
is claimed by this draft. Repeating elementary U `2^m-1` times would destroy
the intended efficient-access interpretation. Compilation, power-coefficient
generation, exact preprocessing, continued fractions, and at most `B` sampled
attempts all have separate costs. All displayed host loops are finite, and
their bit lengths and budgets must be accounted for.

Review cases: N=15/a=2 has orbit length four; y/M=1/4 or 3/4 produces period
four and factors 3 and 5, while 0 or 1/2 does not produce a checked period
under this single-sample policy. N=21/a=2 exercises non-dyadic phase recovery;
all values x>=N exercise the extension; N=9 exercises perfect-power handling;
prime N and budget zero exercise explicit exhaustion. These are proposed
review cases for the draft, not a claim of compiling its imaginary code.
The independent [finite mathematical checks](../../scripts/check_imaginary_v1_examples.py)
exercise selected conventions and counterexamples directly; they do not parse,
compile, or execute this imaginary source.

Unresolved: efficient full-space modular arithmetic with exact scratch
certificates; static power-provider binding; generic QPE approximation budgets;
exact integer limits and host/source ownership boundaries; sampler/backend
semantics; a global confidence contract; distribution-sensitive retry policies
and multi-sample order reconstruction. Existing finite tests and successful
factor checks do not prove the generalized compiler or establish practical
quantum advantage.
