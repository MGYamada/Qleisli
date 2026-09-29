# Resource semantics and the Resource Safety Theorem

Status: **long-term direction adopted on 2026-09-30; to prove**. The user added
quantitative Resource Safety as the third theorem pillar, alongside Qleisli
Soundness and Physical Realizability. The [v1 theorem gates](release-milestones.md#resource-safety-theorem-v1)
are authoritative. This document specifies the intended guarantee and design
constraints, not implemented syntax, an analyzer or an existing Lean theorem.

## Intended guarantee and domain

> Well-typed Qleisli programs admit finite, statically computable resource bounds
> that are preserved by compilation.

This target concerns the declared finite, resource-checked language profile,
with explicit size/input premises and target capabilities. Its resource-aware
typing judgment is a future extension: today's typing success does not already
certify the quantitative theorem. For each admitted size instantiation, the
analyzer must compute a finite bound before execution; a parametric family may
have a symbolic bound in its size parameters. There need not be one constant
bound for every possible size.

Let `sigma` identify a versioned cost model, gate set, layout/scheduling model
and execution boundary; let `R_sigma` be its ordered domain of finite bounds.
For the actual accepted program `P`, admissible input `x` and execution trace
`tau`, the intended obligations include:

```math
\Gamma\vdash_{\sigma} P:A\to B
\quad\Longrightarrow\quad
\mathrm{analyze}_{\sigma}(P)=R(P)\in\mathcal{R}_{\sigma},
\qquad
\forall x,\tau,\;
\mathrm{admissible}(\Gamma,x)\land\mathrm{exec}_{\sigma}(P,x,\tau)
\Longrightarrow\mathrm{cost}_{\sigma}(\tau)\preceq R(P).
```

These are specification names, not current declarations. An existential finite
number alone is insufficient: the executable analysis/checking path must produce
the bound and justify the inequality. Execution includes every permitted prefix
as well as completed runs; establish termination for the supported finite
execution model, rather than bounding only runs that happen to finish.
A producer's estimate, an overflow, a
timeout or an unsupported analysis cannot issue resource evidence. Concrete
syntax, the final resource domain and acceptance algorithm remain to be specified.

## A first-class account alongside types and effects

Internally, a component may carry a resource account in addition to `f : A -> B`
and its effect. The motivating vector is `cost(f) = (q, a, T, D, M, ...)`:

| Component | Intended quantity; the cost model must fix its convention |
| --- | --- |
| `q` | Peak simultaneously live logical qubits, including workspace and retained frames. |
| `a` | Peak auxiliary qubits within that total; entry/output and clean-return roles remain explicit. A count is not evidence of zero return. |
| `T` | Executed T-gate count for a target that includes T, or an explicitly named replacement metric for a different gate basis. |
| `D` | Circuit depth under declared dependency, scheduling and target assumptions. |
| `M` | Executed measurements, including hidden outcomes inside the specified boundary. |
| Further fields | Declared oracle queries, classical work/storage, or other target costs, with separate units and operational meanings. |

Resource semantics should compose with meaning and effects. For sequential
composition, additive event bounds such as T and measurement counts add;
exclusive classical branches use the worst admissible branch, not an expected
value. Coherent `qif` instead charges its actual controlled implementation;
it cannot take the maximum of two quantum branches as though only one circuit
were executed. Peak live
space requires live-input/output and frame information, rather than simply
adding independent gate counts. Tensor composition must account for concurrent
space and the selected schedule; disjoint ownership does not assert a product
state. Repetition charges every actual execution even when its body is shared
in the IR. Query access, inverse and controlled implementations carry the costs
of their actual providers; abstract unitarity does not supply them for free.

The composition rules must cover initialization, retained targets, auxiliary
allocation/release, routing and measurement. This extends the existing
Kleisli-inspired tracking of ownership, classical context and effects; it does
not claim a proved categorical or monadic structure. Resource expressions are
not type-level size expressions: a cost may be nonlinear in sizes even while
the [adopted size-equality language](size-expressions.md) remains linear.

## Compilation preserves the contract

Every source/IR/target stage needs its declared cost semantics. For a pass from
`P_i` to `P_next`, bind a resource certificate to the actual input/output and
the target assumptions, alongside the separate meaning-preservation obligation.
The pass must prove or independently validate an output bound. Different gate
sets and schedules need an explicit bound-translation rule; do not compare
incommensurate raw counts or assume optimizations preserve exact costs.

The accepted end-to-end resource contract must still bound the emitted program.
A transformation that increases a bound beyond that contract requires explicit
rechecking under a revised contract or rejection; silently replacing the promised
bound is not preservation. Synthesis, layout, lowering and optimization all
participate. External search may propose a circuit and resource certificate,
but its actual output must be checked, including approximation precision when
that affects the cost. Sharing a definition reduces storage/checking work,
not its repeated quantum execution cost.

The guarantee is a worst-case finite bound over all permitted measurement and
classical branches. Unbounded repeat-until-success has no such worst-case bound:
use an explicit finite attempt budget with a failure outcome, or keep that host
loop outside the theorem boundary. Expected cost can be reported separately.
The quantum-circuit bound does not automatically bound compiler/proof-search
time, simulator memory, wall-clock latency or device noise. Include those only
under separately specified models and checked premises. Static computability
does not imply polynomial cost, practical efficiency or algorithmic success.

## Current status and trust

Current ownership/SSA/effect checks, exact-work limits, simulator step limits and
cost diagnostics remain useful, but none completes this theorem. In particular,
the older `ResourceSafe` placeholder in S05 describes linear ownership validity;
it is not this quantitative resource bound or the existing R1 ownership result.
QLT cost evaluation and finite corpus measurements can test future rules without
becoming resource evidence by themselves.

The [trust-boundary amendment](../TRUST_BOUNDARY.md#resource-safety-amendment-2026-09-30)
adds a **to prove** obligation, not a newly trusted estimator or optimizer.
Resource annotations/certificates from Rust, Python, foreign formats, humans or
LLMs remain proposals. Present finite acceptance and the Rust/Lean authority
transfer gates are unchanged. This future v1 pillar adds no implementation or
proof requirement to the current 0.2.1 release or the deferred 0.2.2 scope.
