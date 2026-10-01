# Resource semantics and the Resource Safety Theorem

Adopted third v1 pillar, 2026-09-30; **to prove**. [RS-C1–C5](release-milestones.md#resource-safety-theorem-v1) and the [trust amendment](../TRUST_BOUNDARY.md#resource-safety-amendment-2026-09-30) fix duties. No new current acceptance rule or trusted estimator.

## Intended guarantee and domain

The actual static analysis/checking path must produce a finite bound for every admissible input, execution and prefix, with termination under the finite supported model. Overflow, timeout or unsupported analysis is failure to issue evidence. Final syntax/resource domain remain unspecified.

```math
\Gamma\vdash_{\sigma} P:A\to B
\quad\Longrightarrow\quad
\mathrm{analyze}_{\sigma}(P)=R(P)\in\mathcal{R}_{\sigma},
\qquad
\forall x,\tau,\;
\mathrm{admissible}(\Gamma,x)\land\mathrm{exec}_{\sigma}(P,x,\tau)
\Longrightarrow\mathrm{cost}_{\sigma}(\tau)\preceq R(P).
```

## A first-class account alongside types and effects

Compose cost with meanings, types/effects and retained input/output/frame roles. Sequential events add; exclusive classical branches use worst admissible case. Coherent control charges the actual controlled circuit. Peak space needs lifetimes/frames/schedule; tensors account for concurrency and repetition for each execution despite shared IR. Include source/data, clean/dirty synthesis and routing workspace and its zero-return contract; register width is not total live backend space. Cost expressions may be nonlinear even when type sizes are linear.

| Component | Intended quantity; the cost model must fix its convention |
| --- | --- |
| `q` | Peak simultaneously live logical qubits, including workspace and retained frames. |
| `a` | Peak auxiliary qubits within that total; entry/output and clean-return roles remain explicit. A count is not evidence of zero return. |
| `T` | Executed T-gate count for a target that includes T, or an explicitly named replacement metric for a different gate basis. |
| `D` | Circuit depth under declared dependency, scheduling and target assumptions. |
| `M` | Executed measurements, including hidden outcomes inside the specified boundary. |
| Further fields | Declared oracle queries, classical work/storage, or other target costs, with separate units and operational meanings. |

## Compilation preserves the contract

Every actual pass must prove or independently validate target bounds and explicit translations between cost models, alongside meaning preservation. A bound exceeding the accepted contract requires rechecking or rejection. Include synthesis/approximation costs. Worst-case finite retry budgets need failure outcomes; unbounded repeat-until-success has no finite worst-case theorem inside this boundary. Estimates/expected cost, compilation/search resources, simulator budgets, latency/noise and algorithm success are separate.

## Current status and trust

R1/ownership and S05 ResourceSafe are not quantitative resource bounds. Current execution/work limits, diagnostics, QLT cost tests and numerical corpus measurements do not complete RS. Rust/Python/foreign/AI annotations and certificates remain untrusted proposals; actual output and assumptions must be checked.
