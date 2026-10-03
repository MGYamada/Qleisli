# Resource semantics

Third v1 pillar, **to prove**, under RS-C1–C5 and [trust amendment](../TRUSTBOUNDARY.md#resource-safety-amendment-2026-09-30). No current acceptance rule/estimator is added.

## Intended guarantee and domain

Actual static analysis/checking returns finite R(P) bounding cost(τ) for every admissible input/execution/prefix, with termination in the finite supported model. Overflow/timeout/unsupported analysis issues no evidence. Syntax/domain remain unselected.

## A first-class account alongside types and effects

Compose with meaning/types/effects/retained frames: sequential events add, exclusive branches take worst admissible case, coherent control charges actual circuit. Peak space needs lifetimes/schedule; tensors include concurrency and repetitions count every execution despite shared IR. Include clean/dirty synthesis/routing scratch and separate exact return evidence. Cost may be nonlinear despite linear type sizes.

| Field | Intended quantity |
| --- | --- |
| q / a | Peak total / auxiliary live qubits, including retained frames; count proves no cleanup. |
| T / D | Executed target T (or declared substitute) count / depth under declared scheduling/dependencies. |
| M | Measurements including hidden outcomes. |
| Other | Oracle queries/classical work/storage with separate units/model. |

## Compilation preserves the contract

Actual lowering/optimization/synthesis/layout/emission proves or independently validates bounds and model translations alongside meaning; excess requires recheck/reject. Include approximation/synthesis costs. Finite retries include failure; unbounded repeat-until-success has no finite worst case. Expected cost, compiler/search/simulator budgets, latency/noise and algorithm success differ.

## Current status and trust

Ownership/R1/S05 ResourceSafe, work limits/diagnostics/QLT costs/numerics do not prove quantitative RS. All annotations/certificates are untrusted proposals; check actual outputs/assumptions.
