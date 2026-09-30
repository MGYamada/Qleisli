# Shared typed layout calls: CD-3 continuation

Status: **implemented with actual-checker proofs**, 2026-09-29. This experimental profile
connects the [typed layout checker](lean-layout-slice.md) to shared calls and
ordered composition. Production Rust verification remains authoritative.

The [first source](../tests/fixtures/lean_layout_dag/first_source/main.qli)
calls one ordinary definition twice, retaining a quantum Unit owner. The
checking obligation is to bind each invocation to its actual callee and to
its complete input/output owner maps, without expanding shared definitions.
This packet adds no quantum gate, source syntax or implicit type conversion.

## Adopted bounded contract

The profile `typed-layout-dag-v1` contains topologically ordered definitions.
Each definition is a literal layout, a call to an earlier definition through
explicit input and output layouts, or ordered composition of two earlier
definitions. Every definition carries its resulting layout and two inverse
maps as untrusted evidence. The existing layout rules apply to every result
and both call adapters, including exact tuple trees and zero-width owners.

Composition requires the first output interface to equal the second input
interface exactly, including each ordered axis list. Its output-to-input map
is computed from the two actual maps. Calls compose input adapter, actual
callee, then output adapter. Claims do not substitute for this computation.
The entry's computed layout must equal a separately supplied requirement.
All definitions must be reachable; forward, cyclic and missing references
reject. A valid wrong call or swapped composition order must fail the
independent requirement even when all individual types check.

Limits are 256 definitions, 4,096 dependency visits, depth 64, 2,000,000
aggregate conservative layout work units, and 65,536 bytes per file. The
existing per-layout capacities remain in force. Verification computes one
summary per definition. It reports nodes, references, work, depth and expanded
layout applications separately, with dense dimension zero. Each literal leaf
counts as one layout application; a call includes its two adapters, even if
they are identity layouts. Work includes the final independent entry validation
as well as each stored result and adapter. It is charged before structural
validation. No repeat, inverse,
tensor, partial frame, general encoding or phase/gate rule is added here.

## Checking experiment and proof obligation

Use a separate process with independently supplied requests. For small cases,
an external oracle runs literal owner-wise permutations on basis assignments,
following calls and composition directly; it also transports arbitrary joint
reference amplitudes. Pair accepted cases with valid-but-wrong dependency,
adapter and order mutations, and malformed type, owner, inverse and graph
mutations. A depth-64 doubling DAG must retain linear validation visits despite
its exponential expanded application count. The 16-axis boundary requires no
dense simulation. Preserve initial source and actual diagnostics before repairs.

The [executable proof](../lean-kernel/QleisliKernel/LayoutDag.lean) connects cached
composition to a separate operational interpretation of the graph, then connects
actual acceptance to the independent request:

| Theorem | Scope |
| --- | --- |
| `lookup_eq_indexAt` | The total coordinate action agrees with the finite layout map at every valid index. Outside the interface it is defined as identity. |
| `lookup_compose`, `compose_sound` | Computing a compatible layout composition equals composing the actual owner/axis functions in execution order. |
| `evalNode_sound`, `evaluateFrom_sound` | Actual successful cached evaluation agrees with the separate graph interpretation, including both call adapters. No result claim appears in that interpretation. |
| `checkMeanings_sound`, `check_sound` | Actual acceptance implies the independently requested graph meaning and a successful entry `Layout.check`, supplying the exact type/owner/axis permutation certificate. |

Layout permutation/reference theorems therefore apply to accepted entry results.
The interpreter and summary evaluator use standard total list folds; compiled
declarations are audited for generated partial recursion replacements as well.
This is phase-free coordinate semantics, not the full Qleisli Soundness Theorem,
a source-translation proof, a parser proof or a native compiler proof.

## Transport

The artifact header is `qleisli.layout-dag 1 typed-layout-dag-v1`, followed by
`entry N`, `definitions N`, and exactly that many definition blocks. Headers
are `leaf`, `call N`, or `then N N`. A leaf or composition has one certified
layout block; a call has input adapter, output adapter, then result blocks.
Each block uses the existing layout body with inverse maps, without its header.
The separate request retains the `typed-layout-v1` request envelope and fixes
the complete entry layout. Canonical tokens and strict LF rules are unchanged.
The command is `--layout-dag ARTIFACT REQUIREMENT`.

The subsequent [phase/layout profile](lean-phase-layout-slice.md) adds sparse
dyadic phase actions to typed calls under a separate envelope, leaving this
phase-free format unchanged. General gate, encoding and QPE integration remains
outside both component claims.

The [development record](../tests/fixtures/lean_layout_dag/README.md) retains
actual first diagnostics and subsequent results. The [release checkpoint](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/releases/v0.2.0.md#shared-typed-layout-checkpoint-2026-09-29)
separates performed checks from pending production and distribution gates.
