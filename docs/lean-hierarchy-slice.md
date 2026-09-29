# Executable shared phase DAG: first CD-3 slice

Status (2026-09-29): **implemented and proved for cyclic phase actions in the
experimental `phase256-dag-v1` profile**. This extends the
[Mathlib-free Lean kernel](lean-kernel-migration.md), beginning CD-3 without
enabling the production [QPE hierarchy](hierarchical-ir-spec.md). Current Rust
source and QIRF verification are unchanged. The v0.5.0 Qleisli Soundness Theorem,
full CD-3 and H1–H5 remain open.

## Program and obligation

The [original source and diagnostic](../tests/fixtures/lean_hierarchy/README.md)
request two nested `repeat_static(4096, ...)` operations around T. The existing
frontend rejects the resulting finite function evidence. The desired artifact
instead retains three shared definitions: T, its 4096th power, and that
definition's 4096th power. Both repetitions have identity meaning, while actual
execution would still require 16,777,216 primitive gates.

This slice removes expansion from checking that artifact. It does **not** yet
make the saved `.qli` program compile: the experimental artifact is manually
authored, and no source-to-DAG producer or translation proof exists. The record
is informed development, not a controlled authoring benchmark. No new `.qli`
syntax, sealed built-in, standard-library API or external corpus source is added.

## Meaning, interfaces and evidence

Each definition retains one quantum owner with the same input/output shape.
The closed shape tags are `Unit`, `Bit`, `Bits0`, `Bits1`; the latter two are
experimental wire tags, not implemented source notation. Exact tag equality is
required at every dependency and at the independently supplied root request.
Equal widths do not identify `Unit` with `Bits0`, or `Bit` with `Bits1`.

`Unit` and `Bits0` still have one owner and require input/output port lists
`[0]`. Their leaves must be empty. A call requires exactly `[0]` on both sides
for every shape; omitted, duplicated or out-of-range owner ports reject.
There are no classical slots, effects, pair trees, layout conversions or
arbitrary-width interfaces in this initial profile.

The four instructions are:

| Instruction | Meaning and checking |
| --- | --- |
| `leaf word` | Normalize an X/dyadic-phase word with the proved phase-word checker definitions. No imported Rust success flag or opaque leaf evidence is accepted. |
| `call child inputs outputs` | Use a previously checked definition, preserving the complete owner port lists. |
| `sequence children` | Compose a nonempty ordered list of definitions on the same owner. Repeated references are significant. |
| `repeat count child` | Apply the child's action `count` times. Check the dependency, type and proposed meaning even at count zero. |

Definitions are serialized in topological order; every reference must point
strictly backward. This deliberately narrower experimental ordering rejects
even acyclic forward references. Self-cycles, longer cycles, missing references
and any definition unreachable from the entry reject. Zero repetitions retain
their dependency for reachability and validation. A zero repetition is allowed;
an empty `sequence` is not. The identity leaf is `leaf 0`.

For a bit `b` and natural phase `a`, a summary `(flip,p0,p1)` means
`(b xor flip, (a + p[b]) mod 256)`. Both phase entries must be canonical in
0..255. A primitive `pK` adds K ticks to the phase of bit 1; `x` flips the bit.
This retains global phase: `x p16 x p16` has `(0,16,16)`, not identity.

Each definition includes an untrusted proposed summary. The checker derives
every summary once from actual instructions and previously **derived** summaries,
then compares every claim and the independent root request. A false intermediate
claim rejects even when the root request is correct. No artifact-provided
theorem ID, algorithm name or schema selects an unchecked acceptance path.

The closed power implementation uses the two possible permutations of one
bit. If the summary does not flip, multiply each phase by the count. If it
flips, each pair of applications contributes `p0+p1`; an odd remainder applies
the original flip and phases. All phases reduce modulo 256. This requires no
iteration over the count or expansion of the body, and keeps global phase.

## Actual executable theorems

All these definitions and proofs live in the Lean 4.30.0 package with only
Init/Std dependencies. The existing Mathlib proof package is separate.

| Declaration | Proved statement and scope |
| --- | --- |
| [`compose_action`](../lean-kernel/QleisliKernel/Composition.lean) | Summary composition equals sequential operational actions. |
| `powerSummary_eq_repeat`, `powerSummary_action` | The closed power equals recursive summary composition and direct operational repetition, for every natural count and summary. |
| [`Dag.evaluate_map`](../lean-kernel/QleisliKernel/Dag.lean) | Shared evaluation commutes with any interpretation preserving leaves, identity, sequence and powers. The theorem is over the actual cached evaluator. |
| `Dag.evaluate_actions` | Evaluated summaries interpret to the separately defined gate/action evaluator. |
| [`Hierarchy.check_sound`](../lean-kernel/QleisliKernel/Hierarchy.lean) | `check definitions entry required = .ok stats` implies `denote definitions entry = some required.meaning.action`. |

The semantic evaluator executes operational gate actions and recursively
composes them; the native checker uses cached summaries and the proved closed
power. Large operational repetitions are theorem subjects, not computations
performed by verification. Structural/type/port checks execute before semantic
evaluation, but a general resource-safety theorem has not been added here.

These are cyclic phase semantics. The intended complex interpretation is
`|b⟩ ↦ exp(2π i p[b]/256)|b xor flip⟩`. Small independent amplitude-column
experiments check this correspondence, retaining scalar phase; they are not a
complex-number interpretation theorem, an entangled-reference proof, or QPE
instrument correctness. Parser/native compilation correspondence also remains
outside these theorem statements. The compiled declaration/axiom audit and
fresh Lean-kernel replay cover every new executable module.

## Experimental wire contract

From the repository root after building `lean-kernel/`:

```sh
lean-kernel/.lake/build/bin/qleisli-kernel --phase-dag tests/fixtures/lean_hierarchy/shared.qhd tests/fixtures/lean_hierarchy/identity.qhr
python3 scripts/test_lean_hierarchy.py
```

The artifact is:

```text
qleisli.phase-dag 1 phase256-dag-v1
entry 2
nodes 3
Bit 0 0 32 leaf 1 p32
Bit 0 0 0 repeat 4096 0
Bit 0 0 0 repeat 4096 1
```

The separate requirement is:

```text
qleisli.phase-dag 1 phase256-dag-v1
Bit
expect 0 0 0
```

After the header, the artifact has one entry line, one definition-count line,
then exactly that many definition lines. Each definition is
`shape flip phase0 phase1 instruction`. Instruction encodings are
`leaf length gates...`, `repeat count child`, `sequence length children...`, or
`call child inputCount inputPorts... outputCount outputPorts...`. For example,
`call 0 1 0 1 0` maps owner 0 to owner 0. Leaf gates are `x` or `pK`.

Tokens use exactly one ASCII space. Every line, including the last, ends in
LF. Only printable ASCII and LF are accepted. Canonical unsigned decimals have
no leading zero except `0` itself, signs, fractional parts or exponents.
Unknown fields, instructions, profiles, types and versions reject. QFT/QPE
names carry no significance. The old two-file phase-word invocation remains
available; neither experimental format is QIRF or `qpe-dyadic8-v1` JSON.

| Bound | Value and enforcement |
| --- | --- |
| Input bytes | 65,536 for each file, read with at most one extra byte before UTF-8 decoding. |
| Definitions | 1..256; zero-based entry and call/repeat IDs decode in 0..255. Sequence IDs decode up to 4096, then all references must name an earlier actual definition. |
| References | At most 4096 in total, counting repetitions, calls and every sequence occurrence, including zero-repeat dependencies. |
| Leaves and repeats | At most 4096 gates per leaf and count in 0..4096 per repetition. |
| Depth | At most 64, with leaves at depth 1 and every dependency counted even at zero repetition. |
| Work | At most 2,000,000 charged units across preflight; see the cost model below. |
| Numeric input | At most four digits before conversion; flip 0..1 and phases 0..255. Port/sequence length and index tokens are additionally bounded by the decoder. |

On success the process exits 0 and returns one JSON line with
`format:qleisli.kernel-result`, `version:1`, `profile:phase256-dag-v1`,
`accepted:true`, `code:accepted`, `stage:verification`, `node:null` and `stats`.
On failure it exits 1, sets `accepted:false`, `stats:null`, and uses
`syntax`, `limit`, `io`, `invalid_ir` or `contract` as the code. Decode/I/O
failures identify stage `artifact` or `requirement` and have `node:null`.
Verification failures identify a definition index (the offending node for
local checks; entry for root/global failures). No partial success is returned.
Wrong argument count retains the existing phase-word usage envelope and exit 2.

## Costs and remaining integration

Successful statistics separate `nodes`, `references`, `depth`, `work_units`,
`expanded_gates` and `dense_dimension`. The last is zero: this checker creates
no dense matrix. `nodes` counts stored definitions, each interpreted once in
the semantic pass; it is not the total number of visits across all passes.
Preflight, reachability and receipt comparison make separate bounded passes.

The charged work for each definition is `1 + 4*references + localWork`, where
`localWork` is `1 + 3*gateCount` for a leaf, both port-list lengths for a call,
the reference count for a sequence, and 16 for a closed power. This is an
explicit accounting model, not an elapsed-time or whole-process cost theorem.
`expanded_gates` instead sums execution multiplicities: repeats multiply by
their count, calls preserve the child's cost, and sequences sum occurrences.
It is an exact natural-number estimate of primitive gate execution, not a
claim that a large circuit was simulated. Bounded depth/fanout/count keep the
size of these integer operands bounded too.

The three-definition example uses 47 work units for 16,777,216 implied gates.
A 64-definition chain uses 1328 units for `4096^63` implied gates. Independent
small execution, wrong-phase claims, changed dependencies/ports/types, zero
repetitions, cycles, capacities and malformed inputs are tested in fresh
processes. The [development record](../tests/fixtures/lean_hierarchy/README.md)
retains measured artifact/request sizes and actual observations.

The next [typed layout component](lean-layout-slice.md) now checks multi-owner
interfaces, full prefix type trees and explicit axis permutations, with proved
inverse/reference reindexing. It is separate from this phase DAG; neither
component yet supplies general shared typed calls or arbitrary encodings.

Remaining CD-3 work must integrate these interface/type trees and encodings, general
hierarchical forms including tensor/control/inverse, an explicit finite-leaf
boundary, complex interpretation and the proved QFT/controlled-power/QPE
instrument schemas. It must then bind source generation and execution to the
verified artifact. This slice closes none of those gates by naming them.
