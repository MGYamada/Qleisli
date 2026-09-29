# Full-profile dependency scheduling

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

## Constructed denotations

The [evaluation packet](evaluation-packet.md) removes the assumed interpretation
environment for supported accepted derivations. The partial mathematical
evaluator reads actual bodies and all their child references, including a
zero-repeat body. Successful results persist with larger dependency fuel and
are unique. A proof by induction over the actual accepted derivation constructs
sufficient fuel and the same successful implementation/meaning value. The
complex operator, matrix and arbitrary-reference equations then use these
constructed denotations. Proof metadata does not enter either reader.

`HierarchicalEvaluation-first.lean.txt` retains the first implementation.
`evaluation-first-build.json` records that this initial evaluator and its
stability/uniqueness helpers built successfully. Subsequent real proof and
example repairs are summarized in [evaluation-repair-notes.md](evaluation-repair-notes.md).
Nine kernel-checked example theorems cover an accepted π/8 provider under a
direct power schema with independently reordered meaning indices, insufficient
and sufficient depth, the reordered meaning, absent references, zero-repeat
missing/cyclic bodies, an unsupported finite leaf and constructed denotation
existence. These are mathematical evaluator cases, not a new native runtime
suite or a substitute for its resource checks.

The runtime checker is unchanged and expands no repetition. The mathematical
evaluator is not the reference simulator; whole-space unitarity, finite leaves,
remaining rules, external acceptance and source integration remain mandatory.
The preceding registry result is preserved in
`../lean_qpe_instrument/registry-before-evaluation.json`.

## Actual-body complex interpretation

The [operator packet](operator-packet.md) supplies mathematical preservation
for the supported derivations below. `HierarchicalSemantics-first.lean.txt`
and `HierarchicalOperators-first.lean.txt` retain first implementations.
`operator-first-build.json` records the first real build failure; the
[repair notes](operator-repair-notes.md) summarize subsequent actual diagnostics.
Repairs use proved Boolean-equality instances, explicit array/Option membership
and complete interface equalities. No proof admission, increased elaboration
limit, executable-kernel change or audit exception was introduced.

The new theorems prove accepted operator equations under interpretation of
actual table bodies, not proposed proof conclusions. They instantiate complex
coefficients, prove composition/repetition matrix laws and compare entire
joint reference maps. The direct-power bridge obtains its provider equation
from the actual premise derivation. Six kernel-checked example theorems cover
three-axis orientation, selected phase, tensor axis order, conjugate inverse,
coherent control and the visible relative sign of a controlled negative
identity. The count is theorem cases, not a new native sampling suite.

The explicit remaining interpretation premise still needs a constructed
whole-artifact semantics; whole-space unitarity, finite reconstruction,
unsupported rules, external request/schema binding and executable source
remain separate obligations. Native runtime derivation behavior is unchanged.
The previous completed registry check is retained as
`../lean_qpe_instrument/registry-before-operator.json`; the current refreshed
record is `../lean_qpe_instrument/registry-checks.json`.

## Supported derivations from an empty cache

The [derivation packet](derivation-packet.md) advances beyond the pending
provider projections described below. `Rule-first.lean.txt`,
`Derivation-first.lean.txt` and `DerivationHarness-first.py.txt` preserve first
implementations. `derivation-first-diagnostics.txt` records the initial wrong
working-directory build and the pre-build resource review.
`derivation-first-build.json` records actual local-rule proof errors. Repairs
made dependent match arguments explicit, reduced record projections for budget
arithmetic and used the real optional-array lookup lemmas. The empty-cache and
step/scan invariants now prove that actual accepted conclusions have finite
derivations with all premises established. No admission, increased proof limit
or audit exception was used.

The first native run reached all 188 initial cases, then its Python expectation
for a missing premise disagreed with the actual earlier graph rejection.
Removing that premise makes its proof unreachable, so `invalid_ir` is the
correct diagnostic, instead of the initially expected `contract`.
`derivation-first-native.json` retains the observations. The final expanded
`derivation-native.json` passes **235 cases**: **184 complete supported
derivations**, **one local rule match**, **50 rejections**. It includes 104
size/exponent combinations, three table permutations, 39 phase-provider power
cases through denominator 256, exact local budget 5,398/5,397, empty owners,
explicit conversion, cycles, false provider meanings and opaque finite leaves.

An independent recursive Python rule oracle checks **69** generated/shared
graphs without trusting the proposed schedule or cache. A separate exact
monomial interpretation checks **132 nonzero coefficients** at dimension at
most four and retains **21 semantic counterexamples**, including noncommuting
phase/rewire order. Large nested repetitions use mathematical exponentiation
in that oracle; the Lean checker expands no repeated body and creates no dense
matrix. Successful shared graphs report one check per proof node.
`derivation-reductions.json` records kernel evaluation of valid/invalid requests
and the distinction between a pending projection and a rejected finite claim.

This proves derivation closure, not yet its complete complex soundness.
Finite reconstruction, arbitrary call/encoding/computed derivations, complete
QFT/QPE integration, independent external root requests and source support are
still mandatory. No external schema is enabled. Previous artifact/power native
records are preserved as `*-native-before-derivation.json`; current versions
are rerun for the new phase rule. The preceding registry record is
`../lean_qpe_instrument/registry-before-derivation.json`.

## Controlled-power binding

The preceding continuation is the [controlled-power binding packet](power-binding-packet.md).
`Power-first.lean.txt`, `PowerBridge-first.lean.txt` and `PowerHarness-first.py.txt`
retain their first implementations. Actual diagnostics are retained in
`power-first-diagnostics.txt`, `power-bridge-first-diagnostics.txt` and
`power-first-native.json`. Runtime repairs factored the acceptance proof into
local projection and final binding, annotated reference arrays, and corrected
Boolean/array lemmas. The proof bridge uses actual Option monad reductions.
The native harness repaired record-field indentation and replaced unchecked
array indexing requiring an absent default-value instance with explicit source
data. None of these repairs relaxed checker conditions or audit requirements.

`power-native.json` records **182 native cases**: **127 pending projections**,
**48 rejected inputs**, and **seven well-typed semantic counterexamples** that
the schema projection rejects. They include all 104 width/exponent combinations
`n=1..8, k=0..12`, thirteen independently reordered definition/meaning tables,
complete type/axis/empty-owner mutations, provider/count/polarity/premise/metadata
mutations, cycles, a malformed body under zero repeat, and exact remaining-budget
boundaries 15,633/15,632. Repetition 1 versus 4,096 has identical charged work.
Checker dense dimension and expanded repeated-body count are zero.

Two deliberately pending cases retain an opaque finite payload and a wrong
provider meaning. They expose the required remaining semantic obligation:
structural typing and projection do not issue semantic evidence. The actual
Lean operator/unitarity/reference theorems retain provider equation/isometry
premises. `power-reductions.json` records kernel reductions; the first reduction
attempt hit the elaborator heartbeat limit on two `cbv` checks, recorded in
`power-first-reductions.json`. Kernel evaluation via `decide +kernel` replaces
those checks without increasing limits or using native evaluation. CI and source
distribution include the native harness. This packet does not enable an external
schema, implement sized source or complete v0.2.0.

This is the scheduling part of the [adopted hierarchy](../../../docs/hierarchical-ir-spec.md#dependency-scheduling-implementation).
The source client is the retained [shared-QPE first attempt](../authoring_sessions/shared-qpe-v020/attempt-01/estimation.qli),
whose initial unsupported diagnostic is unchanged. Shared calls and controlled
repetition need one checked dependency per body, including count zero, with no
expanded execution during verification. This packet does not add sized syntax.

`Graph-first.lean.txt` is the exact first implementation. An incorrect working
directory prevented its intended pre-check copy; it was copied unchanged after
the first build, before any repair. `graph-first-diagnostics.txt` records a
repeat of that failing build, not a falsely claimed first-check capture.
The proof initially split a nested match before reducing local definitions.
Explicit branches and let reduction repaired the acceptance proof. No admission,
native proof evaluation or audit relaxation was used.

The native harness initially exceeded Lean's elaboration recursion depth on
large generated literal test data in one function. An attempted test-only depth
increase then exposed an elaboration heartbeat limit. Splitting cases into
separate definitions and invocation groups avoids both; no final elaboration override remains, and
the runtime's depth and work bounds stay unchanged.
Two small `decide` examples could not reduce array traversal; kernel `cbv`
reduction replaced them. These are development observations, not LLM benchmarks.

Run `python3 scripts/test_hierarchical_graph.py --record graph-native.json` from
the repository root with a chosen record path. The independent Python DFS uses
actual graph edges rather than the proposed evaluation order. Cases include
forward table references, 64 deterministically permuted DAGs and their wrong
schedules, cyclic/self/dangling dependencies, duplicate/missing schedule nodes,
unreachable data, depth 256/257, 100,000/100,001 nodes and work immediately below/
above two million. A 60-node shared graph represents 2^59 leaf uses while this
pass only traverses its 118 edges. `graph-native.json` retains observed decisions,
statistics, build output, compiled-binary hash and source hashes.

A final implementation review replaced up-front adjacency-list length sums
with a bounded fold that stops at the next over-budget reference, and bounded
the initial root scan. The earlier successful 151-case record is retained as
`graph-native-before-bounded-count.json`; the final suite additionally rejects
an oversized root list. `graph-reductions.json` records the kernel reduction
checks. This change closes uncharged preflight work on rejected inputs; accepted
graphs retain the same limits, statistics and semantics.

This graph component alone is not typed IR checking or a quantum soundness
result. Its theorem is actual-checker acyclicity, with explicit reachability and
budget checks. The subsequent projection implementation is recorded below.

## Typed artifact continuation

`Artifact-first.lean.txt` was saved before the first check.
`artifact-first-diagnostics.txt` records the missing ByteArray representation
and default-value instances in that attempt. The repair supplies a size-only
payload representation and uses checked optional lookups rather than default
definitions. Explicit match reductions repaired the acceptance proofs; no
admission or audit-policy exception was used.

The actual four-table representation now derives every dependency from typed
node fields, including proof endpoints, premises, witnesses and zero repeats.
`prepare_acyclic` connects preparation to the actual graph checker;
`endpoints_bound` connects endpoint acceptance to complete logical/physical
interfaces. Flat and nested tuples remain distinct; Bits(0) retains ownership.
The preparer and scheduler consume one work allowance, with no matrix or repeat
body expansion. No source-author obligation has been removed yet: the retained
shared-QPE source still needs the sized-source implementation.

Run `python3 scripts/test_hierarchical_artifact.py --record <output.json>`.
The final native suite has **54 structural cases**, **22 reference cases** and
**18 prepared results**. Independently written expected edges include every
reference field. It exercises table-index alias attempts, forward references,
cycles, zero-repeat invalid bodies, tuple/axis/zero-owner changes, proof endpoint
changes, fixed IDs and versions, oversized arrays and opaque payload bounds.
The last accepted shared case consumes **1,999,681** visits; the next would need
**2,000,082** and is rejected. The graph suite still has 152 cases after adding
the remaining-budget API.

`artifact-first-native.json` preserves the initial generated Lean indentation
error. Subsequent harness repairs corrected an independent budget expectation
(the per-proof total is 401 visits, not 397) and emitted compact JSON graph
arrays instead of line-wrapped representations. The successful 52-case
intermediate run is `artifact-native-before-shape-cases.json`; explicit flat
and nested positive cases and a Bit-target phase counterexample complete
`artifact-native.json`. `graph-native-before-artifact.json` preserves the graph
run preceding the remaining-budget implementation. These are development
observations, not a controlled model evaluation.

The positive full preparation example initially exhausted `cbv` elaboration
heartbeats (`artifact-first-reductions.txt`). `decide +kernel` evaluates the
same decidable statement in Lean's kernel and passed without raising limits;
the other small examples retain `cbv`. `artifact-reductions.json` records the
passing command and exact test-source hash.

## Complete side maps

`Ports-first.lean.txt` was saved before the first build, which passed. The
subsequent code review replaced prefix-list appends with direct structural
recursion and a proved owner-count equation. That version built and passed
native tests, but the compiled audit rejected Lean's generated
`coordinatesFrom._unsafe_rec` declaration. `Ports-recursion.lean.txt`,
`artifact-native-before-ports-audit.json` and the separate
`registry-ports-recursion-rejected.json` registry record retain this failure.
The final implementation uses the standard total list fold with prepend and
reverse, and proves its owner-count equation. No audit exception was added.
It also counts wire-array sizes before allocation so oversized rejected inputs
cannot trigger flattening first.
Candidate inverse maps come from the actual arrays; checked inverse laws and
full type matching establish the accepted permutations. The coefficient
round-trip theorem retains an arbitrary reference coordinate.

The same native harness now adds **39 side-map cases**: Bits widths 0–8, local
IDs distinct from map positions, owner/axis reorders and disagreement, aliasing,
missing and out-of-range positions, Unit/Bits(0) ownership, flat/nested types,
Bits versus Bit/products, within-register order, classical slot types and
ownership-independent labels, exact remaining-budget and oversized-storage
boundaries. `artifact-native-before-port-maps.json` preserves the prior
54/22-case run. The final record includes all 54/22/39 cases. Kernel reduction
records likewise retain the earlier run before adding side-map examples.

Preparation deliberately accepts a structurally valid phase mutation and an
opaque nonempty finite payload. Neither result is semantic acceptance. Node
typing, integration of the checked port bijections, finite verification, rule derivation, fixed
schema matching, external decoding and independent required-contract binding
remain required before any evidence handle or public wire format is enabled.

## Actual definition-node typing

`NodeTyping-first.lean.txt` was saved before the first check. The unchanged
failing build was replayed into `node-typing-first-diagnostics.txt` before
repairs. The first source needed explicit constructor/record types, a name
other than Lean's reserved `initialize`, and match reduction in the budget
proof. The whole-table fold proof then needed explicit Except pure/bind
reduction. No runtime recursion override, proof admission or audit relaxation
was used. The compiled audit passed for the actual module.

The native harness reuses the artifact harness's build/run helper. Its first
attempt (`node-typing-first-native.json`) needed record-field indentation and
optional encoding updates rather than indexing with an unprovided default.
The expanded attempt (`node-typing-expanded-first-native.json`) used reserved
`repeat` as a test variable; renaming it repaired compilation. The first 62-case
success is `node-typing-native-initial.json`. A final review charged index-list
allocation before constructing it; `node-typing-before-index-charge.json`
retains the intermediate 69-case result.

`node-typing-native.json` records **69 cases**: **28 structurally typed**,
**41 rejected**, with no semantic evidence issued. It covers every definition
constructor, exact sequence endpoints/effect joins, tensor ownership across
both lifetimes, consistent call renaming for owners/wires/classical values,
repeat/inverse/control restrictions, Bit-only phases, measurement/initialization
frames, computed-region endpoint obligations and shared capacities. The
whole-table check rejects an invalid body hidden inside count-zero repetition,
even though the parent alone satisfies its local rule. It also rejects a
nearly exhausted preparation budget before it can be reused for node typing.

`checkAll_conditions` proves actual preparation, all indexed local checks and
the total budget. Finite raw bytes and compute/uncompute equations are still
explicit obligations; the well-typed wrong-phase counterexample still passes
structural typing and must be rejected by the semantic rule checker.


## Actual meaning and encoding typing

`ContractTyping-first.lean.txt` was saved before its first build, which passed.
The executable checker now covers all meaning and encoding constructors, and
`checkAll_meaning` / `checkAll_encoding` connect whole-artifact acceptance to
every actual indexed object. Header comparisons, map checks and index-list
allocation continue the same budget as preparation and definition typing.
These results establish structural conditions; opaque finite payloads,
unitarity, compute/uncompute equations and schema derivations remain open.

The native suite's first compilation needed record-field indentation and an
optional array update rather than an index requiring an unprovided default.
`contract-typing-first-native.json` retains those diagnostics. The final
`contract-typing-native.json` records **164 cases: 115 typed, 49 rejected**,
including all **64** QPE target/precision combinations, retained target and
CBits precision, finite dimension limits, zero-width scratch owners, malformed
meaning bodies under zero power and shared-budget exhaustion. No matrix is
materialized and no semantic receipt is issued. The deliberately wrong phase
still types; a later semantic check must reject it.

`control-target-type-first.lean.txt` and `control-target-type-before.json`
preserve the actual old local control decision: a Bit-to-Bits(1) target change
was structurally accepted. The repaired rule preserves the ordered target
type trees in the inactive sector while allowing consistent local renaming.
This is an internal typing refinement before any external schema is enabled.
`node-typing-before-contract-types.json` preserves the preceding native record;
all 69 node cases were rerun successfully. Kernel reduction examples also pass,
with exact source hashes in `contract-typing-reductions.json`.

The rebuilt component registry and both compiled audits pass with **3,808**
runtime/transport declarations and **731** mathematical declarations. Runtime
source policy covers 24 modules, with no external Lake packages. Fresh Lean
kernel replay passes. All external registry entries remain disabled. These are
development observations, not a measured model benchmark or a release claim.


## Explicit ownership-structure conversions

The [packet](structural-packet.md) fixes this bounded A020-01 experiment before
implementation, against the retained desired take/put helper. The hierarchy
now has explicit structural definition and meaning nodes; both actual typing
passes invoke the same conversion predicate and charge its work to their
remaining allowance. A type-preserving rewire still rejects these conversions.
Source lowering and external semantic derivation binding remain pending.

`Structural-first.lean.txt` retains the pre-build source; the first build
passed. `structural-first-diagnostics.txt` records the real native output
framing failure and command-directory errors. The first harness run produced
multiline arrays that broke its line parser; its full native output was not
saved, and no first-run record is claimed. Compact array output repaired it.
The independently calculated small budget was corrected to 888/887 before the
successful rerun. Native probes now call actual `Layout.reindex`; Python uses
an independently written weighted-bit formula. Arbitrary phase/reference
preservation is the proved coefficient theorem, not a synthetic simulator test.

`structural-before-inverse-binding.json` preserves the intermediate success.
The final inverse routing is read from the actual reversed endpoints, and
`inverse_shape` proves the inverse descriptor has the reversed shape rule.
`valid_reference_round_trips` applies to the very predicate used by both typing
passes. No project recursion, native proof evaluation or audit exception was
introduced.

`structural-native.json` records **123 cases: 88 typed, 35 rejected**, plus
**7,216 basis probes** through actual native reindexing. Cases cover widths
1–8/all selected axes in both directions, Bit/Bits(1), immediate tuple fields,
flat/nested/zero-width types, explicit Unit/Bits(0) creation/consumption,
owner capture, missing/duplicated remainders, wire and type mutations, scalar
limits, oversized storage and exact shared-budget boundaries. Three cases
exercise complete definition/meaning/encoding table typing. The matrix
allocation dimension is zero; no external semantic receipt is issued.

Definition (69), contract typing (164) and preparation/map (115) regressions
were rerun; their earlier records are preserved with `-before-structural` names.
The unchanged dependency scheduler retains its earlier 152-case record.


Final conversion validation also passes kernel reduction examples, both compiled
audits (**3,937** runtime/transport and **731** mathematical declarations),
25-module runtime source policy, fresh kernel replay and actual-type registry
rebuild. The three permitted logical axioms are unchanged; external enablement
remains false for every schema. `structural-reductions.json` binds the kernel
examples to their exact sources. Final native source hashes match the checked
files. Clean distribution and the remaining full release gates are still open.
