# Lean backend expansion and Rust retirement, v0.3.1–v0.3.9

Requested roadmap, 2026-10-03. This proposes an accelerated implementation
schedule after the approved v0.2.9 Lean-only acceptance cutover. It does not
claim that these passes, protocols or proofs exist. Stage contracts and public
changes must be recorded in the relevant Issues before implementation. This
document and the imaginary-v1 tree were retained through the v0.3.0 docs cleanup
and now live under `docs/src/`. The retired `docs-old/` tree is deleted.

## Objective and architectural rule

By v0.3.9, make Lean own the supported production backend from an explicit
input artifact through transformations, target lowering and emitted output.
Remove the replaced Rust semantic implementations in each stage, rather than
maintaining two implementations until v0.5.0. Rust remains useful for source
loading, parsing, diagnostics presentation, transport, external tools and
untrusted search. Moving every host utility into Lean is not the objective.

Expand the **independently checked downstream segment**, while keeping the
[trusted partition](https://github.com/MGYamada/Qleisli/blob/main/TRUSTBOUNDARY.md) and acceptance rules small. The
Mathlib-free `lean-kernel/` package may grow substantially through reusable
semantics, checked transformations, runtime adapters and local proofs. Package
size is not the size of the detector: candidate construction, optimization
heuristics and synthesis search do not become acceptance rules merely because
they are implemented in Lean.

Keep both the input gate and the final output gate:

```text
Rust source frontend / foreign reader / external producer
    -> untrusted input artifact + independent requested contract
    -> Lean input acceptance
    -> backend passes + independently checked input/output relations
    -> Lean target/profile and final-byte checks
    -> immutable checked output / execution plan
    -> thin Rust I/O client or external runtime
```

This moves the last checked boundary toward the backend without abandoning
earlier checks. A valid output is not evidence that a pass preserved its input.
Binding source bytes also does not prove that the frontend expressed their
intended meaning. Source-to-Core preservation remains explicit; this roadmap
does not solve it by renaming a backend artifact.

## Starting point and remaining Rust responsibilities

The [v0.2.9 cutover record](https://github.com/MGYamada/Qleisli/blob/main/tests/fixtures/verification_v029/cutover/README.md)
reports one production acceptance implementation, 799 retained comparison
inputs, all 14 example projects, and known capacity differences. Full release
validation and S05 proof obligations are still open. Its measurements are a
baseline, not evidence for any future pass.

| Current source | Work still performed in Rust | Intended disposition |
| --- | --- | --- |
| [Native bridge](https://github.com/MGYamada/Qleisli/blob/main/src/interchange/native.rs), [transport](https://github.com/MGYamada/Qleisli/blob/main/src/interchange/native/runtime.rs), [view](https://github.com/MGYamada/Qleisli/blob/main/src/interchange/native/view.rs), [codec](https://github.com/MGYamada/Qleisli/blob/main/src/interchange/mod.rs) | Launching, serialization, conversion, evidence reconstruction and execution coordinates | Keep bounded I/O and public data adapters; move production conversion and semantic view construction to the native side. |
| [Finite circuit lowering](https://github.com/MGYamada/Qleisli/blob/main/src/frontend/compile/circuit.rs), [static transforms](https://github.com/MGYamada/Qleisli/blob/main/src/frontend/compile/lower/transforms.rs), [operation descriptions](https://github.com/MGYamada/Qleisli/blob/main/src/frontend/compile/operations.rs) | Flattening, remapping, adjoint/control/repetition and retained-call expansion | Replace with shared Lean backend operations and checked pass relations. |
| [Contract construction](https://github.com/MGYamada/Qleisli/blob/main/src/contract/mod.rs), [function evidence](https://github.com/MGYamada/Qleisli/blob/main/src/contract/function.rs), [exact arithmetic](https://github.com/MGYamada/Qleisli/blob/main/src/contract/exact.rs) | Candidate matrices/circuits, contract composition and rejected-equation diagnostics | Move production construction/composition and failure witnesses; preserve independent finite reference arithmetic outside acceptance where tests need it. |
| [Specialization lowering](https://github.com/MGYamada/Qleisli/blob/main/src/frontend/specialize/lower.rs), [preservation bookkeeping](https://github.com/MGYamada/Qleisli/blob/main/src/frontend/specialize/lower/preservation.rs), [Fourier factoring](https://github.com/MGYamada/Qleisli/blob/main/src/frontend/specialize/fourier.rs), [QPE binding](https://github.com/MGYamada/Qleisli/blob/main/src/frontend/specialize/qpe.rs) | Building and rewriting hierarchy proposals, source-event mappings and candidate discovery | Unify backend construction/checking; keep source elaboration and optional recognizers untrusted until separately replaced. Names never establish algorithm meaning. |
| [Terminal profile](https://github.com/MGYamada/Qleisli/blob/main/src/interop/profile.rs), [target rewrites](https://github.com/MGYamada/Qleisli/blob/main/src/interop/export.rs), [OpenQASM writer](https://github.com/MGYamada/Qleisli/blob/main/src/interop/openqasm.rs), [QIR writer](https://github.com/MGYamada/Qleisli/blob/main/src/interop/qir.rs) | Post-acceptance gate decomposition, workspace allocation, measurement ordering and output text | High-priority retirement: native checked target lowering and byte emission. Preserve foreign parsing as a distinct untrusted adapter. |
| [Flat simulator](https://github.com/MGYamada/Qleisli/blob/main/src/sim.rs), [sampling](https://github.com/MGYamada/Qleisli/blob/main/src/sim/sampling.rs), [hierarchy execution](https://github.com/MGYamada/Qleisli/blob/main/src/interchange/hierarchical/execution.rs) | Instruction interpretation, branch/axis bookkeeping, numerical evolution and sampling | Move duplicated semantic dispatch into one native execution plan/interpreter. Treat numerical arithmetic and randomness under explicit execution assumptions. |

Existing Lean components are starting points, not a complete backend:
[QIRF validity](https://github.com/MGYamada/Qleisli/blob/main/lean-kernel/QleisliKernel/Qirf/Validity.lean),
[encoded contracts](https://github.com/MGYamada/Qleisli/blob/main/lean-kernel/QleisliKernel/Qirf/Contract.lean),
[layout composition](https://github.com/MGYamada/Qleisli/blob/main/lean-kernel/QleisliKernel/LayoutDag.lean),
[phase operations](https://github.com/MGYamada/Qleisli/blob/main/lean-kernel/QleisliKernel/PhasePolynomial/Operations.lean),
[hierarchy derivations](https://github.com/MGYamada/Qleisli/blob/main/lean-kernel/QleisliKernel/Hierarchical/Derivation.lean),
[call lowering](https://github.com/MGYamada/Qleisli/blob/main/lean-kernel/QleisliKernel/Hierarchical/CallLowering.lean),
[circuit traces](https://github.com/MGYamada/Qleisli/blob/main/lean-kernel/QleisliKernel/Hierarchical/CircuitTrace.lean) and
[instrument evaluation](https://github.com/MGYamada/Qleisli/blob/main/lean-kernel/QleisliKernel/Raw/StreamedInstrument.lean).
Read each actual theorem's premises; a structural derivation or trace theorem
alone is not equality of complex operators or instruments.

## Schedule

Versions are target checkpoints, not permission to skip a dependency. Each
stage retires the replaced production body once its gates pass. A blocked
profile remains visibly incomplete; it cannot be declared migrated because
another profile works.

| Target | Native deliverable | Rust debt removed at that stage |
| --- | --- | --- |
| v0.3.1 | Bounded batch protocol, native failure detail and capacity recovery | Repeated production invocation orchestration and redundant failure re-evaluation, after replacements cover their contracts. |
| v0.3.2 | Explicit pass relations, immutable artifacts and native conversion | Semantic conversion/reconstruction in production export paths. |
| v0.3.3 | Checked circuit composition, adjoint/control/repetition and local rewrites | Duplicate finite circuit transform bodies. |
| v0.3.4 | Shared call/evidence DAG and hierarchy backend | Eager retained-call expansion, duplicated remapping and hierarchy construction. |
| v0.3.5 | Exact terminal target lowering | Rust terminal decomposition and its unchecked workspace rewrites. |
| v0.3.6 | Checked layout, workspace and resource summaries | Backend axis/allocation bookkeeping and duplicated cost calculation. |
| v0.3.7 | Bound OpenQASM/QIR emission | Rust output writers and post-check output reconstruction. |
| v0.3.8 | One native execution semantics path and bounded reference execution | Duplicated flat/hierarchical instruction and branch dispatch. |
| v0.3.9 | Entire supported backend chain integrated; retirement audit | Remaining production compatibility implementations; retain only delegating API adapters. |

### v0.3.0 prerequisite: fix contracts before patch-series replacement

Use [#131](https://github.com/MGYamada/Qleisli/issues/131) for the responsibility
and generic-contract architecture, and
[#250](https://github.com/MGYamada/Qleisli/issues/250) for source-language
unification. Specify artifact/profile versions, target capabilities, exact
phase/axis conventions, checked-result ownership, errors and resource groups.
Design a stable Rust facade so later patch releases can replace its internals.
This is not a prerequisite to finish every generic language feature.

The v0.3.1–v0.3.9 targets assume compatible implementation replacement.
The one-time v0.2.9 breaking exception does not authorize later PATCH breaks.
Public Rust types/methods, CLI envelopes, input profiles, seeded sampling and
capacity contracts must be inventoried before replacement. Put necessary
breaks into v0.3.0, or obtain a separately named MINOR migration; keep compatible
wrappers delegating to Lean meanwhile. A wrapper is not a second semantic
implementation. Do not silently change rejection limits to make migration pass.

### v0.3.1: transport, capacity and diagnostics

Resolve the bounded part of [#274](https://github.com/MGYamada/Qleisli/issues/274),
[#275](https://github.com/MGYamada/Qleisli/issues/275) and
[#278](https://github.com/MGYamada/Qleisli/issues/278) before adding many new
boundary crossings. Start with a finite batch per compilation; do not require
a persistent daemon or a reusable serialized success receipt.

Bind every item to its original artifact/request, source table, dependencies,
profile and product version. Check unused concrete bodies too. Shared source
storage can be decoded once within the invocation, but cannot discharge an
unchecked item. Bound batch bytes, per-item and aggregate work, output size,
execution time and cancellation; reject truncation, duplicate/missing item IDs,
cross-item receipt substitution and wrong versions. Do not publish a compiled
entry when another required declaration failed.

Return bounded native failure witnesses/locations so Rust can format useful
diagnostics without repeating semantic matrix calculations. Preserve diagnostic
contracts while retiring replaced branches of Rust counterexample extraction.
Profile decoding, checking, IPC and candidate generation separately. Begin with
the existing small benchmark clients and reduced shared-source cases; account
for all ten stress tests without newly running maximum-size cases. An ignored
failure is not a completed capacity fix. Do not raise deadlines as a substitute
for diagnosing complexity. See #278 for authorized stress-run conditions.

**Exit:** independent and batched native checks agree item by item on retained
inputs and faults; mixed success/failure batches cannot bypass any declaration;
diagnostic and resource behavior is reviewed. Delete replaced per-function
orchestration and diagnostic calculations, retaining a one-item batch adapter
where public callers need it. Record unresolved stress dispositions explicitly.

### v0.3.2: transformations bind input to output

Introduce a small shared backend contract: immutable input/output artifacts,
operation and profile IDs, original independent request, ordered ports, exact
type trees, dependency identities, workspace contract and bounded witness.
Keep the authoritative objects within the fresh native operation; serialized
IDs or hashes identify data but never substitute for checking it.

Move QIRF conversion and canonical output serialization into Lean. Prove or
independently validate the actual conversion relation for each supported
version, including retained meanings and source tables. Preserve exact bytes
for APIs promising unchanged emission; a canonical conversion is a separately
identified operation. A request-free conversion must still check the relation
between its original and resulting programs.

Use Bell/feedback and the retained function-contract examples. Mutate only the
output's phase, tuple shape, axes, evidence dependency or source binding;
also test replacing both artifacts while retaining another operation's receipt.
All must reject for the applicable relation, even if the output alone is legal.

**Exit:** output bytes come from the native result, and active conversion paths
do not reconstruct a second semantic result in Rust. Remove the replaced
production converter and view reconstruction; public raw inspection/proposal
decoding may remain explicitly non-authoritative. Execution users migrate in
later stages rather than losing their current API prematurely.

### v0.3.3: generic circuit algebra and local transformations

Move sequential/tensor composition, port remapping, adjoint, coherent control,
static repetition and a small specified set of local cancellations into shared
Lean backend operations. Reuse existing phase/layout definitions where their
domains match. Construct candidates separately from the checker of the actual
before/after relation. No QFT/QPE-name rule is needed for these operations.

State local preservation results over the actual executable pass/checker:
operator equality for pure circuits, instrument equality where observation is
admitted, or the exact encoding/clean-workspace equation. Keep global phase,
control polarity, nested tuples, zero-width owners and output order. Unitarity
does not grant inverse/control access; a matching probability distribution
does not establish coherent equivalence. Preserve explicit access premises.

Use [operation-contract examples](https://github.com/MGYamada/Qleisli/blob/main/examples/operation_contracts/main.qli),
small phase/inverse cases and the independent semantic fault corpus. Include a
global-sign error under control and an inverse with reversed output axes.

**Exit:** actual-definition lemmas and adversarial tests cover every enabled
rewrite. Delete replaced bodies in finite `circuit.rs`, `lower/transforms.rs`
and contract composition. Keep a compatibility signature only when it calls
the native operation. Exact reference arithmetic retained for independent tests
must not be mistaken for an accepted-program constructor.

### v0.3.4: shared calls, evidence and hierarchy

Use one backend representation of closed specializations, calls, port maps and
evidence dependencies across flat and hierarchical input adapters. Check graph
acyclicity, exact signatures, effects, independent contracts, source/root
bindings, both branches and simultaneous phi inputs. Share validated DAG nodes
within the invocation; do not validate an unbound nominal function name.

Preserve calls/repetition as shared nodes where supported. Do not solve Rust
debt by moving eager exponential expansion or global dense matrices into Lean.
Separate semantic work, expanded execution bounds and actual transport size.
Closed specialization is the scope; this does not adopt unrestricted recursion
or a new generic surface syntax.

Start with nested retained calls, the four earlier DAG examples, small sized
XOR/GHZ and [sized arithmetic](https://github.com/MGYamada/Qleisli/blob/main/corpus/sized/qualtran_arithmetic/README.md).
Then migrate Fourier/QPE candidate factoring through the same generic backend
interfaces. Algorithm theorems remain library/specification facts. An optional
recognizer can remain an untrusted producer; it cannot acquire acceptance power.

**Exit:** flat and hierarchy adapters share backend semantics and dependency
handling. Delete replaced Rust expansion/remapping/hierarchy-builder bodies and
production-only factoring machinery once generic replacement coverage exists.
Source elaboration and source-preservation obligations are recorded separately.
Retain existing Lean component proofs until the new composed path supersedes
their actual callers and obligations.

### v0.3.5: exact terminal target lowering

Prioritize [target rewrites](https://github.com/MGYamada/Qleisli/blob/main/src/interop/export.rs): they currently run after
acceptance and can change the program that an external runtime receives.
Implement a native target artifact and checker for the existing terminal gate
profile. Move deterministic decomposition into Lean; external synthesis search
may still propose circuits and witnesses.

Check the actual generated gates against the accepted input, ordered encodings
and workspace promise. Use the scoped equation `C E_in = E_out U` for pure
realizations, with explicit clean-zero embedding and arbitrary-reference
preservation. Distinguish isometries from same-width unitaries. Dirty workspace
requires its own stronger restoration relation; do not infer it from clean-zero
tests. Terminal observation additionally needs the relevant instrument relation.

Begin with existing H/CNOT/T, controlled phases, negative controls and exact
uncompute. The bounded Bell `LiftBasis` injection and small permutations are
the next profile in [#132](https://github.com/MGYamada/Qleisli/issues/132), after
the workspace/target contracts are fixed. Unsupported phase domains, synthesis
capabilities or non-square realizations remain explicit. No claim of general
Clifford+T synthesis follows from enumerating small basis tables.

**Exit:** a wrong phase, lost control, dirty return, stale input or understated
workspace fails before emission. Actual-definition proofs cover the enabled
decompositions/checkers. Delete the replaced Rust terminal rewrite bodies;
remaining profile extraction is a candidate adapter until stage v0.3.6.

### v0.3.6: layout, workspace and compositional resource bounds

Move ordered wire/owner maps, backend scratch allocation and measurement/result
layout into native checked transformations. Reuse layout/circuit-trace work but
also establish the operator/instrument connection needed by this target pass.
Physical remapping must bind both the original operation and final target ports.

Count logical inputs, source ancillas, backend ancillas, peak live workspace,
expanded steps and target gates separately. Check proposed counts against the
actual target artifact; check arithmetic overflow before allocation. Clean
release is justified by the realization relation, not an allocator flag.
Introduce scheduling/topology certificates only for an explicitly specified
target; this stage does not imply hardware timing or fidelity guarantees.

Use asymmetric wire labels, nontrivial output permutations, reference-entangled
inputs, both branch arms and a phase operation whose controls move. Reject
aliasing, early scratch reuse, reordered classical results, hidden ancillas and
understated counts. Keep limits coherent with the typed-capacity work in
[#94](https://github.com/MGYamada/Qleisli/issues/94).

**Exit:** native layout/workspace summaries describe the same immutable target
artifact that will be emitted or run. Retire Rust terminal-profile semantic
extraction, duplicate axis bookkeeping and backend cost reconstruction. These
local bounds are progress toward Resource Safety, not its general theorem.

### v0.3.7: native emission and final-byte binding

Generate the supported OpenQASM text and QIR text from the checked target
artifact on the native side. Keep serializers, target syntax and semantics
separate. Establish a parser/printer correspondence for the emitted restricted
language, or check an independently decoded output against that same target
artifact. Comparing output using the generator's own intermediate object is
insufficient. Bind gate symbols, operands, allocation, measurement/result order,
labels, target capabilities and the complete byte sequence.

Rust writes the returned immutable bytes atomically, without re-lowering or
reserializing them. LLVM assembly, bitcode conversion, foreign parsing and
hardware execution remain external operations. QIR bitcode verification by LLVM
alone proves neither QIS meaning nor preservation; either validate the decoded
bitcode relation or keep that route explicitly outside the checked-emission
claim. No full LLVM parser needs to enter the detector.

Use [foreign fixtures](https://github.com/MGYamada/Qleisli/tree/main/tests/fixtures/interop) and independent readers.
Mutate a QIS symbol, control, bit order, qubit index and a trailing instruction;
test substituted/truncated output and file-write failure. Preserve the current
supported import/export contracts and distinguish unsupported formats from a
failed semantic relation.

**Exit:** final emitted text is bound to the accepted input through the checked
pass chain. Remove Rust OpenQASM/QIR writer and target-extraction bodies. Foreign
readers can remain untrusted producers whose proposals traverse the same gates.

### v0.3.8: one execution path, with explicit numerical assumptions

Replace duplicated flat/hierarchy opcode, ownership-coordinate and branch/phi
dispatch with one native execution plan and interpreter for the supported
profiles. Start with a bounded exact reference evaluator for the existing
finite domain and reuse the native instrument components. Specify plan-to-input
correspondence and actual interpreter steps before routing public execution.

Do not assume that floating point, trigonometric evaluation, normalization or
randomness becomes exact when moved to Lean. Keep exact semantics and numerical
adapters distinct. External numeric acceleration may remain an untrusted
execution service; its output is not a kernel acceptance result. Every profile
must retain its stated numerical limits, error behavior and seeded sampling
contract. Wider dyadic phases need their own supported numeric/reference path;
an R8 evaluator does not cover them automatically.

Use Bell/feedback, reset/discard, reference correlations and
[iterative QPE](https://github.com/MGYamada/Qleisli/blob/main/examples/iterative_phase_estimation/README.md). Compare full
unnormalized branches, including zero branches, conditional states and visible
classical order. Test injected randomness and step limits. Samples alone cannot
replace an instrument comparison or establish physical execution correctness.

**Exit:** remove replaced production dispatch in `sim` and hierarchy execution.
Keep independent reference oracles in tests, and only the required I/O/numeric
adapter outside the native semantics path. If a public numerical profile cannot
yet be preserved, report the stage as partial rather than deleting its engine
or presenting numerical output as proved.

### v0.3.9: integrate and close the Rust retirement inventory

Exercise complete source/raw/foreign-to-native-backend chains through CLI,
Rust, Python and hierarchy APIs. No output can bypass an earlier relation by
being independently well-formed. Bind the final artifact to the original
request through every enabled pass; verify failure propagation, unused bodies,
source/dependency changes, version mismatch and output substitution.

For every Rust implementation listed above, record one of: deleted; public
facade delegating to Lean; untrusted producer outside acceptance; independent
test oracle; explicitly incomplete replacement. A copied Rust implementation
hidden in another production module is not retirement. No duplicate semantic
implementation may be retained merely as a fallback or cached receipt path.

**Exit:** all supported backend profiles have one production semantic path,
reviewed local preservation contracts, independent validation and final-byte
binding. Build/audit/replay the exact release source, validate installed crates
and relocated native bundles on supported platforms, and freeze source/binary
identities. The full backend-retirement claim requires zero incomplete entries;
otherwise publish the actual narrower scope and carry the remaining Issue.
No deadline authorizes deleting a required proof, test or supported path.

## What establishes each expanded boundary

For a pass from input `p` to output `q`, keep three distinct judgments:

1. The input satisfies the admitted profile and independently supplied contract.
2. The actual pass result or checked witness establishes the specified relation
   `R(p, q)`, including phase, axes, effects, dependencies and workspace.
3. The exact bytes/plan consumed by the next stage represent `q`.

Compose pass relations and their stated premises. Do not replace judgment 2
with independent legality of `q`. Do not define the expected meaning from the
producer's output or treat a Rust/Lean agreement as a specification. Reference
semantics stay independent of acceptance code, with explicit human review.

| Evidence | Claim it supports | Limit |
| --- | --- | --- |
| Independent small-system oracles, mutation tests, differential runs | Detect concrete implementation/specification disagreement | No universal preservation or completeness claim. |
| Fresh translation validation against an independent complete finite request | That admitted input/output instance satisfies the checked relation | Scope and the validator's own correctness remain explicit. |
| Local theorem over actual executable pass/checker definitions | The stated relation for all inputs satisfying its explicit premises | Does not automatically prove other passes, native compilation or the full source language. |
| Composed pass/serialization results | A longer preserved backend chain within the covered profile | Does not establish hardware behavior, general Resource Safety or full Qleisli Soundness. |

The v0.5.0 [Qleisli Soundness milestone](https://github.com/MGYamada/Qleisli/issues/202)
remains. These stages make concrete progress before it: remove duplicate code,
check more actual artifacts, prove local transformations, and test the host and
native paths independently. Formal gaps remain named gaps. Merely rewriting a
Rust pass in Lean receives no stronger correctness label.

## Common implementation and deletion gates

For each stage, use an Issue containing the input/output contracts, admitted
profile, actual executable definitions, expected local theorem or independently
checked relation, resource policy, affected APIs and exact Rust retirement list.
Record the bounded `.qli` client or raw fixture first under the
[session procedure](https://github.com/MGYamada/Qleisli/blob/main/tests/fixtures/authoring_sessions/README.md). Keep real
failed attempts, source snapshots and counterexamples beside their fixtures.

Require positive examples plus phase/control/axis/owner/effect/source/dependency
faults appropriate to the pass. Preserve the original 799 inputs and independent
oracles, while adding witnesses and mutations for the newly enabled relation.
The old replay alone cannot cover new backend functionality. Use small systems;
do not newly generate/check maximum-size cases without changed authorization.

Compile changed proofs, retain source/compiled declaration audits and perform
full replay for boundary-policy risks and releases. Keep Mathlib-free runtime
checking separate from `lean/` specification/complex-semantics proofs. No project
axioms, unsafe/partial definitions, native-evaluation axioms or runtime overrides
are introduced. Retire proof components only with replacement callers and
obligations, not because their corresponding Rust code disappeared.

Measure total latency, native launches, artifact bytes, visited DAG nodes,
shared-source decoding, peak memory and work limits on pinned small clients.
Batching, bounded DAG sharing and local witnesses should prevent the extension
from requiring whole-program matrices, repeated decoding or uncontrolled
expansion. Performance findings and semantic failures are recorded separately.

Keep Cargo build/docs independent of Lean; verification/backend work requires
an explicitly selected matching native runtime. New operations require explicit
protocol/profile compatibility and bounded replies. No runtime downloads or
Rust fallback. Test clean installation, relocation, missing/incompatible binary,
timeouts, partial replies and foreign-output failures at the boundary involved.

## Relationship to existing plans

This is a proposed acceleration of the backend portion previously grouped under
the v0.4.0 [implementation migration #273](https://github.com/MGYamada/Qleisli/issues/273)
and bounded target work in #132. Before implementing a stage, update those
Issues' scheduling and scope rather than creating duplicate backlogs. Their
compatibility, generic-contract and proof-separation requirements remain.

v0.3.0 still fixes the language/architectural contracts. Generic source syntax,
meta/elaboration tools, QLT/QDB/QCP and broad language growth are not implicitly
advanced into the patch series by moving backend code. v0.5.0 still owns the
full supported-profile Soundness composition and review. Physical Realizability
and Resource Safety remain separate theorem obligations, even after a checked
terminal backend and local workspace/resource relations exist.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
