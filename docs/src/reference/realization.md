# Realization, specialization and resources

This chapter specifies the 0.3.0 boundary between a program's meaning and a
claimed target implementation. It applies the adopted PR-2026-01 and RS-2026-01
[interpretations](../design/initial-interpretations.md) under the
[authority hierarchy](authority.md). It selects no concrete target schema,
universal gate set, synthesis algorithm or new source syntax. The current
implementation and proof limits are stated below.

The governing decisions are [#120](https://github.com/MGYamada/Qleisli/issues/120),
[#127](https://github.com/MGYamada/Qleisli/issues/127),
[#280](https://github.com/MGYamada/Qleisli/issues/280) and
[#281](https://github.com/MGYamada/Qleisli/issues/281). Their remaining
implementation and evidence obligations are not discharged by this chapter.

## Semantic validity and a target realization

Semantic unitarity states a property of the exact denotation. It does not
promise that the selected target can implement that operator, that synthesis
can find an implementation, or that the source's logical wires suffice.
Target synthesis failure must not reclassify a semantically unitary program
as non-unitary. Inverse and coherent-control access have their own contracts;
neither follows from finding one realization.

Physical Realizability is a **forward correspondence obligation**. For an
accepted closed instance `p`, a checked realization of the actual output
artifact `C` under profile `T` must implement the accepted meaning of `p`,
subject to its explicit interface, encoding and workspace premises. A claim
about a circuit that was considered during search does not cover a different
circuit subsequently emitted or executed.

Synthesis and search produce candidates outside acceptance. An independently
supplied candidate can qualify through the same checks; possession of a
complete synthesis algorithm for the entire semantic domain is unnecessary.
A failure to find a candidate is not evidence of impossibility. An
impossibility claim requires an obstruction whose hypotheses match the target.

Domain-wide existence or synthesis completeness is optional profile
mathematics. For example, Giles and Selinger's Theorem 1 establishes exact
Clifford+T synthesis with at most one clean ancilla for `2^n × 2^n` unitary matrices over
`Z[1/√2, i]`, using their specified gate and phase conventions. That result
neither grants arbitrary dirty workspace nor verifies a particular compiler's
output. See the [original theorem](https://arxiv.org/html/1212.0506v3#S2).

## Closed specialization

A generic definition describes a family. A **closed specialization** fixes
every choice needed to determine its meaning and interface:

- the resolved definition and complete dependency/source identities;
- ordered static arguments, including natural sizes and basis types;
- selected providers, their types, required capabilities and meaning bindings;
- all relevant static constraints and finite evaluation results;
- the declared constitutional edition and applicable semantic profile.

For a target claim, the realization also fixes the target/profile, ordered
layout and encoding, workspace contract and any target-dependent choices.
An unresolved parameter, capability, constraint or budget expression cannot
be treated as a successful concrete certificate. A spelling, bit width or
function name is not a specialization identity. The
[exact type tree](type-model.md#structural-equality-coherence-and-physical-maps) remains part
of that identity, including Unit factors and zero-width owners.

Generic checking must cover the generic body's admitted cases under its
declared premises. A favorable specialization cannot excuse an invalid generic
body or erase an obligation in an unselected branch. Conversely, a well-typed
family need not fit one fixed target at every parameter value.

A family theorem may quantify over all admissible substitutions. Its statement
must retain those premises; it must not describe one fixed finite circuit as
implementing an unbounded family. Static totality, computation of an instance's
resource bounds, and feasibility of those bounds on a target are separate
properties. The static language and specialization implementation remain
tracked in [#28](https://github.com/MGYamada/Qleisli/issues/28),
[#44](https://github.com/MGYamada/Qleisli/issues/44) and
[#47](https://github.com/MGYamada/Qleisli/issues/47).

## Workspace and exact correspondence

Source `clean`/`dirty` workspace is part of the author's program contract and
owner accounting. Backend workspace is additional implementation storage used
to realize that meaning. Backend storage does not become an implicit source
owner or permission to discard a source value. Its initialization, lifetime,
restoration and physical cost must appear in the realization claim.

For a clean-workspace unitary instance, a representative equation is

```text
(C ⊗ I_E)(encode_in ⊗ I_E)(|0>_W ⊗ ψ)
  = (encode_out ⊗ I_E)(|0>_W ⊗ (U ⊗ I_E)ψ)
```

Here `ψ` belongs to `L_in ⊗ E`, and `U` maps `L_in` to `L_out`.
The isometric encodings map `W ⊗ L_in` and `W ⊗ L_out` to the respective
physical interfaces; the reference `E` stays last and is untouched. Thus each
side uses the same explicit workspace/data/reference order. The equality is exact,
including scalar phase. `W` starts and finishes in the specified pure zero
state. A type width, owner name or an example input does not prove this
equation. For other encodings or differing input/output interfaces, the
realization must state its corresponding typed equation explicitly.

Dirty workspace requires the declared identity action on its unknown state
and all reference correlations. Returning its marginal state on a few inputs
is insufficient. Observing implementations require the complete unnormalized,
outcome-indexed instrument correspondence, including declared classical result
assembly; a normalized selected branch or matching measurement probabilities
cannot replace it. The exact clean/dirty requirements come from the adopted
QS interpretation and [#70](https://github.com/MGYamada/Qleisli/issues/70),
[#156](https://github.com/MGYamada/Qleisli/issues/156) and
[#157](https://github.com/MGYamada/Qleisli/issues/157).

Projective equality is different from exact operator equality. Dropping a
global phase can change a coherently controlled operation. The present exact
contract does not quotient by that phase. A different equality relation must
identify its boundary and compositional obligations explicitly; this chapter
introduces no approximate acceptance or error budget. Exact/approximate
profile decisions remain in [#31](https://github.com/MGYamada/Qleisli/issues/31)
and [#123](https://github.com/MGYamada/Qleisli/issues/123).

## Separate engineering approximation claims

The human-adopted **EXACT-2026-01** interpretation in
[#311](https://github.com/MGYamada/Qleisli/issues/311) governs this boundary.
An epsilon-bound approximation is an engineering synthesis or export claim,
outside edition-2026 constitutional semantic truth conditions. It cannot
replace exact source Meaning, semantic equality, phase/control, owner/effect
or clean/dirty restoration obligations. An approximation bound grants no
purity, inverse, control access or exact release capability.

A checked engineering claim must identify the exact ideal, actual artifact,
interface, target/profile, metric, finite bound, input/reference domain and
composition assumptions. Instrument claims must retain the complete public
outcomes and residual outputs with arbitrary external references. Sampling,
algorithmic resolution, synthesis and numerical-runtime information remain
distinct; an absent claim does not mean zero error. The bounded engineering
profiles below implement these contracts within their stated domains. They
define no universal approximation metric; target-resource certificates remain
separate work under #163.

Engineering receipts and their API/CLI claim kinds must remain mechanically
distinct from exact correspondence and resource evidence. Neither a small
bound nor a reported `epsilon = 0` bypasses the independent exact gates or
automatically discharges constitutional PR or target RS. An actual circuit
may independently obtain ordinary acceptance for its own exact meaning;
that acceptance does not identify its meaning with the source ideal.
Reusing engineering evidence through a Meaning or operation interface cannot
weaken that interface's exact promise.

Numerical, interval and approximate search methods may construct an exact
artifact or proof. That result remains eligible for the separate exact
correspondence and resource checks; the spelling of a search parameter does
not decide its claim kind. Conversely, exact cost accounting for an approximate
artifact does not supply its missing exact correspondence to the source.
No new interpretation, guarantee admission or broader QS/PR/RS discharge
follows from either engineering validation or this clarification.

The pure component checks a sufficient squared Frobenius
witness over canonical rectangular R8 matrices and a closed nonnegative dyadic
budget. Its proof bounds the explicitly selected Euclidean operator norm,
including arbitrary finite external references and literal scalar phase.
Witness failure does not establish that no approximation or synthesis exists.
The original-artifact component runs the existing exact PureLeaf check on each
body against its own independent matrix request before comparing those matrices;
both complete type trees and ordered ports remain checked. Neither component
changes the exact equality gate. A separate native engineering protocol binds
these components to the actual invocation and both retained host graphs. The
native composed instrument profile, target-resource gate and source-compiler
consumption of engineering claims remain unsupported. Mathematical instrument
composition and native ordered pure tensor composition are described below.
An engineering result does not establish source/target preservation.

### Native pure engineering comparison

```text
qleisli engineering compare-pure ACTUAL --against=REQUEST --lean-kernel=PATH --format=json
```

`ACTUAL` is an original finite QIRF artifact. `REQUEST` is a UTF-8 JSON request
containing the separate original ideal artifact, both independently specified
matrices and ordered ports, common complete domain/codomain type trees and a
closed canonical nonnegative dyadic budget. Each file is bounded to 16 MiB;
the QLV3 envelope retains its existing 64 MiB limit. The exact finite-matrix
carrier remains R8; no arbitrary-angle syntax or coefficient extension follows.

The request has exactly these fields:

| Field | Value |
| --- | --- |
| `format`, `version` | `qleisli.engineering-pure-request`, `1` |
| `claim_kind` | `engineering` |
| `metric` | `pure-euclidean-operator-norm-v1` |
| `checker_profile` | `frobenius-r8-pure-leaf-v1` |
| `target_profile` | `qirf-r8-pure-v1`, an IR profile rather than a hardware claim |
| `composition` | `single-component-v1` |
| `error_category` | `implementation-distance` |
| `domain`, `codomain` | Full QIRF Basis objects, for example `{"tag":"bit"}` |
| `actual`, `ideal` | Objects with exactly `input`, `output` and `matrix` |
| `epsilon` | `{"numerator":"7","denominator_bits":3}` means 7/8; use reduced signed decimal data, with zero encoded as `"0"` and exponent 0 |
| `expected_artifact` | Original UTF-8 ideal QIRF text, including its original byte spelling |

Ports and matrices use the existing native pure-leaf request encodings.
Unknown or missing fields, unsupported profiles, malformed or open budgets,
false body matrices and insufficient arithmetic/work capacity refuse. A
successful conservative witness is an inequality, not a completeness claim.
Hidden observation, reset or discard cannot acquire a pure label through this
path, even when the requested budget is large.

The Rust `interchange::engineering_pure` API constructs data-only requests and
returns a private, allocation-bound `EngineeringPureReport` after a fresh
native check. Its serialized convenience entry independently decodes the same
typed request. Both original artifacts receive their ordinary checks and then
fresh independent pure checks against their own matrices; Lean compares the
typed context and both fresh graphs with the actual retained Rust execution
description. Inspection and caller scopes refuse this mode. The engineering
response uses a distinct header and cannot enter an exact accepted-handle
constructor. The report has no conversion to `AcceptedProgram`, Meaning,
control/inverse access, cleanup or resource evidence, including at epsilon 0.
Serialized CLI output is an inert report, never reusable native acceptance.

Text and JSON identify the engineering metric, bound, profiles, composition,
original artifact/request digests and selected checker path. Checker identity
remains unpinned under the existing provenance limitation. Hashes identify
reported bytes, not native binary correctness or human authority. Sampling,
algorithmic resolution and numerical-runtime errors are separately `not-claimed`;
they are not silently zero. Source preservation, exact source correspondence,
instrument bounds and target-resource bounds remain explicitly unestablished.

Pure composition proofs establish additive sequential and ordered tensor error
rules for the same Euclidean metric under the stated exact isometry premises,
including arbitrary references. The coherent-control corollary additionally
requires equal domain/codomain and the existing independent access meanings.
These mathematical rules do not change the single-component profile or supply
compiler/lowering preservation. The separate ordered-tensor profile below
checks its own original parent artifacts and component comparisons.

### Native ordered pure tensor comparison

```text
qleisli engineering compare-pure-tensor ACTUAL --against=REQUEST --lean-kernel=PATH --format=json
```

This profile combines exactly two ordered pure comparisons. It checks six
original QIRF artifacts afresh: actual and ideal parents, actual and ideal left
components, and actual and ideal right components. Each body retains its own
dependency order, exact matrix request, ordered ports and full type trees.
Both parent interfaces are the complete products of the component interfaces;
`Unit` nodes are retained even when they occupy no physical wires.

The exact parent equations use the existing low-first coordinates
`left + left_dimension * right`. Both parent matrices must equal the ordered
tensors of their respective component matrices. The checker then adds the two
closed component bounds exactly and requires equality with the explicitly
requested total bound. It does not repeat the sufficient whole-parent
Frobenius inequality: an additive component certificate may succeed when that
whole-matrix witness is too loose. All six body checks, component inequalities,
parent equations and bounded addition share one remaining-work counter.

The request has exactly fourteen top-level fields:

| Field | Value |
| --- | --- |
| `format`, `version` | `qleisli.engineering-pure-tensor-request`, `1` |
| `claim_kind` | `engineering-pure-tensor-bound` |
| `metric` | `pure-euclidean-operator-norm-v1` |
| `checker_profile` | `tensor-additive-r8-pure-leaf-v1` |
| `target_profile` | `qirf-r8-pure-v1` |
| `composition` | `ordered-tensor-two-v1` |
| `error_category` | `implementation-distance` |
| `actual`, `ideal` | Parent leaf objects with exactly `input`, `output`, `matrix` |
| `left`, `right` | Component objects described below, in that order |
| `epsilon` | Canonical nonnegative dyadic, exactly the sum of the two component budgets |
| `expected_artifact` | Original UTF-8 ideal parent QIRF text |

Each component object has exactly `domain`, `codomain`, `actual`, `ideal`,
`epsilon`, `actual_artifact` and `expected_artifact`. Types, leaf requests and
budgets use the single-component encodings; both artifact fields contain the
original UTF-8 QIRF text. Parent type trees are derived from the ordered
components, rather than supplied as width-only claims. Missing or extra
components, altered profiles, noncanonical or open budgets, a stale total
budget, false body matrices or parent tensor equations, and arithmetic/work
exhaustion refuse. Existing per-file, envelope, matrix and work limits apply.

The dedicated QLV3 invocation accepts execution scope only. Lean compares its
freshly decoded typed request and all six graphs with the retained Rust QDV1
view in parent-actual, parent-ideal, left-actual, left-ideal, right-actual,
right-ideal order. The private Rust report binds the immutable artifacts,
original request and selected checker path. A changed component, matrix,
budget or parent cannot reuse it. Text and JSON report this engineering bound
and its composition profile, with the same separate unclaimed error categories
and preservation/resource disclosures as the single-component result.

The checked additive operator bound extends to every finite external reference,
including entangled inputs, under the freshly checked exact isometry premises.
It supplies no exact equality between the parents, source preservation,
controlled/inverse access, cleanup, emitted-target correspondence or resource
certificate, including at total epsilon zero. Recursive, sequential, controlled
and instrument native composition remain separate unsupported paths; this
two-component profile supplies only its stated additive engineering bound.

### Instrument engineering comparison

The instrument component uses a **complete adjoint Euclidean operator
bound**. For actual and ideal Kraus families, it bounds the difference between
their adjoint actions on every joint observable family `B`, for every finite
external reference `R` and classical input `x`:

```text
norm(sum_y,h (K_actual[x,y,h] tensor I_R)^dagger B[y]
             (K_actual[x,y,h] tensor I_R)
   - sum_y,k (K_ideal[x,y,k] tensor I_R)^dagger B[y]
             (K_ideal[x,y,k] tensor I_R)) <= epsilon * norm(B)_infinity
```

The norms on operators are explicitly Euclidean operator norms; the family
norm is the supremum over public outcomes. Hidden-history sets may differ.
This quantifies joint observables, including reference correlations, without
a reference-dimension factor or branch renormalization. The metric is not
advertised as a diamond norm without a separate norm-duality proof.

The sufficient witness assigns a canonical nonnegative closed dyadic `q` to
every complex CP-coefficient difference, in fixed order: public outcome,
output row, input column, other output row, other input column. All actual and
ideal public labels contribute; absent labels denote zero. Each coefficient
is freshly reconstructed from all matching hidden histories. Existing exact
R8 arithmetic checks its squared magnitude against `q*q`, and exact summation
checks `sum(q) <= epsilon`. Both `q` and `epsilon` have unsquared norm units.
Witness length is exact. Malformed dimensions/coefficients, noncanonical or
negative budgets, insufficient witnesses and arithmetic/work exhaustion refuse.
A remaining-work preflight precedes Cartesian witness allocation. Its work
counter bounds verification, separately from program or target resources.

The original-graph wrapper reuses ordinary root/dependency checks, requested
complete signature equality, ordered result projection, principal Observe
checks and complete Kraus/Gram reconstruction on both bodies. Its current
profile has one quantum input owner, empty classical inputs and the existing
bounded dense reconstruction. Requested source/type trees remain distinct
from source-to-IR preservation. The independent metric also defines general
finite classical input families for subsequent composition work.

The dedicated native request has fourteen fields: `format`, `version`,
`claim_kind`, `metric`, `checker_profile`, `target_profile`, `composition`,
`error_category`, `actual_signature`, `expected_signature`, `identity`,
`epsilon`, `majorants` and `expected_artifact`. Its format is
`qleisli.engineering-instrument-request`, version `1`, with claim kind
`engineering-instrument-bound`, metric
`complete-adjoint-euclidean-operator-norm-v1`, checker profile
`choi-l1-r8-instrument-v1`, target profile `qirf-r8-instrument-v1`, composition
`single-component-v1` and error category `implementation-distance`.
Other profiles and extra/missing fields refuse. Bounds use the existing closed
dyadic data, for example `{"numerator":"1","denominator_bits":2}` for `1/4`.
The target names an IR profile, not hardware. No producer-supplied outcome
labels, matrices, probabilities or success flags replace reconstruction.

The Rust request uses validated `InstrumentSignature`/`InstrumentResult` data,
and its private `EngineeringInstrumentReport` retains both immutable artifacts,
the original request and selected checker path. The native QLV3 invocation
accepts execution scope only and compares both fresh graphs, signatures,
identity and complete budget/witness data with the Rust execution view.
Inspection, caller scopes, old outer frames, cross-kind replies and
missing/incompatible/failed checkers refuse without fallback.

```text
qleisli engineering compare-instrument actual.qirf --against=comparison.json --lean-kernel=PATH
```

Text and `--format=json` disclose the complete instrument bound, actual input
digests and unpinned checker identity. Pure phase agreement, source preservation,
inverse/control, cleanup, resources and constitutional PR/RS remain
unestablished, including at epsilon zero. Sampling, algorithmic resolution and
numerical runtime error are separate unclaimed categories. The pure comparison
continues to report instrument bounds as unestablished.

Independent mathematical composition uses the actual Kraus families. Full Gram
completeness implies adjoint contraction at every finite reference. A literal
pure operator gap `delta` and both pure Gram equations imply the one-way
instrument bound `2*delta`; no phase information is recovered. Feed-forward
composition retains public `(y,z)` outcomes and hidden `(h,k)` histories.
Ordered tensor composition retains the declared left/right input/output,
public and hidden products through explicit proved reference regrouping.
Both constructions have additive `epsilon_1 + epsilon_2` bounds under their
stated component bounds and Gram premises. Separate completeness theorems
require both original Gram equations; a bound alone does not establish them.

These results provide no source epsilon annotation, compiler consumption or
original source/QIRF composition-preservation proof. The native profile remains
single-component: it does not issue a composed certificate. Emitted target-byte
comparisons require the separate bounded profile below. Target-resource
certification remains unfinished under #163; this profile supplies no such claim.
No instrument bound grants pure phase agreement, coherent control, inverse,
exact release or constitutional PR/RS authority.

### Literal OpenQASM target comparison

```text
qleisli engineering compare-openqasm3 TARGET --against=REQUEST --lean-kernel=PATH --format=json
```

`TARGET` contains the actual emitted bytes. The closed profile accepts this
literal ASCII structure, with zero to eight ordered gate lines between reset
and measurement, and a final newline:

```qasm
OPENQASM 3.0;
include "stdgates.inc";
qubit[1] q;
bit[1] c;
reset q;
h q[0];
c[0] = measure q[0];
```

Each gate line is exactly `h`, `x`, `y`, `z`, `s`, `sdg`, `t` or `tdg`, followed
by ` q[0];`. The profile bounds the target to 1,024 bytes and eight gates.
Changed whitespace, headers, includes, operands, additional results, gates
after measurement and unsupported syntax refuse. The include line is a fixed
token; checking loads no external include file. This deliberately bounded
profile is not a general OpenQASM parser or hardware-conformance claim.

The independent byte reader imports the existing Raw meaning data without
acceptance definitions. Its ordered gate word constructs the actual instrument:
consume an explicit zero-width `Q<Unit>` owner, initialize one qubit, apply the
word, then consume that qubit with terminal Z measurement. The full interface
is exactly `Unit -> Bit`, with a classical result and principal Observe effect.
Equal widths do not admit `Bits<0>`, products of Unit or other result trees.
This closed terminal experiment grants no open pure or controllable map.

The standard gate interpretation is an explicit specification assumption.
The adapter reuses existing exact Raw/std meanings; it introduces no new
semantic primitive or constitutional interpretation. Kernel-checked matrices
and the original-body bridge preserve H's sign, literal Y phase, S/SDG direction
and T/TDG direction before the terminal observation. This does not adopt a new
external reference specification or prove general OpenQASM execution semantics.

`REQUEST` has the same fourteen field names and signature/identity/dyadic
encodings as the instrument request above, with these distinct fixed values:

| Field | Value |
| --- | --- |
| `format`, `version` | `qleisli.engineering-openqasm-request`, `1` |
| `claim_kind` | `engineering-target-instrument-bound` |
| `metric` | `complete-adjoint-euclidean-operator-norm-v1` |
| `checker_profile` | `canonical-target-choi-l1-r8-v1` |
| `target_profile` | `openqasm3-canonical-one-qubit-terminal-r8-v1` |
| `composition` | `single-component-v1` |
| `error_category` | `implementation-distance` |

Both complete signatures must equal the fixed interface. `expected_artifact`
retains the independently supplied original ideal QIRF, including all original
dependencies; no fixed H ideal or producer-supplied actual matrix substitutes
for it. The unchanged exact instrument gates reconstruct both complete Kraus
families and Gram equations before checking the closed epsilon and every Choi
coefficient majorant. The complete-adjoint bound covers every finite external
reference and joint observable, without branch normalization.

The native `--engineering-openqasm-check` mode accepts execution scope only.
Its QLV3 body contains literal target bytes; its QDV1 comparison binds the typed
request, original byte array, ordered word, generated actual graph and original
ideal graph. Decoding is charged before traversal and shares remaining work
with the ideal reader, exact instrument reconstruction and metric check.
Missing, incompatible, failed or cross-kind checkers cannot fall back.

The private `EngineeringOpenQasmReport` retains immutable target/ideal/request
bytes, full contract and checker path. Its actual graph is data, without a Rust
accepted-program constructor. Text/JSON report the target-bound instrument
inequality and actual digests. Sampling, algorithmic resolution and numerical
runtime errors remain separately unclaimed. Source/export preservation, exact
source correspondence, pure phase agreement, inverse/control, exact cleanup,
target resources and constitutional PR/RS remain unestablished even at epsilon
zero. This comparison supplies no resource certificate for #163.

## Quantitative resource claims

A resource certificate must identify the actual closed instance, emitted
artifact, target/profile, resource measures, schedule or interpretation of
those measures, and checked bounds. Changing providers, layout, target,
workspace or output bytes invalidates reuse unless checked correspondence
establishes the new claim. A content hash establishes identity, not the bound.

Physical live width includes logical data, explicit source workspace,
backend synthesis workspace and routing/target storage. Count actual physical
locations once, accounting for their lifetimes and permitted reuse. Peak
width is the maximum simultaneous live count; a sum of separate peaks is a
conservative upper bound, not necessarily the realized peak. Logical width
alone does not bound the physical implementation width.

Gate count, depth and non-Clifford cost require declared target conventions.
Literal IR T-word counts are not automatically physical or optimal T counts.
Compiler memory, checker work limits, static termination, ownership safety
and target resource bounds are different claims. In particular, the existing
ownership-only predicate does not discharge quantitative RS.

An admitted symbolic family bound may strengthen RS within edition 2026.
It still needs the corresponding current proof and actual compilation/resource
binding. Before certifying a newly admitted family or construct whose resource
behavior lies outside current coverage, its corresponding bound and preservation
obligations must be discharged; existing guarantees remain in force.
Failure to meet a target budget rejects that target claim, without
changing the program's mathematical denotation. QCP implementation and concrete
target schemas retain their separately scheduled scope in
[#103](https://github.com/MGYamada/Qleisli/issues/103); this chapter is not their
implementation. Phase-aware target cost is tracked in
[#165](https://github.com/MGYamada/Qleisli/issues/165).

## Small obstruction examples

Embedding a `k`-qubit gate `G` into `n` wires, under a fixed ordered basis,
gives determinant `det(G)^(2^(n-k))`. Determinants multiply under composition.
Consequently a target generator set restricts same-wire determinants.
This is a necessary obstruction; sufficiency requires a separate theorem for
that precise generator, phase and workspace profile.

The repository retains two exact small examples:

| Operator | Semantic property | Same-wire obstruction for the stated profile |
| --- | --- | --- |
| Positive-exponent three-qubit Fourier operator `F8` | Unitary, with `det(F8) = i` | The embedded H/T/X and NCT generators considered by the regression have determinants only `±1` on three wires. |
| Four-bit `c3x` basis permutation | A bijection with one transposition, hence determinant `−1` | Those embedded generators have determinant `+1` on four wires. |

Both programs remain semantically accepted. The regression
`tests/static_semantics.rs::review_same_wire_obstructions_do_not_reject_semantic_unitaries`
checks the original four-bit table, the complete exact F8 operator and the
embedded-generator determinant calculation. Its retained source is
`tests/fixtures/review_v023/c3x.qli`. These examples do not establish a universal
obstruction for other target vocabularies, arbitrary controlled gates or a
profile that permits additional workspace.

## Current production status and diagnostics

The [production inventory](production-boundary.md) identifies actual native
acceptance, proposal, execution and export routes. Ordinary native acceptance
does not itself issue a target realization or resource certificate. The two
admitted QLV1 guarantees cover original-root ownership and classical scope;
they do not certify source lowering, target emission or quantitative bounds.

The current terminal exporter in `src/interop/export.rs` performs bounded
untrusted rewrites after program verification. A borrowed cursor expands actual
retained function circuits, including nested controls, adjoints and ordered axis
maps, before merging adjacent diagonal actions. Contract expansion shares the
existing 1,000,000-step function limit across the whole export; this is a producer
work limit, not a target-resource bound. Flat input and emitted-gate limits remain
unchanged. The exporter explicitly allocates and uncomputes conjunction scratch
and rejects output exceeding its physical qubit capacity. A nontrivial
uncontrolled scalar still has no terminal-gate realization in this profile.
The independent `scripts/test_review_v024.py` oracle checks
emitted small QFT/control circuits, including complex phase, output axes and
zero-return scratch. Such bounded numerical validation is distinct from a
general transformation proof or resource certificate. External schema entries
remain disabled until their binding gates are completed.

Diagnostics for a failed realization/resource claim must identify the closed
instance, requested profile and failed premise, and distinguish a proved
obstruction from unsupported synthesis or exhausted checking capacity. An
unsupported target operation or target-width error must not be presented as
failure of semantic unitarity. The current exporter already reports unsupported
operations and the synthesis-workspace capacity limit; a general specialization
certificate, profiler and obstruction diagnostic are not implemented by those
messages. Pending diagnostics and release evidence remain part of
[#48](https://github.com/MGYamada/Qleisli/issues/48),
[#120](https://github.com/MGYamada/Qleisli/issues/120) and
[#127](https://github.com/MGYamada/Qleisli/issues/127).

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
