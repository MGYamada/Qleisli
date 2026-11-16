# Realization, specialization and resources

This chapter specifies the 0.3.0 boundary between a program's meaning and a
claimed target implementation. It applies the adopted PR-2026-01 and RS-2026-01
[interpretations](../design/initial-interpretations.md) under the
[authority hierarchy](authority.md). It selects no concrete target schema,
universal gate set, synthesis algorithm or new source syntax. The current
implementation and proof limits are stated below.

The governing decisions are [#120](https://github.com/MGYamada/Qleisli/issues/120),
[#121](https://github.com/MGYamada/Qleisli/issues/121),
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

## Observing instruments on a target

The [source instrument judgment](source-text.md#instruments-and-ordinary-feed-forward)
defines the complete outcome maps of an `Observe` expression. Realization
requires a separate judgment for its closed instance, the selected target
profile and the actual emitted artifact. The judgment fixes the ordered quantum
and classical interfaces, logical encodings and projection of target records to
source outcomes. It accounts for the initialization and disposition of every
additional physical owner.

For each ordinary input `x` and declared outcome `c`, let `Φ[x,c]` be the
source map and `Ψ[x,c]` the emitted instrument's map after the declared record
projection. The projection assigns every target history to exactly one source
outcome, including histories with records hidden from the source. With the
declared input and output encoding channels `E_in` and `E_out`, the exact
obligation is

```text
(Ψ[x,c] ⊗ id_R)((E_in ⊗ id_R)(ρ)) =
(E_out ⊗ id_R)((Φ[x,c] ⊗ id_R)(ρ)).
```

It holds for every finite external reference `R` and every joint input
`ρ` at the complete source interface. The unnormalized maps fix both outcome
probabilities and the residual quantum state on the declared retained owners.
The correspondence includes consumed owners, the order of all remaining
owners and the action of every branch that contributes to a public outcome.

The evidence states how the profile realizes each required measurement basis,
where measurements can occur, which owners remain live, and how reset or
repreparation obtains its stated output. For feed-forward it identifies the
available classical outcome, conditional operations and any dynamic control,
scheduling or latency assumptions needed for the branch to execute with the
specified live owners. Classical feed-forward selects a branch using a
classical outcome. Coherent control instead acts on a live quantum selector and
must preserve coherence between its sectors. Each needs its own realization
evidence.

Destructive readout accounts for the consumed owner. A retaining instrument
requires the declared output owners and their conditional quantum state.
A readout-and-prepare implementation qualifies only if the full correspondence
equation holds. For example, measuring both data qubits in Z and reporting
their parity has the same classical distribution as
[`std::measurement::parity_zz`](stdlib.md) on an even Bell state. The two
readouts lose the coherence between `00` and `11`, whereas the retaining parity
projector preserves it. Preparing computational-basis replacements leaves
that difference in the even outcome map.

A terminal-readout-only profile may refuse a target claim that requires
mid-circuit measurement and conditional quantum action. Missing capability or
missing evidence is a target-lowering failure, so the source retains its
instrument, type and effect. Any engineering approximation requires the
[explicit separate claim below](#separate-engineering-approximation-claims)
under [#31](https://github.com/MGYamada/Qleisli/issues/31). This abstract
obligation from [#124](https://github.com/MGYamada/Qleisli/issues/124) is an
input to the future [target capability schema](https://github.com/MGYamada/Qleisli/issues/179).
QCP or another backend can express the premises using its own profile
vocabulary. Source semantics are defined independently of that vocabulary.

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

Terminal export can identify the closed specialization and original source
expression when a rejected operation has a single retained origin. This includes
steps from an explicit clean or dirty workspace body. When a rewrite combines
several expressions, the enclosing Raw operation can provide its own origin.
For a failed native workspace equation, the checker supplies the original Raw
interval and the host checks it against the retained workspace. The diagnostic
can name the enclosing specialization or a single specialization shared by
all steps in the checked body. Packet-wide errors and ambiguous bodies leave
the specialization unspecified.
Imported artifacts have no original project diagnostics.

## Logical axes and physical placement

The logical interface records the ordered axes of each owner using the exact
[source type trees](type-model.md#structural-equality-coherence-and-physical-maps).
A physical layout assigns the live axes to target locations. For example,
the ordered pair of logical axes can occupy physical locations `(17,4)`.
The first axis remains the first logical axis. Nested products and `Bits<n>`
retain their declared axis and owner order. A zero-width owner retains its
interface identity and contributes no physical location.

A target realization records the initial and final placement or their
equivalent ordered encodings. For a pure instance with semantic action `U`
and actual target action `C`, a correspondence with encodings `E_in` and
`E_out` has the form `C ∘ E_in = E_out ∘ U`. The encodings include the
specified workspace and its boundary state where required. The equation
extends to arbitrary joint inputs with an untouched reference. Observing
realizations use the [outcome maps above](#observing-instruments-on-a-target)
and record the placement and disposition of the owners still live at each
interface, including any retired locations where the profile supports them.

Routing may change the placement from `(17,4)` to `(4,17)` by an emitted
physical SWAP, provided the evidence tracks each logical axis into its
new location. The SWAP contributes to the target cost. A metadata relabeling
changes the description of the layout and leaves the physical state in place.
The encoding evidence must justify that relabeling. A source-level axis
permutation changes the logical action and must be included in `U` with its
specified order and phase. An emitted implementation of a logical SWAP must
realize that action under its declared encodings.

The placement evidence identifies each routing step and accounts for the
live locations used by routing and synthesis workspace. The target model
may expose this relation to QCP routing analysis. The [future target capability
schema](https://github.com/MGYamada/Qleisli/issues/179) consumes the abstract
correspondence required by [#126](https://github.com/MGYamada/Qleisli/issues/126).
The current [bounded routing checker](#quantitative-resource-claims)
covers literal physical SWAP intervals and their stated placement premises.

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

For the finite one-scratch checker, the application proof
`WorkspaceTargetAction.clean_checked_separates` uses the exact checked
insertion and output coefficients with QPTL's fixed-scratch law. The joint
output density has support only in the zero-scratch block, for every input
density on data and a reference. The companion
`WorkspaceTargetAction.dirty_checked_promotion` binds every coefficient of
the actual body to the logical operator promoted on the ordered data axes.
`WorkspaceTargetAction.dirty_checked_reference` then applies that action
to each joint reference column and proves that every selected input
coordinate retains the output's scratch bit.

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

## Controlled target realizations

The coherent Meaning of `controlled(U)` is the ordered direct sum
`I ⊕ U` with inactive sector zero and active sector one. Semantic unitarity
establishes the operator property of `U`. The static `Controllable(U)`
judgment separately governs source use under the
[operation type rules](type-model.md#general-pure-operation-arrows).
Target lowering additionally requires a checked realization of the exact
direct sum on the selected target.

For transparent implementations, a structural derivation must check each
original gate or named implementation with its control, dependencies, axis
order and exact phase. The implementation must act as identity in the
inactive sector and implement the requested operation in the active sector.
Composition and powers can compose those exact sector equations when the
interfaces and control match. QPTL proves the corresponding operator
identities in `controlled_mul` and `controlled_pow`. Provider calls and
controlled powers used by QPE carry the same obligations.

A realization certificate binds the original operation and Meaning, the
actual emitted implementation, the target profile, and the ordered control,
data and workspace encodings. It identifies where native controlled gates
are used and where additional synthesis steps are needed. Physical counts
include workspace preparation, live width, restoration, generated inverse
steps and routing when required by that implementation. An opaque provider
requires explicit controlled evidence bound to the requested operator and
the emitted artifact.

A scalar phase multiplying only the active block changes its phase relative
to the inactive block. QPTL's `controlled_phase_ne` proves the change for
any nontrivial scalar on a nonzero operator. Projective agreement or channel
equality for the uncontrolled operation therefore cannot supply the
controlled equation. An engineering approximation to a controlled operator
must bound its error against the intended controlled Meaning itself and
retain the exactness distinction below.

## Isometries and initialized target interfaces

A semantic isometry `V: A -> B` satisfies `V† V = I_A`. The basis trees
of `A` and `B` can differ, including in width. A realization of
`Op<A -> B>`, or its refinement `Op<A -> B, M>`, retains both exact
ports and the requested Meaning. Sequential composition matches the middle
tree exactly. Tensor composition preserves the declared order of both ports.

For a target that implements the isometry with a unitary dilation, let
`E_in: A -> P_in` and `E_out: B -> P_out` be the exact input and output
isometric encodings, and let `C: P_in -> P_out` be the action of the actual
target circuit. On every joint input `ψ` with external reference `R`,
the realization must establish

```text
(C ⊗ I_R)(E_in ⊗ I_R) ψ = (E_out ⊗ I_R)(V ⊗ I_R) ψ.
```

The input encoding specifies any initialized backend wires and their ordered
placement. The output encoding identifies the retained logical output and
fixes the state of every backend wire claimed to be returned clean. Other
physical degrees of freedom require an explicit output contract. Isometry
typing introduces no implicit discard or partial trace. Source `clean` and
`dirty` contracts bind source owners separately. A target claim accounts for
every physical wire used by the dilation, including initialized backend
workspace, plus the preparation, realization, cleanup and routing required
by the selected target model. A dilation existence theorem supplies a
candidate. The accepted artifact still requires the displayed correspondence.

The mathematical adjoint reverses `V` on its image. On the full output space,
`V V†` is the projector onto that image. For an exact unitary dilation,
`C† E_out V = E_in`, including under arbitrary external reference, so an
available checked reverse circuit recovers the encoded input on that image.
An application outside the established image needs its own contract. The
static `Adjointable` capability and physical realization of a reverse
operation require independent evidence under the
[operation type rules](type-model.md#general-pure-operation-arrows).
The QPTL theorem `dilation_recover_reference` derives the image-restricted
equation from the exact forward square and the unitary implementation law.

## Exact target-domain membership

`M ∈ ExactDomain(P)` is an abstract judgment about the requested exact
Meaning `M` and a specified target profile `P`. Its evidence identifies the
profile and version, literal gate vocabulary, coefficient and parameter
domain, ordered interface, and phase convention. It also states the admitted
initialization, encoding, workspace and restoration assumptions. Same-wire
and clean-workspace profiles can therefore have different exact domains.

Physical Realizability requires evidence of this premise for an accepted
exact target realization. A checked exact witness for the profile can
establish membership and bind the actual emitted artifact to the same
Meaning. An existence theorem or coefficient test can support this judgment
within its own hypotheses. A necessary condition alone does not authorize a
candidate. A search failure or capacity refusal leaves the claim unproved.
A target-domain refusal concerns the requested realization; the source
retains its exact meaning and typing.

For a profile whose gates and computational-basis coordinates have
coefficients in `Q(ζ8)`, every entry of the gate product lies in that field.
Appending clean zero workspace and taking the corresponding returned
coordinate selects entries of the same product. A controlled phase of one
sixteenth of a turn has coefficient `ζ16` at its active diagonal entry,
which is outside `Q(ζ8)`. The obstruction applies for any number of such
clean axes. The QPTL theorem `extracted_sixteenth_ne` proves the coefficient
obstruction. A target with a declared native sixteenth-turn gate requires
its own exact-domain evidence. The existing eighth-root execution profile
reports an unsupported exact phase for such a request.

Engineering approximation requires an explicit separate claim with the
applicable metric, closed budget and actual artifact correspondence, as
specified below. A failed exact request does not choose that path implicitly.
This judgment is independent of any eventual QCP implementation and can be
used by the future [target capability schema](https://github.com/MGYamada/Qleisli/issues/179).
The domain boundary is tracked in [#123](https://github.com/MGYamada/Qleisli/issues/123).

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
define no universal approximation metric. The bounded literal OpenQASM
resource profile below uses its own closed engineering budget.

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
source correspondence, pure phase agreement, inverse/control, exact cleanup
and constitutional PR/RS remain unestablished even at epsilon zero. Version 1
checks the instrument bound alone.

### Literal OpenQASM engineering resource limits

Version 2 of the same request uses claim kind
`engineering-target-instrument-resource-bound` and adds one required field.

```json
"resource_limits": {"model":"openqasm3-one-qubit-literal-gates-v1","gates":2,"t_gates":2}
```

Both limits are closed integers from 0 through 8. `gates` bounds emitted gate
lines and `t_gates` bounds the subset `t` and `tdg`. The required literal
header, reset and terminal readout fix one reserved qubit, one reset and one
measurement. This model charges the literal one-qubit vocabulary and excludes
compiler work, synthesis search, hardware timing, and cross-component
composition. The metric, epsilon and single-component contract stay required.

Lean checks the limits against the independently decoded word used for the
engineering instrument inequality. The typed execution view includes the
model and limits. Text and JSON reports include the checked counts and limits
with the identities of the actual artifact, original ideal and request.
Changing any of them requires a fresh comparison. A timed-out or rejected
check emits no certificate. The engineering receipt cannot supply exact
cleanup, phase-sensitive coherent control, or constitutional PR/RS. See
[#163](https://github.com/MGYamada/Qleisli/issues/163).

## Quantitative resource claims

A resource certificate must identify the actual closed instance, emitted
artifact, target/profile, resource measures, schedule or interpretation of
those measures, and checked bounds. Changing providers, layout, target,
workspace or output bytes invalidates reuse unless checked correspondence
establishes the new claim. A content hash establishes identity, not the bound.

The [provider resource contract](functional-boundary.md#provider-selection-and-quantitative-resource-evidence)
applies to each selected body and composition. An external, opaque or
device-native implementation must meet the same admission requirements.

Physical live width includes logical data, explicit source workspace,
backend synthesis workspace and routing/target storage. Count actual physical
locations once, accounting for their lifetimes and permitted reuse. Peak
width is the maximum simultaneous live count; a sum of separate peaks is a
conservative upper bound, not necessarily the realized peak. Logical width
alone does not bound the physical implementation width.

A fixed-occupancy SWAP segment records the ordered placement of all
occupied locations, including any source, synthesis and routing scratch
that is live during the segment. Each literal SWAP must name two distinct
occupied locations connected in the declared profile. It moves both
locations in the placement, leaves every other location alone, and counts
as one operation even when a later SWAP cancels it. The final placement
preserves logical axis order and exact joint coefficients with any
reference. The Lean component independently decodes the declared register
width and the literal SWAP instructions from a designated byte interval
of canonical OpenQASM output. It also checks the target capacity.
A complete certificate still establishes that the interval is used for
routing and that its entry placement is correct. It also checks the other
target operations, allocation, release and reuse.

The canonical terminal profile reserves all declared physical locations
and resets them before its first gate. It retains the reservation through
terminal measurement. The independent complete-artifact reader counts
reserved and reset wires, gates, literal SWAPs, T/TDG and measurements from
the output bytes. An exact finite workspace check can also compare a
designated gate interval with the independently checked original clean or
dirty body. The comparison uses the declared ordered data/scratch placement
and requires the physical register to cover the checked Raw peak. The checker
can derive the workspace's ordered locations from the checked original Raw
frame and its complete injective physical placement. A fresh scratch must
occupy a location absent from that frame. For a fresh scratch wire, the
checker can verify that nothing touches it between the initial reset and
workspace entry, or after exact restoration. This profile keeps the physical
reservation throughout.

For a closed straight-line Raw prefix with zero preparations, structural
owner operations and finite gates, the checker derives this frame by
replaying the original prefix and the decoded target gate word. Marked
routing operations must match connected physical SWAPs in the emitted word.
An ordinary Raw SWAP is matched as a gate and does not move the encoding.
The derived original frame must equal the checked workspace entry, including
zero-width ports. With one checked workspace interval and literal gates, the
checker can carry the original exit owners through the target suffix and use
the resulting placement to verify the emitted terminal measurements in
classical output order. All original quantum owners must be consumed by the
end. Discarded owners and measurements outside the classical outputs do not
add to the emitted readout. The single-interval check requires an exclusive
lifetime for fresh scratch. Outside a workspace interval the checker can also
compare a single original circuit event against a decomposed target word. It
derives the ordered support from the original operands and controls and
compares the complete exact operators on that support, up to six axes. Gates
on other wires and phase changes are rejected. Matrix checking spends the
same cumulative work as the surrounding replay.

A gate decomposition may use allocated synthesis scratch. The checker
verifies that its physical locations are declared and separate from all live
owners. It compares the full target word on the data and scratch with the
original operator under the canonical zero embedding at both ends. The
six-axis bound includes scratch. The executable check keeps the same zero
encoding at entry and exit. The Lean theorem
`WorkspaceTargetAction.synthesis_action` connects the actual decoded gate
word to the original local operator under that encoding. It proves equality
with full phase on every external reference column, with zero amplitude
whenever any synthesis scratch bit is nonzero. The checked placement replay
recovers this evidence at the original Raw position and physical gate offset,
for either a single circuit event or an optimized span.
`WorkspaceTargetAction.bound_synthesis_action` and
`WorkspaceTargetAction.native_suffix_synthesis_action` connect the replay
before a source workspace and the native decision's terminal suffix to that
exact action. The equation uses the original circuit steps on the recovered
support with their dependencies. Reindexing the checked local steps by the
ordered data and synthesis scratch layout recovers the same emitted instruction
slice. The decoder establishes the arity and distinct, in-range operands of
each instruction. The full physical register action on a fixed spectator
slice therefore agrees with the checked local word for arbitrary input
amplitudes and external references. The literal gate interval and its
synthesis scratch locations are within the reported gate and register counts.
A complete trace may reserve locations for several disjoint synthesis slices.
Original allocation, routing, source workspace and readout cannot touch
these locations. Every slice using them
checks its own zero return. An individual slice can instead use exclusive
scratch, which the checker verifies is untouched everywhere else.

A physical scratch location can also be reused across ordered, disjoint,
clean intervals. A zero-gate interval still checks the exact zero-return
equation and covers no gate accesses. The checker
requires an exact zero-return equation for each interval, checks that every
gate touching that location lies in one of those intervals, and checks that
the location is absent from terminal readout. The literal multi-interval check
derives every entry placement from the preceding original owners and target
word. It reserves each designated scratch location across the complete trace,
keeping it out of ordinary preparations, routing and terminal readout. Each
reuse interval must be bound to its own checked original workspace.

For a successful native placement check, each reusable clean wire is in the
counted reset register. Every gate that touches that wire belongs to a
checked restoration interval, with one operator step per decoded gate in
the interval. A routing action before a workspace or in the terminal suffix
points to a literal SWAP on an allowed edge at a counted gate index. The
reported SWAP total includes the literal routing gates as well as any
ordinary SWAP instructions in the target word.
The replay can also align a target word with several consecutive Raw circuit
events and structural owner operations. It reads the actual owner transitions
and checks the combined operator on the ordered support, with the same
zero-return check when the slice uses synthesis scratch. Preparation,
observation and source workspace boundaries require their own alignment.
The typed-source adapter reads workspace intervals from the original checked
root and named calls. It binds each local interval to the identical Raw
operations at its position in the root, checks the selected and returned
ports against the full caller frame, and retains all untouched spectator
ports. The exporter preserves the interval boundaries across exact
rewrites and proposes the corresponding gate positions and scratch locations.
Lean checks the proposal against the original source, including the clean and
dirty intervals and terminal result order.
The written logical operation and the workspace body use the same admitted
workspace source fragment. This lets an independently checked controlled
phase appear in the declared logical operation and in the body; their exact
restoration equation still checks the complete data and scratch action.
The application theorem `Qleisli.WorkspaceTargetAction.decoded_action`
connects the exact action of that decoded workspace slice to the literal Raw
body on its full ordered data and scratch interface. The equality preserves
the original phase for arbitrary reference columns.
For each reserved clean wire, `native_clean_access_counted_once` links native
placement success to its literal reset and one unique restoration interval
for every emitted gate that touches it. The application theorem also places
the interval inside the counted target gates and excludes the scratch wire
from terminal readout.
For a `Q<Bits<n>>` data register, each original `take_bit` or `put_bit` index
determines the ordered wire selection or insertion. The Raw repartition retains
the other owners, including a distinct `Q<Bits<0>>` remainder. Repartition inside
a workspace body is part of its independently evaluated exact operator.

Use `qleisli interop emit-qasm <source> --input=qli --resources` for the
checked resource report on a closed typed program with workspace scopes in
its root or in a statically named call, or with a protected computed scope.
The JSON result contains the emitted text, exact work spent in the placement
check, reserved qubits, reset wires, gates, literal SWAPs, T/TDG operations and
measurements. Counts come from Lean's decoding of the returned text.
The internal packet binds the complete original QLV3 request and literal target
bytes. Lean rechecks the original source, decodes the target and replays
placement using one 20,000,000 exact-work budget. Exhausting it returns a
limit rejection with no resource payload. The report covers the
supported canonical terminal profile and its declared physical register.
Lean proves that the decoded register width bounds the maximum Raw live width
over the workspace occurrences visited by the replay, including caller
spectators and temporary clean wires.
The native reply theorem binds the reported counts to those exact target bytes
and proves that the reserved width is within the requested target capacity.
A structural basis lift updates the physical placement only when its complete
table is an axis permutation. It contributes zero gates. A routing SWAP
must occupy a literal gate position.

For a source-checked structural `with_computed` interval, the Raw resource
read counts the full live frame plus one private scratch wire at peak. It
counts one preparation, one clean release and both predicate passes. The
literal circuit count includes every forward step, inverse step and protected
use. The Lean theorem `Qleisli.RuntimeComputedResources.structural_counts`
binds these numbers to the same original source-checked Raw occurrence and
retains caller spectators in the peak width.
The Raw interval reader charges owner and issuance-history checks separately
from literal circuit validation. Its circuit charge covers the full forward
and inverse fields and the operand checks in each forward step and protected
use. `QleisliKernel.Qirf.StructuralComputedRaw.read_work` proves the debit of
the executable reader. Both charges consume the same shared work budget.
The source-bound compute and inverse comparisons consume exactly
`16 * (1 + sum(2 * control_count + 7))`, summing over the predicate clauses.
The Lean theorem
`QleisliKernel.Qirf.StructuralComputedUse.read_circuit_work` identifies the
work state after both comparisons and before checking the emitted auxiliary
action. This charge depends on the literal circuit fields. The original
runtime plan retains the predicate and auxiliary action computed by Lean for
the exact source occurrence. Both the structural and finite-table paths use
those source results and check the actual literal action independently.
The same literal XOR factorization proves logical action for the independently
checked Raw event, even for an arbitrary caller amplitude function. The
source-bound theorem additionally identifies the predicate and phase from the
original body. The complete pure Raw event fold uses the local logical action
without constructing a global matrix.

The terminal OpenQASM placement check can read this event in a closed original
source root, including in a pure interval before or after an explicit workspace.
It places the ordered source wires followed by a private predicate wire and
reconstructs the whole forward, protected-use and inverse word from the Raw
operation. The decoded target word must agree on the complete support,
including the predicate wire, with exact phase. If the target decomposition
uses additional scratch, the same synthesis check requires it to start and
return to zero. The predicate and synthesis wires are reserved from source
allocation, routing and terminal readout. Counts include their resets, the
physical compute and inverse gates, and any additional synthesis gates.
This check uses the bounded terminal operator profile and its shared work
budget.
`BoundSegment.structural_paid` and `FinishedTrace.suffix_structural_paid`
recover the checked placement and gate interval from the executable replay.
`StructuralPlacement.literal_costs` binds that interval and the distinct data
and scratch locations to the decoded gate and reset counts.

For an admitted finite-table computed scope, the exporter uses the retained
table rows to emit controlled XOR flips of the private auxiliary bits. It
emits the protected operations on the ordered source, target and auxiliary
coordinates, then repeats the XOR flips to restore the auxiliary bits. For
resource reporting the source program must retain its original checked typed
request. Lean builds the original table permutation and protected word from
that request's checked Raw event and compares them to the complete decoded
target interval. The same bounded operator profile covers these comparisons.
`ProtectedTablePlacement.literal_costs` ties the decoded interval and its
distinct physical locations to the reported gate and reset counts.

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

## Phase words and target-dependent costs

In the eighth-root finite profile, let `ω = exp(2πi/8)`. The one-axis phase
with residue `r` is exactly `diag(1,ω^r)` on the declared axis, including
when it acts on an input entangled with a reference. A supported source
`phase[j,d]` has `r = 8j / 2^d` when this quotient is an integer. The
[primitive contract](primitive-boundary.md) specifies the source and profile
limits. Adjoint changes the exponent to `-r` modulo eight. Repetition
adds the residue on each action. A scalar `ω^r I` differs from a one-axis
phase and can become a relative phase under coherent control.

The existing finite format represents the one-axis phase by a monomial with
the chosen axis, identity permutation `[0,1]` and phase exponents `[0,r]`.
The action of the historical word of `r` T gates is the same diagonal.
Keep decoding the existing gate and circuit constructors in their versioned
profiles. This equivalent monomial representation requires no dedicated Phase
constructor or change to the established encoding of a T word.

For the canonical terminal OpenQASM vocabulary, the selected one-axis words
and their literal `t` or `tdg` counts are

| Residue | Emitted word | Literal T/TDG |
| --- | --- | ---: |
| 0 | empty | 0 |
| 1 | T | 1 |
| 2 | S | 0 |
| 3 | S, T | 1 |
| 4 | Z | 0 |
| 5 | S†, T† | 1 |
| 6 | S† | 0 |
| 7 | T† | 1 |

These counts apply to the specified one-axis words. A coherent branch or
control requires the complete ordered action on each sector with its original
phase. For example, the terminal export uses two T instructions, one T† and
two CX instructions for controlled S. A negative control can introduce
additional X gates. A conjunction-based lowering includes its live scratch,
preparation, computation and full reverse
chain. A model that decomposes CCX must include that decomposition. In the
canonical terminal profile CCX is a single literal gate and is outside the
`t_gates` counter, which counts exactly the emitted T and T† instructions.

Literal source-IR word counts, optimized target instruction counts and resource
bounds are separate claims. A certificate binds the actual emitted word and
checked decomposition to its profile and includes the required workspace and
routing. An exponent, operation name, or normalized phase word supplies no
bound for a different target or an optimal cost claim. See
[#165](https://github.com/MGYamada/Qleisli/issues/165).

## Small obstruction examples

Embedding a `k`-qubit gate `G` into `n` wires, under a fixed ordered basis,
gives determinant `det(G)^(2^(n-k))`. Determinants multiply under composition.
Consequently a target generator set restricts same-wire determinants.
This is a necessary obstruction; sufficiency requires a separate theorem for
that precise generator, phase and workspace profile.

In QPTL, `QPTL.FiniteMatrix.det_embedded` proves this determinant formula
for finite matrix bases and simultaneous reindexing of both interfaces.
`QPTL.FiniteMatrix.exact_same_wire_obstruction` proves that a product of
generators whose determinants lie in a multiplication-closed set containing
one cannot equal a requested matrix with determinant outside that set.
The premises retain the chosen target vocabulary, layout and exact phase.

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
and rejects output exceeding its physical qubit capacity. For an accepted
single-bit certified compute with an all-zero predicate, the exporter emits
the physical body with data axes followed by a separately reserved clean
scratch wire. It reuses that wire after complete verified zero return. The
Rust/Lean regression binds the same emitted OpenQASM bytes to two original
clean intervals and checks their placement, exact restoration and readout.
The terminal OpenQASM exporter can consume the original accepted handle of a
closed typed source program. It emits a wire-level projection of a Unit result
or a positive-width product of measured bits in the verified SSA output order.
Nominal results, zero-width components of products and source parameters are
outside this projection. Typed QIRF transport remains a separate obligation.
A nontrivial uncontrolled scalar has no realization in this gate vocabulary.
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
operations and the synthesis-workspace capacity limit. For source project
exports, a failure at a Raw operation emitted inside a closed generic body
identifies the specialization and points to the original expression. The
terminal exporter reports its own target refusal after source checking has
completed. Imported artifacts lack these compiler-local source diagnostics.
The location supplies no realization or resource certificate. General
specialization certificates and diagnostic coverage remain part of
[#48](https://github.com/MGYamada/Qleisli/issues/48),
[#120](https://github.com/MGYamada/Qleisli/issues/120) and
[#127](https://github.com/MGYamada/Qleisli/issues/127).

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
