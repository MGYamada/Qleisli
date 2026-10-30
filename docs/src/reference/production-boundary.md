# Current production verification boundary

This chapter records the implemented acceptance boundary and its proof limits.
It is subordinate to the [authority hierarchy](authority.md), the adopted
[single-verifier decision #276](https://github.com/MGYamada/Qleisli/issues/276)
and repository `TRUSTBOUNDARY.md`. It does not discharge a constitutional
obligation or widen an existing theorem. Source paths below identify files in
the [Qleisli repository](https://github.com/MGYamada/Qleisli).

## Implementation, publication and proof are separate

Production acceptance has completed the adopted migration to one native Lean
implementation. Rust generates proposals, selects and invokes the compatible
checker, retains immutable checked bytes, decodes views, reports diagnostics
and executes simulations. Missing, incompatible or failing native checkers
reject; the retired Rust verifier and dual-acceptance fallback are absent.
This does not mean that every public function invokes Lean or grants acceptance.

Version **0.2.9 was published and verified**. Its immutable record is
`tests/fixtures/releases/v0.2.9/publication.json`, binding source commit
`a77e68f4d3942cd75cb4c4710350aab9a99f8c8b`, the full CI run, registry and
GitHub distribution checks, native bundles and fresh installation evidence.
The selected development version **0.3.0-beta is unpublished**. The historical
release record does not certify the changed beta tree or its future packages.
The earlier VM29 first-slice, comparison and cutover records remain historical
evidence with their original scopes and results.

All **S05-C1–C5 remain open**, with full supported-profile Soundness targeted at
0.5.0. Implementation unification, publication, proof compilation, tests and
audits are distinct evidence. Neither this inventory nor an existing helper
theorem automatically discharges a guarantee in the constitutional ledger.
Edition 2026 identifies the constitutional regime, independently of release
and syntax compatibility.

## Entrypoints and actual checked representations

`native::Kernel` below means `interchange::native::Kernel`. Its ordinary
`NativeChecked` retains the artifact, optional request, checker identity and
reported work. `AcceptedProgram` retains its predecoded execution view only after a fresh
QLV3 native comparison of that exact graph and its caches. Inspection alone
does not authorize execution; [QDV1 and the envelope](execution-view.md) specify
the compared data and scope. The hierarchy module has a **different** `NativeChecked` with
its own payload/request/candidate and finite-obligation scope. Its dedicated
protocol reports are not ordinary `AcceptedProgram` handles.

| Entry path | Artifact or request actually checked | Actual checker | Existing proof and remaining gap |
| --- | --- | --- | --- |
| Source/project/qrate checks and compilation; raw IR; function/meaning evidence; QIRF import, export, conversion and `verify-ir`; foreign/Python imports | QLV3 envelope containing the original QLV1 QIRF/request packet and the actual retained execution view when execution is requested. Source, evidence and foreign adapters produce these bytes. | `native::Kernel` → `--qirf-native` → `Protocol.NativeContext.run` → `ExecutionView.Native.ordinary` → the original QIRF check and requested view comparison | `Qleisli.NativeValidity.check_sound` binds success to `VerifiedMeaning`; `check_scopeSafe` covers classical scope. Full ordinary EffectSound/CPTP, source/foreign translation, emitted-output and runtime preservation remain separate. |
| `CheckedContract::check`, its checked compositions, and `check_computed` | QIRF root and `qleisli.native-contract` encoded equation | `Kernel::check_encoded` → `--qirf-contract` → `ExecutionView.Native.contract` → `Protocol.NativeContract.checkRetained` → `Qirf.checkContract` | `Protocol.NativeContract.check_acceptance` binds the original bytes, decoded request and actual checking states. `Qleisli.NativeContract.check_encoded_sound` / `encoded_meaning` connect success to original-root `BodyMeaning`, the exact Basis interface and requested encoded equation. `Wrapper.circuitMatrix_entries` proves the actual wrapper's coefficient equality with the original matrix; `encoded_reference` extends the equation to any reference amplitude function. Source/compiler, compiled I/O, runtime/export, clean-release and quantitative resource claims remain separate; these theorems are not ledger admissions. |
| `finite_leaf::{check_unitary,check_serialized_unitary}` | QIRF root, signature, ordered input/output ports and exact matrix request | `Kernel::check_leaf` → `--qirf-contract` → `ExecutionView.Native.contract` → `Protocol.NativeContract.checkRetained` → `Validity.checkRoot` and `Qirf.check` | `Qleisli.NativeContract.check_sound` / `leaf_meaning` compose native byte acceptance to original-body instrument meaning for the bounded closed unitary fragment, exact requested matrix, signature and ordered ports. The output port is tied to an actual verification. `leaf_reference_laws` extends both whole-space inverse laws to every finite reference. Source/runtime and broader effect/clean-release claims remain separate. |
| `pure_leaf::check_pure` | QIRF root, separate domain/codomain type trees, ordered owner ports and exact rectangular matrix | `Kernel::check_pure_leaf` → `--qirf-contract` → `ExecutionView.Native.contract` → `Protocol.NativeContract.checkRetained` → `Qirf.PureLeaf.check` | `pure_leaf_meaning` binds fresh graph/root checking to the original body and exact Gram identity. `pure_leaf_reference` preserves inner products for arbitrary joint reference amplitudes. This grants neither inverse nor control access, source/runtime correspondence, target realization or quantitative resource evidence. |
| `Kernel::check_carrier`; explicit `Instantiation::check_carrier` source adapter | Original QIRF/dependencies, both ordered nominal owner forests, original declaration sources and an independent exact logical matrix | `--carrier-pure-check` → `ExecutionView.CheckedCarrier.run` → `Protocol.Carrier.check` → original source checks and `Qirf.Carrier.check` | The binding retains the original packet and exact QDV1 comparison; the core postcondition binds actual body/code and Gram equations. The source adapter adds retained-step replay, without ordinary runtime, inverse/control access or an AST-preservation theorem. |
| `engineering_openqasm::{check_with_kernel,check_serialized_with_kernel}` and `engineering compare-openqasm3` | Literal canonical target bytes, original ideal/dependencies, exact Unit/Bit signatures, closed epsilon/majorants and the complete retained QDV1 view | `--engineering-openqasm-check` → `CheckedEngineeringOpenQasm.run` → independent byte decode and unchanged complete instrument checks | `NativeEngineeringOpenQasmProtocol.run_meaning` binds the literal target and original ideal to the actual checking execution. `run_complete_adjoint_bound` covers every finite reference. The private report is engineering-only, without an actual `AcceptedProgram`, source/export-preservation, pure/control, cleanup, hardware, resources or constitutional PR/RS claim. |
| `hierarchical::Kernel::{inspect,inspect_native}` | Dedicated hierarchy payload and all required finite leaves | `--hierarchy-pending` → `Conditional.checkAll` and `HierarchicalFinite.checkLeaves` | `NativeHierarchy.conditional_derives` and `checkLeaves_semantics` bind structural derivation and finite meaning. Full analytic meaning-to-Operator composition remains open. |
| `hierarchical::Kernel::{check_against,check_against_native}`, ordinary request branch | Hierarchy payload and composition request | `--hierarchy-request-pending` → `Root.checkAll`, `checkLeaves` and `checkPairs` | `NativeHierarchy.requested_pairs` and finite-leaf results retain their stated premises; a producer comparison request proves consistency, not source preservation. |
| The same methods' Fourier branch | Hierarchy payload and Fourier request, including Hadamard obligations | `--hierarchy-fourier-pending` → `FourierRoot.checkAll`, `checkLeaves` and `checkHadamards` | `NativeHierarchy.hadamard_semantics` and `checkHadamards_semantics` establish finite obligations; complete analytic/source/runtime composition remains open. |
| `check_instrument` / `check_instrument_native` | Instrument payload and preparation/evolution/readout request | `--instrument-pending` → `Instrument.checkAll`, `checkLeaves` and `checkPairs` | `Instrument.checkAll_stages` / `checkAll_boundary` and native finite results cover components. They do not establish complete source or host execution preservation. |
| `check_qpe_instrument` / `check_qpe_instrument_native` | Instrument payload, named provider request and candidate binding | `--qpe-instrument-pending` → `QpeInstrument.checkAll`, `checkLeaves`, `checkPairs` and `checkHadamards` | Named structural and finite obligations are checked. The complete native analytic Operator bridge and general source-QPE meaning remain open. |
| Private readout and preparation protocols | QLM1 readout and QLZ1 preparation packets | `--readout-check` → `Readout.check`; `--preparation-check` → `Preparation.check` | Component `check_reference` / `check_boundary` results retain explicit premises. These reports are not complete program handles or runtime guarantees. |
| Phase-word, phase DAG, layout, layout DAG and phase-layout file protocols | Separate component artifacts and requirements | `Cli.Finite` → `verify`, `Hierarchy.check`, `Layout.check`, `LayoutDag.check`, `PhaseLayout.check` | Existing phase/layout component results do not extend automatically to ordinary production programs. |
| `Finite.check` / `checkAll`, `circuitMatrix`, `FiniteCodec.readMatrix` | Finite circuits, contracts or serialized matrices | Finite checking, evaluation or decoding, respectively | Finite component theorems have explicit inputs. Evaluation and decoding alone are not acceptance; composition with each actual production root is required. |

`lean-kernel/Main.lean` dispatches sixteen explicitly versioned native modes,
including four mechanically separate engineering-only comparisons.
`lean-kernel/Cli/NativeContext.lean` invokes the pure
`Protocol.NativeContext.run` dispatcher and its single reply projection. It
checks the original QLV3 edition and compiled product before applying each
mode's existing gate; the strict version-3 reply binds that same context.
The older IO adapters are unused and await retirement after replacement
conformance coverage; they are not fallback entry points.
`lean/Qleisli/NativeValidity.lean`, `lean/Qleisli/NativeContract.lean`,
`lean/Qleisli/NativeHierarchy.lean` and `lean/Qleisli/Qirf.lean` contain the cited
bridge theorems. The native executable,
its transport, decoder and execution correspondence assumptions remain explicit;
having Lean source does not prove compilation or the entire pipeline correct.

The native-contract bridge is specific to `Protocol.NativeContract.check`; it
does not inherit the theorem for the ordinary `Protocol.Validity.check` root.
Its `Acceptance` witness retains the original QLV1 body and request bytes,
UTF-8/JSON decoding, artifact/order, requested signature, ordered ports and exact
matrix or encoded contract, with continuous work states. These are necessary
success facts, not a converse characterization of every parser constraint.
The leaf conclusion retains complex phase; its arbitrary finite-reference laws
require no separability or normalization premise. The encoded branch retains
the original root's `BodyMeaning`, complete Basis interface and checked encoded
equation through `EncodedMeaning`, `encoded_meaning` and `check_encoded_sound`.
Those bounded original-root results do not establish source, deployed-binary
or host execution correspondence.

### Finite nominal carrier requests

The internal `--carrier-pure-check` mode accepts a strict version-1
`qleisli.carrier-request` with profile `finite-carrier-pure-v1`. Its fields
are `format`, `version`, `profile`, `attached`, `required` and `logical`.
Both interfaces retain complete ordered owner forests and public effects.
Nominal atoms retain original module/declaration/source identities and member
order, independently of logical cardinality and physical width. Singleton
enums and empty records remain distinct from Unit and Bits<0>.

`Protocol.Carrier.check` reconstructs the original declarations, import paths
and existing field Nat helpers before checking the actual graph and root.
The core freshly checks both canonical code Gram equations, the logical map's
Gram equation and `physical * E_in = E_out * logical`. Logical dimensions
govern the Unitary label; a larger physical unitary does not justify a logical
Unitary claim. Observation, reset and discard cannot be hidden as pure.
The existing source, matrix and work limits remain in force.

`CheckedCarrier.run_binding` binds the execution-only QLV3 packet and actual
QDV1 comparison of the graph, both interfaces and logical matrix. Its
`Binding.root_safe` follows the actual checked root to the independent
ownership and classical-scope properties. Extra source rows require exact
nominal origins after source checking; ordinary checking retains its previous
source-use rule. Uncovered helper/import-only rows refuse.

The explicit source adapter uses the common judgment, selected Builder and Raw
emitter. It requires an independent logical request and replays retained source
steps against the checked body. Its sealed `CheckedSourceCarrier` retains that
source graph and always reports `source_meaning_verified() == false`.
Descriptors and source preparation grant no acceptance. Neither this result nor
the private native carrier holder converts to an ordinary execution handle or
grants inverse/control access. The first closed ordinary-result runtime route
is separate below; general nominal functions, quantum owners, full qmatch and
original AST-to-step preservation remain unfinished. These component results
admit no new guarantee and do not widen the two existing ledger scopes.

### Ordinary input/result requests

The internal `--ordinary-root-check` mode accepts `qleisli.ordinary-root-request`
version 2, profile `finite-ordinary-root-v2`. Its strict fields are `format`,
`version`, `profile`, `selection`, `module`, `declaration`, `parameters`,
`input_storage`, `input_rows`, `basis`, `storage` and `public_effect`. Version1
and unknown fields/profiles reject without fallback. Project selection denotes
exactly closed `main::main`, including a private ordinary main; exported selection
requires an original public declaration. Internal selection checks an original
private non-entry declaration without exporting its name. Original parameter and
result types must be ordinary finite types; quantum ports remain unsupported here.

Nongeneric public selected functions use this same gate through the common
original-source compiler, including small quantum temporaries checked over every
hidden history. Interfaces remain ordinary in this mode.
Selection retains the exact original instantiation, complete checked host
bindings and accepted request. Both closed simulation and sampling reject
nonempty retained parameter forests even when every parameter has zero width.
The source wrapper also discharges dormant function pairs through the same
contract gate as project checking, preparing the original Meaning/body
dependencies visited by global obligations. Explicit public `main` selections
use the exported rule; project-main restrictions remain separate.
Generic selected integration remains unfinished. Mixed quantum interfaces use
the separate runtime-root mode below. Untrusted
portable nominal emission refuses until its complete typed request is transported.

The basis retains the existing complete nominal prefix representation. Storage
separately retains Unit, Bit, Bits, pair, tuple, enum origin/SSA coordinates and
record origin/ordered named children. Zero-width nodes cannot be discarded.
The original ordered parameter forest and declared result are freshly read and
compared with the request. Argument count and zero-width arguments stay explicit.
Closed simulation and sampling additionally inspect that retained parameter
forest: Unit, Bits<0> and empty records still require an actual invocation even
when the Raw input lists are empty. A nullary typed result remains closed.
The same original Raw root/dependency/ownership/effect/scope checks run before
complete exact instrument reconstruction. Lean independently enumerates the
entire canonical parameter domain, first argument on low coordinates, and
requires exact equality with the proposed `input_rows`. It checks typed input
storage for every row, then interprets every actual hidden history, including
zero-probability histories, using the independent ordinary-value relation.
Flattened input/output SSA maps must equal the original Raw lists. An invalid
enum code, changed nominal identity, reordered field/axis or hidden Observe under
a pure label refuses. A declared public Observe bound is retained even for a
pure implementation. Source rows require the actual selected original, exact
checked nominal origins or actual original type-resolution paths from the
selected parameter/result types and recursive record fields. The shared
independent resolver retains its exact query, original lookup bytes, visibility
and import/reexport edges. An arbitrary row or a validated unused Nat helper
cannot supply type-path coverage. Projection and both coverage scans are
precharged within the existing work limit.

Rust's private ordinary proposal decoder accounts for every proposed source's
path and text under the existing aggregate identity limit, then defers relevance
to this native gate. It returns no accepted handle. Other decoding routes retain
their original unused-row refusal; the ordinary execution view compares every
retained original source byte before a fresh accepted handle is bound.

`Protocol.OrdinaryRoot.check_binding` retains the original packet, fresh
artifact/request reads and actual root check. The execution-only QDV comparison
and native dispatcher retain this binding through `CheckedOrdinaryRoot` and
`run_typed_ordinary_binding`. The private accepted program retains the same
typed request, complete checked input rows and graph. Ordinary source callers
use the common original-body lowering. Existing `run_closed`/`sample_closed`
APIs still reject any nonclosed root; checking parameters adds no unchecked
arbitrary-input execution API. Generic selected/dependency integration, full
qmatch and nominal finite-table consumers remain separate work.
Untyped rechecking and portable export refuse until
the complete typed artifact transport exists. Existing six-bit instrument and
carrier/work limits remain. Text/JSON reports distinguish this declared
result/history check from an independent external algorithm specification.
No source-body, decoder/native compiler, simulator or target preservation
theorem, external schema, inverse/control capability or new guarantee follows.

### Mixed runtime root requests

The internal `--runtime-root-check` mode reads strict version1
`qleisli.runtime-root-request` metadata with profile `finite-runtime-root-v1`.
Full parameter/result prefixes preserve each `Q` boundary, nominal declaration,
ordinary tuple and zero-width owner. Storage binds actual ordinary SSA values
and ordered quantum ports. The original runtime signature and shared Raw root
checks remain independent of these producer descriptions.

For every independently enumerated ordinary input, `RuntimeFamily` reconstructs
all hidden maps, checks ordinary results even on zero-probability histories,
checks exact input/output code-space equations and their complete logical Gram
sum. Physical padding may not leak into a logical result. Observation remains
Observe, and a Unitary label requires equal logical dimensions. The six-bit
dense component limit and existing work limits remain unchanged.

QLV3/QDV compares this complete request and the actual retained graph.
`Kernel::check_runtime_root` and fresh `check_program` rechecking bind the same
objects to an execution-only native decision; inspection/caller scopes refuse.
`AcceptedProgram::runtime_result` exposes read-only metadata. Portable export
cannot erase that metadata. Original parameters prevent closed execution even
at zero physical width. The common nongeneric project/selected emitter uses
this gate for mixed runtime interfaces, retaining actual input storage before
call expansion and complete output types/owners afterward.

`RuntimeRoot.check_binding`, `CheckedRuntimeRoot.run_binding` and
`NativeContext.run_typed_runtime_binding` connect actual reads and comparisons.
The root safety theorem reuses the original Raw gate without enlarging either
human-admitted guarantee. Exact computation witnesses are separate from complex
denotation, source-body preservation and numerical runtime correspondence.
Generic/static, nominal coherent-table/Meaning and wider qmatch integration
remain pending. No external schema, inverse/control capability, new guarantee
admission or broader QS/PR/RS/EXACT discharge follows from this mode.

### Named-arm qmatch component requests

Shared conformance cases cover three- and four-label nominal selectors on two
physical bits with a distinct zero-width Unit target, reordered written arms
and exact relative phases. The three-state code leaves its padding label
outside the logical interface. Literal retained-view expectations include
the four dyadic coordinates of an eighth-root phase. Phase, control-polarity
and evidence faults must reach the equation gate; original nominal/arm/owner
substitutions reach the request gate, and stale compared output reaches QDV
refusal. These component checks do not supply ordinary source execution or
the full twelve-bit profile.

`Kernel::check_qmatch_source` invokes the execution-only internal
`--qmatch-source-check` mode. The [request and QDV schema](execution-view.md#internal-named-arm-qmatch-component)
bind both complete typed interfaces, the original source byte occurrence and
actual evidence/control indices to one fresh graph. Original source reads
determine the canonical labels, types, owners, public effects and source rows;
actual receipt inputs and dependency snapshots bind the named arm bodies.
The pure finite/Raw/QIRF/nominal gates check exact main/U/CU sector equations.
The ordinary source-root wrapper retains its original main-only roots and empty
extra source-query extension.

The Rust walker describes the actual retained graph and circuit/matrix caches,
then the same allocations enter `QmatchChecked` only after exact QDV and native
product/edition/mode/scope/request matching. No public conversion yields an
ordinary `AcceptedProgram`, inverse or controlled capability. Data constructors,
request encoding and source headers alone supply no source-function theorem.
Generic success bindings retain the original Raw ownership/classical-scope
properties without enlarging either human-admitted guarantee.

This named-arm component uses an internal canonical owner frame. General source
expressions/call frames, other valid mappings, constructed/static/generic arms,
ordinary/selected quantum nominal execution and the full twelve-bit/64-label
source contract remain pending. The internal frame is not a new language
restriction. Fresh native conformance, canonical proof maintenance and full CI
remain required; original source-body lowering, decoder/walker/native compilation,
runtime/target preservation and broader QS/PR/RS/EXACT duties are separate.

The current ordered Raw frame additionally requires a complete structural
source return. Checked renaming, ordinary tuple moves and the final expression
retain the original logical owner identities, basis trees and returned order.
Unknown suffix expressions, hidden observation/discard and missing or duplicated
owners refuse. A legal source return that changes owner order requires a matching
Raw output mapping; equal types or empty wire lists do not justify reusing the
unswapped Raw subject. This check does not establish general source/arm lowering
or expose ordinary source execution.

The original Raw operations additionally transport an independently derived
logical owner tree. Explicit joins retain ordered children; splits recover those
children, and owner-moving operations retain their complete source roles. The
actual output-token order must match the original source return. Reversing two
empty Raw ports cannot pass for a canonical source return; a matching source/Raw
zero-width permutation is accepted. Physical widths constrain a split without
identifying a logical owner. No role table or cached tree is supplied by a producer.
Splitting an opaque source owner, allocation/release or changed representation
needs its own checked source rule/refinement; this structural component does not
establish every valid Raw mapping or complete source preservation.

### Rectangular pure-leaf requests

The version-paired native gate accepts `qleisli.native-contract` version 1
with `kind: "pure-leaf"`. Its complete fields are `format`, `version`, `kind`,
`domain`, `codomain`, `input`, `output`, and `matrix`. Both types use exact QIRF
basis trees; the ports retain token, ordered wires and bit shape. Unknown fields,
unknown versions and producer acceptance flags reject. The existing square
`kind: "leaf"` protocol and its two-sided unitary conditions remain available.

The original QIRF root interface now describes a unary pure function with
independent input and output types. Its structural check requires a Unitary or
Isometry effect, no classical ports, one input and one actual live output owner,
and the corresponding input/output widths. The literal original-body reader
finds the output owner; the input width does not stand for the output width.
Ordinary validity alone still does not establish an external matrix equation.

`PureLeaf.check` freshly checks the original dependency graph and body, binds
both exact type trees and both ordered ports, reconstructs every input column,
and checks exact equality to the requested matrix and `V†V = I`. Reconstruction
retains the original effect checks, complete classical branches and hidden
observation histories. Measurement, reset and discard cannot be relabeled pure
or erased from the equation. Zero-width owners, exact phase and axis order remain
part of the obligation. Both endpoint dimensions retain the existing six-bit
dense bound and shared exact-work accounting; no unbounded matrix API is added.

`CheckedPureLeaf` is a private-construction receipt over immutable original
artifact/request bytes. Rust boundary construction and matrix serialization
validate untrusted data shape only. Fresh native acceptance is required for
every receipt, including one using previously checked dependency data.

The ordinary frontend retains `SourcePureEquation` sidecars on its accepted
entry: independently checked implementation and reference leaves, their exact
matching domain/codomain and matrix, resolved names and original source text.
Constructor lowering rechecks actual renamed Raw fragments against the derived
matrix. Selected Raw lowering retains its original Meaning requests and checks
actual instruction intervals. The hierarchy's refined finite-leaf path remains
square and refuses rectangular Meaning obligations. Source snapshots provide
provenance; neither sidecar is a general source-preservation proof, an arbitrary
whole-entry functional specification, or a new constitutional guarantee.

### Original-artifact control-sector requests

The existing version-paired `--qirf-contract` gate also accepts a strictly
decoded `qleisli.native-contract` version-1 request with `kind: "control"`.
Its complete field set is `format`, `version`, `kind`, `signature`, and `axes`.
`signature` is the exact QIRF basis tree; `axes` is an ordered list of distinct
physical bit positions in that interface. Extra fields, including a proposed
matrix or producer success flag, reject. The inner QLV1 format and encoded/leaf request contracts remain unchanged;
external calls require the QLV3 envelope and scope.

Lean checks the original graph, root, dependency evidence and identical
input/output interface, reconstructs its actual action, checks whole-space
unitarity, and then requires every matrix entry between different requested
computational-basis sectors to be exactly zero. The existing six-bit finite
reconstruction limit and continuous work accounting apply. An empty axis list
is meaningful for a zero-width logical owner; it does not erase ownership or
nontrivial phase.

`Protocol.NativeContract.ControlAcceptance` and `check_acceptance` retain the
original body/request bytes, exact decoded signature/axes and the actual
checker execution. `Qleisli.NativeContract.control_meaning` connects the same
action to original-root `BodyMeaning`, its exact interface, sector condition
and inverse laws. `control_reference` proves projector commutation on arbitrary
joint complex amplitudes with any external reference. Phase kickback and
entanglement are permitted; the result does not assert an unchanged reduced
control state or separability.

This request alone does not enable source `ctrl` calls. Original
source places, call-specific artifact identity, aliasing, access lifetimes,
lowering/execution correspondence and quantitative resource/scheduling claims
remain separate obligations. No new native mode, external schema admission or
constitutional guarantee is introduced.

The internal `Qirf.ControlAccess.checkOwners` component additionally checks
an original call with several ordered quantum ports, without constructing a
single-port packing wrapper. Its explicit requested basis forest must match
the original input and live returned owner widths and positions, including
zero-width owners. `checked_owners_meaning` and `checked_owners_action_project`
bind the actual root/dependencies and full complex action to the sector law.
Raw bit widths do not establish source type trees: the requested forest still
requires binding to the original checked source. The strict native request
`kind = "control-owners"` carries exactly `format`, `version`, `kind`,
`signatures` and `axes`; it accepts neither a proposed matrix nor a success
receipt. `ControlOwnersAcceptance` retains the decoded ordered forest and
coordinates, original packet bytes and actual checking execution.
`control_owners_meaning` and `control_owners_reference` extend the original-body
and arbitrary-reference results to this request. The finite project path binds
this request to each actual emitted control-call interval, original ordered
owner ports/basis forest and returned tokens before updating source bindings.
It checks nested calls and unused concrete declarations. The complete final
artifact still requires ordinary native acceptance. Neither an annotation nor
native unitarity alone supplies control-sector evidence; host source lowering
and interval extraction are not a Lean source-preservation theorem.

Selected source projection retains the original ordered access roles with the
call's source identities and positions, including public `ctrl` occurrences.
Elaboration checks the exact owner shape and actual effect; it neither grants
sector authority nor rewrites the role to `excl`. Checker-free Raw and
hierarchical lowering reject retained control roles. Native-checked selected
Raw lowering independently checks every retained control-bearing concrete body
and the selected root, then replays its actual decoded calls with fresh sector
requests. Final consumption repeats native acceptance and source replay;
retaining a role or an earlier success is not acceptance authority.
The common judgment also records each original control call as a pending sector
obligation. Native-checked selected Raw lowering requires every original
obligation to have a concrete interval in each retained specialization of its
declaration; absent intervals remain unsupported. One specialization cannot
cover another's missing call. Unused original declarations, unselected branches,
empty loops and zero-count providers cannot erase the obligation or its
location. Retained zero-count provider bodies are checked before root emission.

The internal Raw replay bridge can discharge a retained control obligation
using the checker associated with the accepted original artifact. It selects
the actual instruction interval consumed by replay, its input/returned tokens
and ordered source basis forest, then submits a fresh `control-owners` request.
It does not take a producer-supplied call body, matrix or success receipt.
Control replay without a native checker refuses. Work is shared across these
decisions within the existing exact-work ceiling. Regression tests use original
public control source graphs as well as private graph mutations. The checked
Raw entry shares this budget across all body and root decisions; it refuses an
increased ceiling, exhaustion or unavailable checker. AST-to-step preservation
and Rust decoding/interval extraction remain separate obligations; this host
bridge is not a new Lean source-preservation theorem.
Symbolic inverse/controlled replay also refuses retained control roles: its
transformed trace does not supply the original call intervals required by this
native bridge. Zero-count and unused-provider obligations must still be covered
before selected transport can be admitted; they are not waived by empty output.

`tests/fixtures/constitution_v030/native-contract-bridge/` preserves the unchanged
executable prefix, printed theorem/predicate types and axiom sets, and a
validation record. These identity and proof checks do not admit a new guarantee,
close S05, or establish source/compiler, deployed-binary, Rust rematerialization,
target/runtime or quantitative Resource Safety claims.

### Original-artifact observing instrument requests

The version-paired `--qirf-contract` gate accepts `kind = "instrument"` in
`qleisli.native-contract` version 1. Its exact fields are `format`, `version`,
`kind`, `actual_signature`, `expected_signature`, `identity` and
`expected_artifact`. `expected_artifact` is the original expected QIRF JSON as
a UTF-8 string; the actual QIRF remains the original QLV1 body. Both complete
graphs, selected roots and dependency evidence are freshly checked. Supplied
matrices, receipts, success flags, missing fields and extra fields reject.
The QLV1 framing, QIRF representation and previous request variants are unchanged.

Each signature has exactly `input` and `result`. `input` is the existing QIRF
basis tree. The complete result tree uses these exact objects:

| Result | Fields |
| --- | --- |
| Ordinary Unit or Bit | `{"tag":"unit"}` or `{"tag":"bit"}` |
| Ordinary Bits | `{"tag":"bits","width":N}`, with a u32 natural width, including zero |
| Quantum owner | `{"tag":"quantum","basis":B}`, with the complete QIRF basis tree |
| Pair | `{"tag":"pair","left":L,"right":R}` |
| Tuple of at least three values | `{"tag":"tuple","fields":[...]}` |

The signatures must agree as entire trees, including Unit, Bits<0>, zero-width
quantum owners and product nodes. The ordered quantum owners and classical
projection must match the original roots. Source consumers select this contract
using caller-visible Observe effects. The current native profile additionally
requires genuinely observing original artifacts; a conservative Observe bound
on a pure body neither rewrites its Raw classification nor authorizes a pure
contract fallback. Unsupported concrete pairs refuse, including unused ones.
The first profile has one quantum input and no runtime classical inputs.
Signatures are requested type data: native widths alone do not reconstruct
or prove preservation of the source's full types.

`identity` has exactly `implementation`, `specification` and `sources`, with
each source containing exactly `path` and `text`. Existing name/path, 128-source
and aggregate 1 MiB identity bounds apply. Result trees are bounded to depth 64
and 4,096 nodes. Existing six-bit dense reconstruction, shared work, JSON and
16 MiB transport limits apply; no equality tolerance is introduced.

`Protocol.NativeContract.InstrumentAcceptance` retains the original decoded
request, original expected text, fresh expected graph and continuous checking
states. `Qleisli.NativeContract.instrument_meaning`, `check_sound` and
`check_encoded_sound` connect success to both original-body instrument meanings,
complete Kraus sums, untruncated dimensions and identical unnormalized public
outcome maps on any joint matrix with a finite external reference. The independent
reference in `Qleisli.Semantics.InstrumentEquality` sums all hidden histories;
neither their count nor their labels are public outcomes.

The private Rust instrument handle retains both original accepted artifacts,
the complete signature, source identity and fresh paired native decision.
Both concrete `apply_contract` adapters execute only the implementation and
check its actual emitted interval again against the immutable reference. Each private
call sidecar retains original ports, instructions, result IDs and source span;
the enclosing root has its separate ordinary acceptance. Unused original
closed obligations are also checked. These sidecars do not change QIRF or set a
request-free root's `request_checked` or `source_meaning_verified` to true.
Selected Raw preparation independently replays the original implementation,
then checks the consumed instruction interval, actual input owner and ordered
result through a fresh native equation. The retained proposal keeps the original
pairs and private call sidecars; later source validation checks again using the
accepted artifact's checker. Dependencies, unused declarations and zero-count
children keep their original obligations. Hierarchy lowering and checker-free
emission reject this overload. This grants no observing Meaning, coherent control
or adjoint access. Pure Meaning retains its exact phase rule. Request-free
whole-root inspection still reports no independent requested meaning. Source,
decoder, native compilation/runtime and emitted-artifact preservation remain
separate obligations; these lemmas admit no constitutional guarantee.

## Root loading and compatibility during generic migration

`frontend::project::Project` loads every `.qli` module beneath its selected
source root and all bundled ordinary sources. Ordinary project compilation
checks every materialized concrete ordinary function root, including unused
functions. Classical bodies and Meaning declarations have their separate
preparation/checking obligations. Common source checking covers every declaration,
including unused declarations and both branch bodies.
`QrateSource` in `src/frontend/project/manifest.rs` provides opt-in selection of
an explicitly declared `[source].root`. That selection chooses the source tree;
it does not introduce reachable-only loading or exempt unused siblings inside
it. Explicit module-map `ParsedProgram::parse` checks every supplied module and
the bundled registry before selecting a concrete entry.

Ordinary finite-frontend function/instrument receipts and local equation
sidecars retain source provenance separately from this loading policy. Each
retained declaration contributes its original resolved lexical dependencies,
including type and Nat expressions, Meaning references, inactive branches and
zero-count operations. Actual bound Op descriptors and checked Raw receipt
dependencies contribute their original source records as well. Pure providers
retain their original declaration and equation association; instrument calls
also retain the original caller and its concrete Op bindings for source-span
binding. The resulting closure retains complete original module text, including
comments, and shares immutable module records across receipts. Unrelated loaded
modules need not appear in each receipt. Existing metadata and aggregate native
transport limits still apply. This selection changes neither loading nor eager
checking of every loaded declaration and does not implement #273. These records
provide provenance, not a source-preservation proof or acceptance authority.

A future reachable-module policy in
[#273](https://github.com/MGYamada/Qleisli/issues/273) must specify entry roots,
transitive imports/providers/Meaning dependencies, independent checking of the
selected graph, bundled-library validation and the treatment of unused sources.
It must retain original module/root/dependency identities and reject stale,
missing or replaced references. Preserve the current permitted import-only
cycles; imports have no runtime action. Forbidden call, Meaning and provider
dependency cycles retain the rules of their actual profiles, including any
explicitly admitted decreasing recursion. Diagnostics and source-selection
migration need review before changing the current all-source behavior. This
chapter enables no such change.

The [five-role architecture](primitive-boundary.md#generic-acceptance-and-library-owned-algorithms)
assigns compatibility duties for flat Raw IR, both QIRF profiles, finite
contracts, all five hierarchy modes, component protocols, source/qrate and
module-map entrypoints, Rust/Python clients, foreign adapters and research
comparisons. A later migration must preserve each supported contract or state
its explicit versioned replacement, unsupported cases and migration tests.
Keep replaced wrappers and their proofs built/audited until their supported
callers and obligations migrate. Missing/incompatible native checking must
continue to reject through every route.

Already retired APIs are not compatibility promises to resurrect:
`frontend::sized` moved to `frontend::compile`, and the `qleisli sized` command
prefix was removed with explicit migration diagnostics. The separate research
and Python comparison readers do not restore that production namespace or
supply alternative source acceptance. Edition 2026 continues to identify the
constitutional regime; source/API/protocol compatibility is versioned
separately.

## CLI success reports and requested meaning

Without an explicit `--entry`, `qleisli check <source-root>` and
`qleisli check <directory> --qrate` check the source project and its concrete
lowered roots. A successful request-free native
decision establishes the applicable IR structure, ownership, interface and
classical-scope checks. It does not establish an independently requested
algorithm, the source's full meaning, or preservation from source to IR.
The text success report names this scope and the actual canonical checker paths,
states whether independent requests were checked, and states that source
preservation is not proved.

The version-1 JSON result envelope retains `outcome: "ok"` and an empty
`diagnostics` array. Its whole-project source-check `result` replaces the former
`{"verified":true}` with the following fields:

| Field | Meaning |
| --- | --- |
| `checker_paths` | Distinct canonical executable paths captured from actual successful native invocations, rather than resolved again after checking. Several paths can occur if a selected symlink changes between invocations. |
| `checker_identity` | `"unpinned"`: the executable was selected and invoked, but its bytes were not checked against a trusted binary identity. A canonical path is not attestation. |
| `native_decisions.count` | Number of successful native acceptance decisions observed during this source check, including repeated decisions and decisions for partial source contracts. |
| `native_decisions.requests_checked` | Number of those decisions with a separate native request payload checked by Lean. This counts decisions, not distinct source declarations or whole-source meanings. |
| `native_decisions.complete` | Whether the metadata covers every successful decision and its checker path. If false, the bounded report is incomplete and its path list or counts must not be treated as exhaustive. |
| `entry.present` | Whether the ordinary project has a supported `main::main` entry. A library without that entry can still check successfully. |
| `entry.request_checked` | Whether that entry's own accepted artifact has a separately checked native request payload; `null` when there is no entry. Producer-generated typed requests count here without establishing an independent algorithm specification. Requests on other roots or partial contracts do not change this value. |
| `entry.ordinary_result_checked` | Whether this entry retains the native ordinary-v2 input/result and all-hidden-history check. False for absent entries and other modes. |
| `entry.runtime_result_checked` | Whether this entry retains the native runtime-v1 complete type/storage, quantum code-space and all-hidden-history check. False for absent entries and other modes. |
| `concrete_ir_roots.local`, `concrete_ir_roots.bundled` | Counts of checked concrete ordinary function roots, separating loaded project/dependency modules from bundled library modules. |
| `source_preservation_verified` | `false`: this command does not prove source-to-IR preservation. |

All loaded bundled concrete functions are checked, including unused ones;
their decisions and roots therefore contribute to the report. Generic operation
expansions occur within enclosing concrete roots; they are not additional roots
merely because a specialization was registered. Constructing or declaring an
unused Meaning does not imply that Lean checked a corresponding equation.
Pure/function/instrument contract requests have their individual native scopes.
When supplied as separate external requests, their successful decisions contribute to `requests_checked` without asserting
a whole-entry Meaning or general source preservation. In particular, a positive
aggregate request count can accompany `entry.request_checked: false`.
These request fields describe the separate external request payload, not
Meaning entries embedded in an ordinary QIRF artifact. A zero request count
does not claim that no embedded Meaning was checked. A reachable
`FunctionEvidence` dependency is checked with its ordinary QIRF root; that
invocation contributes to the decision count but has no separate request
payload. Its exact dependency equation is not identified or proved merely by
reading these counters. Request data can itself be
producer generated; checking it does not establish an independent specification
of the original source.

Selected-source `check --entry ...` routes report the selected root's singular
actual `checker_path`, `checker_identity: "unpinned"`, `request_checked` and
`source_preservation_verified: false`, alongside their existing `verification`
scope and `request_origin`. The Raw route's native-validity scope is distinct
from hierarchy composition, Fourier, instrument and named-QPE request scopes.
Finite artifact reports additionally expose `ordinary_result_checked` and
`runtime_result_checked` with the same meanings as the project-entry fields.
`request_checked: true` also applies to a checked producer-consistency request;
it does not assert an independent specification of the source's Meaning.
The existing `source_meaning_verified: false` remains explicit. These fields
describe the selected root's receipt, rather than an aggregate of every native
decision made while preparing and checking the source.

`verify-ir` reports the checked artifact's singular actual `checker_path`,
`checker_identity: "unpinned"` and `request_checked`; with `--against`, the
request result applies to that exact supplied artifact/request pair. `emit-ir`
reports its output `path` with the emitted root's checker and request metadata.
Their text successes likewise state the IR/request scope. Neither command's
success establishes preservation from a source, a trusted binary identity,
or correctness of downstream execution/export.
`interop check` uses the same singular actual-root metadata in its JSON
success instead of the former unqualified `verified: true`; importing foreign
source and accepting its lowered artifact do not prove translation preservation.

Clients using the former source-check `verified` boolean must inspect the
explicit scope fields instead. The former `verify-ir` and `interop check`
unqualified `verified` booleans are also retired. Request-free success remains
a successful structural
check; no independent Meaning is inferred from it. Binary identity pinning is
separately tracked by [#302](https://github.com/MGYamada/Qleisli/issues/302).
These reporting changes alter no acceptance rules, proof scope or admitted
constitutional guarantee.

## Public operations that confer no new acceptance

| Operation | Scope |
| --- | --- |
| `RawProgram`, `RawOp`, `native::Proposal::{new,from_raw}` | Untrusted IR or serialized proposals. Structural validity does not imply native acceptance. The 19 RawOp constructor coverage entries describe their checking coverage, not constructor authority. |
| `Circuit::new`, `Encoding::{new,identity}`, `Contract::new`, `FiniteMeaning::{permutation,phase,matrix,target_ir}`, `UnitaryBoundary::new`, matrix codecs | Descriptions, exact arithmetic and bounded host construction. A proposed meaning is not evidence that an implementation has that meaning. |
| `qleisli doc` → `render_markdown` | Reads/parses documentation and returns before source compilation. It confers no type or semantic acceptance. |
| Source loading, edition configuration and `Kernel::new` | Configure files or a checker path. Later checking can still fail. |
| Checked-object accessors and `check_binding` / `check_entry` | Retain or compare the original checked identity and scope; they do not perform a fresh semantic acceptance decision. |
| Foreign export | Consumes `AcceptedProgram` and emits target text. Input acceptance does not prove preservation of the emitted OpenQASM/QIR or target execution. QIRF export separately performs a fresh native validity check on its output; output validity alone is not a translation theorem. |
| `sim`, `host`, hierarchy execution and sampling | Execute already checked descriptions numerically. Acceptance and bounded reference tests do not establish runtime or floating-point preservation. |

OpenQASM/QIR export may replace three adjacent actual expanded function
steps, `H; Z; H`, with the existing X/CX/CCX word. The target axis and the
ordered zero, one or two controls, including polarity, must match in all three
steps; Z must have identity permutation and exact eighth-turn phases `[0,4]`.
No source name or inferred label authorizes this replacement, and no step
commutes across another. Nonmatching words retain the existing emitter policy.
The original accepted graph, source types, owners and dependencies remain intact.

A final target-word pass also recognizes exactly adjacent uncontrolled `H; Z; H`
on one identical physical operand, including words separated by pure Raw
operation boundaries. It reads the actual emitted gate definitions and operand
maps and uses the same native equation gate, receipt cache and export-wide work
counter. Allocation, singleton preparation, measurement and discard boundaries
prevent a window from crossing them. No phase folding, commuting or source-name
lookup creates a window. This pass starts only after the gate stream emitted by the existing cursor
normalization and lowering has satisfied the existing 4,096-gate cap; final
shortening cannot admit an otherwise over-limit emitted stream. Other target limits and original checked
obligations remain unchanged. This bounded local comparison is not a general
source, target-emission, physical-resource or external-QIS preservation theorem.

Each distinct compact original/replacement Raw pair requires the existing native
function-equation check under the input `AcceptedProgram`'s own checker. The
local comparison retains full scalar phase and ordered control polarities. An
export retains at most seven complete-body local receipts and shares the
existing 10,000,000 exact-work budget across all Raw operations. Unavailable
checking, rejection or exhausted capacity produces no artifact or alternate
acceptance path. These local equations do not establish general source/export,
resource or external QIS preservation; the two adopted guarantees and pending
QS/PR/RS/EXACT obligations retain their existing scopes.

Explicit module-map source selection parses, instantiates, elaborates and
lowers **untrusted proposals**. Ordinary commands with explicit entry/module
bindings use the shared source execution plan. `emit-proposal` writes
transport without constructing a kernel and reports `untrusted-proposal`.
The preselected Raw route uses ordinary native acceptance and then separately
compares the accepted instructions with the retained source steps. The
hierarchy route retains dedicated request, Fourier, instrument or named-QPE
checking and required initialization-move binding. A native failure cannot
switch routes or discard the caller's request. Selected checking/execution results retain
`source_meaning_verified: false`; native validity, producer consistency,
caller composition and named-QPE requests have distinct scopes. Neither
source-step comparison nor general lowering preservation follows merely from
an accepted proposal. See [selected-source execution](type-model.md#selected-source-execution)
for the remaining invocation and checking-profile boundaries.

Source roots with a checked public Isometry contract and an actual Unitary or
Isometry body use the supported Isometry profile through the existing
`check_instrument_native` boundary for fresh-zero preparation, checked unitary
evolution and a readout with zero measurements. A unitary body needs
no preparation step. This transport selection preserves the public bound and
does not rewrite its actual source-step or Raw effect to Isometry. The quantum
entry/result trees, zero-width owners and complete live frame remain part of
the proposal and its initialization-move comparison. At most one ordinary `Bits<0>` result may
accompany the quantum results; the transport's empty outcome does not create
a source Observe effect. Isometry execution returns its single unnormalized branch
with scalar phase retained. Sampling requires a checked public Observe contract
and an actually observing supported artifact. Conservative public bounds cannot
recover sharper source eligibility or fabricate actual operations; the Raw
profile keeps its actual classification and explicit support limits. A public
Observe contract over a pure body remains outside this hierarchy profile.

This adapter reuses component checks and introduces no new native primitive,
accepted-handle authority, formal theorem or constitutional guarantee. The
ordinary QLV1 ownership/scope admissions do not extend to this hierarchy path.
An independent hierarchy request must fit the supported composition language;
a whole-root finite-matrix request cannot replace a composite root's required
child structure. Producer consistency, the bounded initialization/source-step
comparison and numerical execution observations retain their separate scopes.
General source preservation and the complete native analytic/operator and
runtime correspondence duties remain pending.

## Durable coverage check

`tests/fixtures/verification_v029/coverage.json.xz` separates current implementation,
published 0.2.9 validation, unpublished development and open proof obligations.
It retains 46 coverage groups, 25 boundary entry lists, current constructor
variants and the 19 RawOp variants. The original groups and boundary lists are
preserved; engineering-only comparisons and the check-only nominal carrier
component have distinct classifications. There are 30 classified paths.
Mixed boundary rows refer to individually
classified paths; a public surface containing a constructor or `doc` is not
counted wholesale as native acceptance.

`scripts/check_production_coverage.py` checks the reviewed public surface,
complete path classifications, all fourteen native modes and dispatch targets,
named source/declaration bindings and existing regression functions. It fails
on an omitted route, a newly exposed boundary, changed dispatch, missing binding
or a proposal misclassified as acceptance. The native-contract proof scope also
retains the explicit encoded-equation and guarantee-admission limits. These
checks detect inventory drift;
source markers and test existence are not formal proof or evidence that a test
has just run. The underlying inventories, actual tests, proof builds and audits
remain necessary.

Existing regression bindings include `tests/native_paths.rs`,
`tests/function_evidence.rs`, `tests/semantic_contracts.rs`,
`tests/finite_leaf.rs`, `scripts/test_source_kernel.py`,
`scripts/test_interop_native.py`, `tests/hierarchical_host.rs`,
`tests/hierarchical_qpe_host.rs`, `tests/sized_source.rs`, and the explicit
no-kernel proposal test in `tests/sized_cli.rs`. The separate `doc` regression
is in `tests/cli.rs`. Their bounded observations do not replace S05 proofs or
human review of the intended semantics.

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
