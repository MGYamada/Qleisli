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
The selected development version **0.3.0-alpha is unpublished**. The historical
release record does not certify the changed alpha tree or its future packages.
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
reported work. `AcceptedProgram` adds the decoded execution view after a fresh
native decision. The hierarchy module has a **different** `NativeChecked` with
its own payload/request/candidate and finite-obligation scope. Its dedicated
protocol reports are not ordinary `AcceptedProgram` handles.

| Entry path | Artifact or request actually checked | Actual checker | Existing proof and remaining gap |
| --- | --- | --- | --- |
| Source/project/qrate checks and compilation; raw IR; function/meaning evidence; QIRF import, export, conversion and `verify-ir`; foreign/Python imports | Original QLV1 packet containing QIRF and an optional finite request. Source, evidence and foreign adapters produce these bytes. | `native::Kernel` → `--qirf-native` → `Cli.runValidity` → `Protocol.Validity.check` → `Qirf.Validity.inspect` | `Qleisli.NativeValidity.check_sound` binds success to `VerifiedMeaning`; `check_scopeSafe` covers classical scope. Full ordinary EffectSound/CPTP, source/foreign translation, emitted-output and runtime preservation remain separate. |
| `CheckedContract::check`, its checked compositions, and `check_computed` | QIRF root and `qleisli.native-contract` encoded equation | `Kernel::check_encoded` → `--qirf-contract` → `Protocol.NativeContract.check` → `Qirf.checkContract` | `Protocol.NativeContract.check_acceptance` binds the original bytes, decoded request and actual checking states. `Qleisli.NativeContract.check_encoded_sound` / `encoded_meaning` connect success to original-root `BodyMeaning`, the exact Basis interface and requested encoded equation. `Wrapper.circuitMatrix_entries` proves the actual wrapper's coefficient equality with the original matrix; `encoded_reference` extends the equation to any reference amplitude function. Source/compiler, compiled I/O, runtime/export, clean-release and quantitative resource claims remain separate; these theorems are not ledger admissions. |
| `finite_leaf::{check_unitary,check_serialized_unitary}` | QIRF root, signature, ordered input/output ports and exact matrix request | `Kernel::check_leaf` → `--qirf-contract` → `Protocol.NativeContract.check` → `Validity.checkRoot` and `Qirf.check` | `Qleisli.NativeContract.check_sound` / `leaf_meaning` compose native byte acceptance to original-body instrument meaning for the bounded closed unitary fragment, exact requested matrix, signature and ordered ports. The output port is tied to an actual verification. `leaf_reference_laws` extends both whole-space inverse laws to every finite reference. Source/runtime and broader effect/clean-release claims remain separate. |
| `hierarchical::Kernel::{inspect,inspect_native}` | Dedicated hierarchy payload and all required finite leaves | `--hierarchy-pending` → `Conditional.checkAll` and `HierarchicalFinite.checkLeaves` | `NativeHierarchy.conditional_derives` and `checkLeaves_semantics` bind structural derivation and finite meaning. Full analytic meaning-to-Operator composition remains open. |
| `hierarchical::Kernel::{check_against,check_against_native}`, ordinary request branch | Hierarchy payload and composition request | `--hierarchy-request-pending` → `Root.checkAll`, `checkLeaves` and `checkPairs` | `NativeHierarchy.requested_pairs` and finite-leaf results retain their stated premises; a producer comparison request proves consistency, not source preservation. |
| The same methods' Fourier branch | Hierarchy payload and Fourier request, including Hadamard obligations | `--hierarchy-fourier-pending` → `FourierRoot.checkAll`, `checkLeaves` and `checkHadamards` | `NativeHierarchy.hadamard_semantics` and `checkHadamards_semantics` establish finite obligations; complete analytic/source/runtime composition remains open. |
| `check_instrument` / `check_instrument_native` | Instrument payload and preparation/evolution/readout request | `--instrument-pending` → `Instrument.checkAll`, `checkLeaves` and `checkPairs` | `Instrument.checkAll_stages` / `checkAll_boundary` and native finite results cover components. They do not establish complete source or host execution preservation. |
| `check_qpe_instrument` / `check_qpe_instrument_native` | Instrument payload, named provider request and candidate binding | `--qpe-instrument-pending` → `QpeInstrument.checkAll`, `checkLeaves`, `checkPairs` and `checkHadamards` | Named structural and finite obligations are checked. The complete native analytic Operator bridge and general source-QPE meaning remain open. |
| Private readout and preparation protocols | QLM1 readout and QLZ1 preparation packets | `--readout-check` → `Readout.check`; `--preparation-check` → `Preparation.check` | Component `check_reference` / `check_boundary` results retain explicit premises. These reports are not complete program handles or runtime guarantees. |
| Phase-word, phase DAG, layout, layout DAG and phase-layout file protocols | Separate component artifacts and requirements | `Cli.Finite` → `verify`, `Hierarchy.check`, `Layout.check`, `LayoutDag.check`, `PhaseLayout.check` | Existing phase/layout component results do not extend automatically to ordinary production programs. |
| `Finite.check` / `checkAll`, `circuitMatrix`, `FiniteCodec.readMatrix` | Finite circuits, contracts or serialized matrices | Finite checking, evaluation or decoding, respectively | Finite component theorems have explicit inputs. Evaluation and decoding alone are not acceptance; composition with each actual production root is required. |

`lean-kernel/Main.lean` dispatches the nine explicitly versioned native modes.
`lean-kernel/Cli/Validity.lean` selects the ordinary or contract root;
`lean-kernel/Cli/Hierarchical.lean` composes the dedicated hierarchy checks.
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

### Original-artifact control-sector requests

The existing version-paired `--qirf-contract` gate also accepts a strictly
decoded `qleisli.native-contract` version-1 request with `kind: "control"`.
Its complete field set is `format`, `version`, `kind`, `signature`, and `axes`.
`signature` is the exact QIRF basis tree; `axes` is an ordered list of distinct
physical bit positions in that interface. Extra fields, including a proposed
matrix or producer success flag, reject. The original QLV1 packet format and
encoded/leaf request contracts remain unchanged.

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
projection must match the original roots. Both bodies must have principal
Observe effects; an Observe annotation on a pure body supplies no evidence.
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
Ordinary concrete `apply_contract` executes only the implementation and checks
its actual emitted interval again against the immutable reference. Its private
call sidecar retains original ports, instructions, result IDs and source span;
the enclosing root has its separate ordinary acceptance. Unused original
closed obligations are also checked. These sidecars do not change QIRF or set a
request-free root's `request_checked` or `source_meaning_verified` to true.
Explicit specialization and independent source replay of the observing
overload remain open; that route rejects pending obligations. This grants no observing Meaning, coherent control
or adjoint access. Pure Meaning retains its exact phase rule. Request-free
whole-root inspection still reports no independent requested meaning. Source,
decoder, native compilation/runtime and emitted-artifact preservation remain
separate obligations; these lemmas admit no constitutional guarantee.

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

Principal Isometry source roots in the selected hierarchy use the existing
`check_instrument_native` boundary for fresh-zero preparation, checked unitary
evolution and a readout with zero measurements. The quantum entry/result trees,
zero-width owners and complete live frame remain part of the proposal and its
initialization-move comparison. At most one ordinary `Bits<0>` result may
accompany the quantum results; the transport's empty outcome does not create
a source Observe effect. Isometry execution returns its single unnormalized branch
with scalar phase retained. Sampling requires a principal Observe source root,
independently of the chosen native transport or optional source annotation.

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

`tests/fixtures/verification_v029/coverage.json` separates current implementation,
published 0.2.9 validation, unpublished development and open proof obligations.
It retains all 36 coverage groups, 20 boundary entry lists, current constructor
variants and the 19 RawOp variants. Mixed boundary rows refer to individually
classified paths; a public surface containing a constructor or `doc` is not
counted wholesale as native acceptance.

`scripts/check_production_coverage.py` checks the reviewed public surface,
complete path classifications, all nine native modes and dispatch targets,
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

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
