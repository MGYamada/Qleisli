# Current production verification boundary

The **production verification boundary** is the set of entry paths that reach
the native checker, together with what each check establishes. The **native
checker** is the Lean executable that `lean-kernel/` builds. A **mode** is one
dispatch argument of the native checker, such as `--runtime-root-check`. An
**entry path** is a Rust API or a CLI command that submits bytes to a mode.
For each mode, this chapter states the request that the mode reads, the rules
that the native checker applies, the Lean theorems that bind the check, and
the obligations that no theorem discharges.

The chapter is subordinate to the [authority hierarchy](authority.md), the
adopted single-verifier decision that [History](#history) cites, and
repository `TRUSTBOUNDARY.md`. It does not discharge a constitutional
obligation or widen an existing theorem. Source paths identify files in the
[Qleisli repository](https://github.com/MGYamada/Qleisli).

Production acceptance has one implementation, the native checker.

Rules:

- Rust generates proposals, selects and invokes the compatible checker,
  retains immutable checked bytes, decodes views, reports diagnostics and
  executes simulations.
- A missing, incompatible or failing native checker rejects. The retired Rust
  verifier and the dual-acceptance fallback are absent.
- Not every public function invokes Lean or grants acceptance.
  [Public operations that confer no acceptance](#public-operations-that-confer-no-acceptance)
  lists the operations that do neither.

## Constitutional theorem boundary

The boundary below applies to the implementation that this chapter describes,
under [the adopted interpretations](../design/initial-interpretations.md) and
the single-verifier decision.

```text
Source or external artifact, with its requested contract when present
    |
    v
Elaboration or adaptation proposes artifact and evidence bytes
    |
    v
------------ independent production acceptance boundary ------------
Native Lean gate checks the actual bytes, profile and applicable evidence
    |
    v
Accepted judgment binds the decoded artifact, contract and evidence
    |
    +--> QS  Independent semantics of the accepted artifact
    +--> PR  Checked correspondence of an admitted target artifact
    +--> RS  Checked bounds on accepted behavior and admitted realization
```

The **accepted judgment** of a mode is the success of its Lean check on the
submitted bytes.
[Entrypoints and actual checked representations](#entrypoints-and-actual-checked-representations)
identifies the judgment and the checked representation of each mode. The two
[admitted scoped guarantees](../design/initial-guarantees.md) concern
ownership and classical scope of the original decoded ordinary root.

Under the adopted interpretations, the three obligations concern these
subjects:

| Obligation | Subject |
| --- | --- |
| QS | The declared typing, ownership, effect and exact semantic contracts of the actual accepted object |
| PR | Forward correspondence from that meaning to the actual admitted target artifact, under its target and workspace premises |
| RS | Finite, checked bounds for the accepted behavior and the applicable realization, under the stated resource model |

Their broader proof obligations and the strict exactness obligations are
pending.

Rules:

- Elaboration must preserve the specified source meaning for every claimed
  source scope. Its evidence links the original source and dependency
  contracts to the checked artifact, including its owners, ordered axes,
  effects and exact phase.
- A successful artifact check establishes the covered artifact properties. A
  preservation theorem or independent validation must establish the source
  correspondence separately.
- The same rule applies to an adapter that claims preservation of a foreign
  input, and to a backend that claims preservation in emitted output.
- Source syntax that a later change adds may elaborate under the same edition
  whenever it preserves the adopted contracts.
- A replacement checked representation must carry the applicable current
  guarantees through justified semantic transport.
- Every frontend and backend that claims constitutional acceptance must use
  the applicable native gate and its current evidence.
- Missing evidence or a failed check rejects the claimed scope.

## Entrypoints and actual checked representations

The table below maps each entry path to the bytes that its mode checks. It
uses these names:

- `native::Kernel` means `interchange::native::Kernel`.
- The ordinary `NativeChecked` of that kernel retains the artifact, the
  optional request, the checker identity and the reported work.
- An **accepted handle** is an `AcceptedProgram`. It retains its predecoded
  execution view only after a fresh QLV3 native comparison of that exact graph
  and its caches. Inspection alone does not authorize execution.
  [QDV1 and the envelope](execution-view.md) specify the compared data and
  scope.
- The hierarchy module has a different `NativeChecked`, with its own payload,
  request and candidate and its own finite-obligation scope. Its dedicated
  protocol reports are not ordinary `AcceptedProgram` handles.

| Entry path | Artifact or request that the mode checks | Mode and checker | Proof scope and open obligations |
| --- | --- | --- | --- |
| Source/project/qrate checks and compilation; raw IR; function/meaning evidence; QIRF import, export, conversion and `verify-ir`; foreign/Python imports | QLV3 envelope containing the original QLV1 QIRF/request packet and the actual retained execution view when execution is requested. Source, evidence and foreign adapters produce these bytes. | `native::Kernel` → `--qirf-native` → `Protocol.NativeContext.run` → `ExecutionView.Native.ordinary` → the original QIRF check and requested view comparison | [Ordinary QIRF root requests](#ordinary-qirf-root-requests) |
| `CheckedContract::check`, its checked compositions, and `check_computed` | QIRF root and `qleisli.native-contract` encoded equation | `Kernel::check_encoded` → `--qirf-contract` → `ExecutionView.Native.contract` → `Protocol.NativeContract.checkRetained` → `Qirf.checkContract` | [Encoded and square-leaf requests](#encoded-and-square-leaf-requests) |
| `finite_leaf::{check_unitary,check_serialized_unitary}` | QIRF root, signature, ordered input/output ports and exact matrix request | `Kernel::check_leaf` → `--qirf-contract` → `ExecutionView.Native.contract` → `Protocol.NativeContract.checkRetained` → `Validity.checkRoot` and `Qirf.check` | [Encoded and square-leaf requests](#encoded-and-square-leaf-requests) |
| `pure_leaf::check_pure` | QIRF root, separate domain/codomain type trees, ordered owner ports and exact rectangular matrix | `Kernel::check_pure_leaf` → `--qirf-contract` → `ExecutionView.Native.contract` → `Protocol.NativeContract.checkRetained` → `Qirf.PureLeaf.check` | [Rectangular pure-leaf requests](#rectangular-pure-leaf-requests) |
| `Kernel::check_carrier`; explicit `Instantiation::check_carrier` source adapter | Original QIRF/dependencies, both ordered nominal owner forests, original declaration sources and an independent exact logical matrix | `--carrier-pure-check` → `ExecutionView.CheckedCarrier.run` → `Protocol.Carrier.check` → original source checks and `Qirf.Carrier.check` | [Finite nominal carrier requests](#finite-nominal-carrier-requests) |
| `Kernel::check_ordinary_root` | Original QIRF/dependencies and the `qleisli.ordinary-root-request` version-2 request, profile `finite-ordinary-root-v2` | `--ordinary-root-check` → `CheckedOrdinaryRoot.run` | [Ordinary input/result requests](#ordinary-inputresult-requests) |
| `Kernel::check_runtime_root` | Original QIRF/dependencies and the `qleisli.runtime-root-request` version-2 request, profile `finite-runtime-root-v2` | `--runtime-root-check` → `CheckedRuntimeRoot.run` | [Mixed runtime root requests](#mixed-runtime-root-requests) |
| `Kernel::check_qmatch_source` | Original QIRF/dependencies and the `qleisli.qmatch-request` version-4 request | `--qmatch-source-check` → `CheckedQmatch.run` | [Version 4: named-arm component requests](#version-4-named-arm-component-requests) |
| `Kernel::check_qmatch_source_v5` | Original QIRF/dependencies and the `qleisli.qmatch-request` version-5 request | `--qmatch-source-v5-check` → `CheckedQmatchV5.run` | [Version 5: source-body requests](#version-5-source-body-requests) |
| `engineering_pure::{check_with_kernel,check_serialized_with_kernel}` and `engineering compare-pure` | Original actual and ideal QIRF artifacts and the closed pure comparison request | `--engineering-pure-check` → `CheckedEngineeringPure.run` | [Native pure engineering comparison](realization.md#native-pure-engineering-comparison) states the checked bound. The reply is `engineering-checked`, not an accepted handle. |
| `engineering_pure_tensor::{check_with_kernel,check_serialized_with_kernel}` and `engineering compare-pure-tensor` | Original actual and ideal QIRF artifacts and the closed ordered tensor comparison request | `--engineering-pure-tensor-check` → `CheckedEngineeringPureTensor.run` | [Native ordered pure tensor comparison](realization.md#native-ordered-pure-tensor-comparison) states the checked bound. The reply is `engineering-checked`, not an accepted handle. |
| `engineering_instrument::{check_with_kernel,check_serialized_with_kernel}` and `engineering compare-instrument` | Original actual and ideal QIRF artifacts and the closed instrument comparison request | `--qirf-engineering-instrument-native` → `Native.engineeringInstrument` | [Instrument engineering comparison](realization.md#instrument-engineering-comparison) states the checked bound. The reply is `engineering-checked`, not an accepted handle. |
| `engineering_openqasm::{check_with_kernel,check_serialized_with_kernel}` and `engineering compare-openqasm3` | Literal canonical target bytes, original ideal/dependencies, exact Unit/Bit signatures, closed epsilon/majorants and the complete retained QDV1 view | `--engineering-openqasm-check` → `CheckedEngineeringOpenQasm.run` → independent byte decode and unchanged complete instrument checks | `NativeEngineeringOpenQasmProtocol.run_meaning` binds the literal target and original ideal to the actual checking execution. `run_complete_adjoint_bound` covers every finite reference. The private report is engineering-only, without an actual `AcceptedProgram`, source/export-preservation, pure/control, cleanup, hardware, resources or constitutional PR/RS claim. |
| `engineering_openqasm_gate::compare_serialized_with_kernel` and `engineering compare-openqasm3-gate` | Literal OpenQASM gate definition, exact ideal slices and the requested sequential or controlled approximation with resource accounting | `--engineering-openqasm-gate-check` → `CheckedEngineeringOpenQasmGate.run` → `Protocol.EngineeringOpenQasmGate.checkRetained` and retained QDV1 comparison | `NativeEngineeringOpenQasmGate.sequential_reference_bound` and `controlled_reference_bound` bound the literal operator difference on arbitrary finite references. Report authority is limited to the checked engineering request. |
| `AcceptedProgram::check_openqasm_placement`, internal to OpenQASM export | The accepted program's retained version-5 qmatch request and execution view, the emitted OpenQASM target bytes and their alignment | `--openqasm-placement-check` → `CheckedQmatchV5.PlacementPacket.check` | The reply is `placement-checked` with target resource counts, not an accepted handle. This chapter states no proof for this mode. |
| `hierarchical::Kernel::{inspect,inspect_native}` | Dedicated hierarchy payload and all required finite leaves | `--hierarchy-pending` → `Conditional.checkAll` and `HierarchicalFinite.checkLeaves` | `NativeHierarchy.conditional_derives` and `checkLeaves_semantics` bind structural derivation and finite meaning. Full analytic meaning-to-Operator composition is open. |
| `hierarchical::Kernel::{check_against,check_against_native}`, ordinary request branch | Hierarchy payload and composition request | `--hierarchy-request-pending` → `Root.checkAll`, `checkLeaves` and `checkPairs` | `NativeHierarchy.requested_pairs` and finite-leaf results retain their stated premises; a producer comparison request proves consistency, not source preservation. |
| Selected pure hierarchy source with `ctrl` | One hierarchy composition, compared plan and each original call's replayed node index, ordered basis forest and control roles | `--hierarchy-control-pending` → `Root.checkAll`, finite leaves and pairs, and `HierarchicalFinite.checkControls` | `ControlAccess.check_bound` binds the native sector predicate to the executable action of the selected node. Source occurrence replay and the general source/resource correspondence have separate scopes. |
| The same methods' Fourier branch | Hierarchy payload and Fourier request, including Hadamard obligations | `--hierarchy-fourier-pending` → `FourierRoot.checkAll`, `checkLeaves` and `checkHadamards` | `NativeHierarchy.hadamard_semantics` and `checkHadamards_semantics` establish finite obligations; complete analytic/source/runtime composition is open. |
| `check_instrument` / `check_instrument_native` | Instrument payload and preparation/evolution/readout request | `--instrument-pending` → `Instrument.checkAll`, `checkLeaves` and `checkPairs` | `Instrument.checkAll_stages` / `checkAll_boundary` and native finite results cover components. They do not establish complete source or host execution preservation. |
| `check_qpe_instrument` / `check_qpe_instrument_native` | Instrument payload, named provider request and candidate binding | `--qpe-instrument-pending` → `QpeInstrument.checkAll`, `checkLeaves`, `checkPairs` and `checkHadamards` | Named structural and finite obligations are checked. The complete native analytic Operator bridge and general source-QPE meaning are open. |
| Private readout and preparation protocols | QLM1 readout and QLZ1 preparation packets | `--readout-check` → `Readout.check`; `--preparation-check` → `Preparation.check` | Component `check_reference` / `check_boundary` results retain explicit premises. These reports are not complete program handles or runtime guarantees. |
| Phase-word, phase DAG, layout, layout DAG and phase-layout file protocols | Separate component artifacts and requirements | `Cli.Finite` → `verify`, `Hierarchy.check`, `Layout.check`, `LayoutDag.check`, `PhaseLayout.check` | Existing phase/layout component results do not extend automatically to ordinary production programs. |
| `Finite.check` / `checkAll`, `circuitMatrix`, `FiniteCodec.readMatrix` | Finite circuits, contracts or serialized matrices | Finite checking, evaluation or decoding, respectively | Finite component theorems have explicit inputs. Evaluation and decoding alone are not acceptance; composition with each actual production root is required. |

> **Implementation note.** `lean-kernel/Main.lean` dispatches the explicitly
> versioned native modes, including mechanically separate engineering
> comparisons. `lean-kernel/Cli/NativeContext.lean` invokes the pure
> `Protocol.NativeContext.run` dispatcher and its single reply projection. It
> checks the original QLV3 edition and compiled product before applying each
> mode's existing gate. The strict version-3 reply binds that same context.
> The older IO adapters are unused and await retirement after replacement
> conformance coverage. They are not fallback entry points.

These files contain the bridge theorems that the table and the sections below
cite by name:

| File | Cited theorems |
| --- | --- |
| `lean/Qleisli/NativeValidity.lean` | `check_sound`, `check_scopeSafe` |
| `lean/Qleisli/NativeContract.lean` | `check_sound`, `check_encoded_sound`, `encoded_meaning`, `encoded_reference`, `leaf_meaning`, `leaf_reference_laws`, `control_meaning`, `control_reference`, `control_owners_meaning`, `control_owners_reference`, `instrument_meaning` |
| `lean/Qleisli/NativeContractWrapper.lean` | `Wrapper.circuitMatrix_entries` |
| `lean/Qleisli/NativePureLeaf.lean` | `pure_leaf_meaning`, `pure_leaf_reference` |
| `lean/Qleisli/ControlAccess.lean` | `checked_owners_meaning`, `checked_owners_action_project` |
| `lean/Qleisli/NativeHierarchy.lean` | `conditional_derives`, `checkLeaves_semantics`, `requested_pairs`, `hadamard_semantics`, `checkHadamards_semantics` |
| `lean/Qleisli/NativeEngineeringOpenQasmProtocol.lean` | `run_meaning`, `run_complete_adjoint_bound` |
| `lean/Qleisli/NativeEngineeringOpenQasmGate.lean` | `sequential_reference_bound`, `controlled_reference_bound` |
| `lean-kernel/Protocol/ExecutionView/Native.lean` | `ordinary_original` |
| `lean-kernel/Protocol/NativeContract.lean` | `check_acceptance` |
| `lean-kernel/QleisliKernel/Hierarchical/ControlAccess.lean` | `ControlAccess.check_bound` |
| `lean-kernel/QleisliKernel/Hierarchical/Instrument.lean` | `Instrument.checkAll_stages`, `checkAll_boundary` |
| `lean-kernel/QleisliKernel/Hierarchical/Readout.lean`, `lean-kernel/QleisliKernel/Hierarchical/Preparation.lean` | `check_reference`, `check_boundary` |

`lean/Qleisli/Qirf.lean` defines the graph denotation that these bridge files
use. It contains none of the theorems that this chapter cites by name.

## Ordinary QIRF root requests

The mode `--qirf-native` checks an ordinary QIRF root. The first row of the
entry-path table lists its entry paths and its bytes. The bytes are a
[QLV3 envelope](execution-view.md#native-envelope-cutover) that holds the
original QLV1 packet, with its optional independent request, and the retained
execution view when the caller requests execution.

Rules:

- The accepted judgment is the success of
  `QleisliKernel.Protocol.ExecutionView.Native.ordinary` on the QLV3 payload at
  its requested scope, reached through `Protocol.NativeContext.run`.
- Execution also requires comparison of the retained view against the view
  that Lean decodes.

Proof scope:

- `ordinary_original` binds the accepted judgment to
  `Protocol.Validity.Acceptance` for the original QLV1 packet. That witness
  identifies the decoded `Qirf.Artifact`, the order and the optional
  independent request. It also identifies the success of
  `Qirf.Validity.inspect` on those exact values.
- `Qleisli.NativeValidity.check_sound` binds success to `VerifiedMeaning`.
- `check_scopeSafe` covers classical scope.

Not established:

- Full ordinary EffectSound/CPTP is a separate obligation.
- Source translation preservation and foreign translation preservation are
  separate obligations.
- Emitted-output preservation and runtime preservation are separate
  obligations.

## Native contract requests

The mode `--qirf-contract` reads a strictly decoded `qleisli.native-contract`
version-1 request beside the original QIRF root. The field `kind` selects one
of six request kinds:

| `kind` | Fields | Section |
| --- | --- | --- |
| `encoded` | `format`, `version`, `kind`, `contract` | [Encoded and square leaf](#encoded-and-square-leaf-requests) |
| `leaf` | `format`, `version`, `kind`, `signature`, `input`, `output`, `matrix` | [Encoded and square leaf](#encoded-and-square-leaf-requests) |
| `pure-leaf` | `format`, `version`, `kind`, `domain`, `codomain`, `input`, `output`, `matrix` | [Rectangular pure leaf](#rectangular-pure-leaf-requests) |
| `control` | `format`, `version`, `kind`, `signature`, `axes` | [Control sector](#original-artifact-control-sector-requests) |
| `control-owners` | `format`, `version`, `kind`, `signatures`, `axes` | [Control sector](#original-artifact-control-sector-requests) |
| `instrument` | `format`, `version`, `kind`, `actual_signature`, `expected_signature`, `identity`, `expected_artifact` | [Observing instrument](#original-artifact-observing-instrument-requests) |

Rules:

- The inner QLV1 format is the same for every kind. An external call requires
  the QLV3 envelope and its scope.
- The `control` kind changes neither the inner QLV1 format nor the encoded and
  leaf request contracts.

Proof scope:

- The native-contract bridge is specific to `Protocol.NativeContract.check`.
  It does not inherit the theorem for the ordinary `Protocol.Validity.check`
  root.
- Its `Acceptance` witness retains the original QLV1 body and request bytes,
  the UTF-8/JSON decoding, the artifact and order, the requested signature,
  the ordered ports and the exact matrix or encoded contract, with continuous
  work states. These are necessary success facts. They are not a converse
  characterization of every parser constraint.
- `Protocol.NativeContract.check_acceptance` binds the original bytes, the
  decoded request and the actual checking states.
- `tests/fixtures/constitution_v030/native-contract-bridge/` preserves the
  unchanged executable prefix, the printed theorem and predicate types, the
  axiom sets and a validation record.

Not established:

- The identity and proof checks of that fixture admit no guarantee and do not
  close S05.
- They establish no source/compiler, deployed-binary, Rust rematerialization,
  target/runtime or quantitative Resource Safety claim.

### Encoded and square-leaf requests

The entry-path table gives the entry paths and the checked bytes of the kinds
`encoded` and `leaf`.

Rules:

- The square `kind: "leaf"` protocol keeps its two-sided unitary conditions.
  It is available beside the rectangular kind.

Proof scope:

- `Qleisli.NativeContract.check_encoded_sound` and `encoded_meaning` connect
  success to original-root `BodyMeaning`, the exact Basis interface and the
  requested encoded equation. Through `EncodedMeaning`, the encoded branch
  retains that `BodyMeaning`, the complete Basis interface and the checked
  encoded equation.
- `Wrapper.circuitMatrix_entries` proves the coefficient equality of the
  actual wrapper with the original matrix.
- `encoded_reference` extends the equation to any reference amplitude
  function.
- `Qleisli.NativeContract.check_sound` and `leaf_meaning` compose native byte
  acceptance to original-body instrument meaning. They cover the bounded
  closed unitary fragment, the exact requested matrix, the signature and the
  ordered ports. The output port is tied to an actual verification.
- `leaf_reference_laws` extends both whole-space inverse laws to every finite
  reference. The leaf conclusion retains complex phase. Its arbitrary
  finite-reference laws require no separability or normalization premise.

Not established:

- For the kind `encoded`: source/compiler, compiled I/O, runtime/export,
  clean-release and quantitative resource claims are separate. The theorems
  are not ledger admissions.
- For the kind `leaf`: source/runtime claims and broader effect and
  clean-release claims are separate.
- The bounded original-root results of both kinds do not establish source,
  deployed-binary or host execution correspondence.

### Rectangular pure-leaf requests

The mode `--qirf-contract` accepts `qleisli.native-contract` version 1 with
`kind: "pure-leaf"`. Its complete fields are `format`, `version`, `kind`,
`domain`, `codomain`, `input`, `output` and `matrix`.

Rules:

- Both types use exact QIRF basis trees. The ports retain token, ordered wires
  and bit shape.
- Unknown fields, unknown versions and producer acceptance flags reject.
- The original QIRF root interface describes a unary pure function with
  independent input and output types. Its structural check requires a Unitary
  or Isometry effect, no classical ports, one input and one actual live output
  owner, and the corresponding input and output widths.
- The literal original-body reader finds the output owner. The input width
  does not stand for the output width.
- Ordinary validity alone does not establish an external matrix equation.
- `PureLeaf.check` freshly checks the original dependency graph and body. It
  binds both exact type trees and both ordered ports, reconstructs every input
  column, and checks exact equality to the requested matrix and `V†V = I`.
- Reconstruction retains the original effect checks, complete classical
  branches and hidden observation histories. Measurement, reset and discard
  cannot be relabeled pure or erased from the equation.
- Zero-width owners, exact phase and axis order are part of the obligation.
- Both endpoint dimensions keep the six-bit dense bound and the shared
  exact-work accounting. The kind adds no unbounded matrix API.
- Every receipt requires fresh native acceptance, including a receipt that
  uses previously checked dependency data.

> **Implementation note.** `CheckedPureLeaf` is a private-construction receipt
> over immutable original artifact and request bytes. Rust boundary
> construction and matrix serialization validate untrusted data shape only.

> **Implementation note.** The ordinary frontend retains `SourcePureEquation`
> sidecars on its accepted entry. A sidecar holds independently checked
> implementation and reference leaves, their exact matching domain, codomain
> and matrix, the resolved names and the original source text. Constructor
> lowering rechecks actual renamed Raw fragments against the derived matrix.
> Selected Raw lowering retains its original Meaning requests and checks
> actual instruction intervals. The refined finite-leaf path of the hierarchy
> is square and refuses rectangular Meaning obligations.

Proof scope:

- `pure_leaf_meaning` binds fresh graph and root checking to the original body
  and the exact Gram identity.
- `pure_leaf_reference` preserves inner products for arbitrary joint reference
  amplitudes.

Not established:

- The check grants neither inverse nor control access. It supplies no
  source/runtime correspondence, target realization or quantitative resource
  evidence.
- Source snapshots provide provenance. Neither sidecar is a general
  source-preservation proof, an arbitrary whole-entry functional specification
  or a constitutional guarantee.

### Original-artifact control-sector requests

The mode `--qirf-contract` accepts two kinds that request a control-sector
check of an original artifact:

| Request | Complete field set | Content |
| --- | --- | --- |
| `kind: "control"` | `format`, `version`, `kind`, `signature` and `axes` | `signature` is the exact QIRF basis tree. `axes` is an ordered list of distinct physical bit positions in that interface. |
| `kind = "control-owners"` | `format`, `version`, `kind`, `signatures` and `axes` | `signatures` is the requested basis forest of an original call with several ordered quantum ports. |

Rules:

- A `control` request with an extra field rejects, including a proposed
  matrix or a producer success flag.
- A `control-owners` request carries exactly its five fields. It accepts
  neither a proposed matrix nor a success receipt.
- Lean checks the original graph, root, dependency evidence and identical
  input/output interface. It reconstructs the actual action and checks
  whole-space unitarity. It then requires every matrix entry between different
  requested computational-basis sectors to be exactly zero.
- The six-bit finite reconstruction limit and continuous work accounting
  apply.
- An empty axis list is meaningful for a zero-width logical owner. It does not
  erase ownership or nontrivial phase.
- The internal `Qirf.ControlAccess.checkOwners` component checks an original
  call with several ordered quantum ports, without constructing a single-port
  packing wrapper. The requested basis forest must match the original input
  and live returned owner widths and positions, including zero-width owners.
- Raw bit widths do not establish source type trees. The requested forest
  requires binding to the original checked source.

Rules for source `ctrl` calls:

- The Finite project path binds the `control-owners` request to each actual
  emitted control-call interval, to the original ordered owner ports and basis
  forest, and to the returned tokens, before it updates source bindings. It
  checks nested calls and unused concrete declarations. The complete final
  artifact also requires ordinary native acceptance.
- Selected source projection retains the original ordered access roles with
  the source identities and positions of the call, including public `ctrl`
  occurrences. Elaboration checks the exact owner shape and actual effect. It
  neither grants sector authority nor rewrites the role to `excl`.
- Checker-free Raw lowering and hierarchical lowering reject retained control
  roles.
- Native-checked Selected Raw lowering independently checks every retained
  control-bearing concrete body and the selected root. It then replays its
  actual decoded calls with fresh sector requests. Final consumption repeats
  native acceptance and source replay. Retaining a role or an earlier success
  is not acceptance authority.
- The common judgment records each original control call as a pending sector
  obligation. Native-checked Selected Raw lowering requires every original
  obligation to have a concrete interval in each retained specialization of
  its declaration. A program with an absent interval is unsupported. One
  specialization cannot cover the missing call of another.
- Unused original declarations, unselected branches, empty loops and
  zero-count providers cannot erase the obligation or its location. Retained
  zero-count provider bodies are checked before root emission.
- Control replay without a native checker refuses.
- Symbolic inverse or controlled replay refuses retained control roles. Its
  transformed trace does not supply the original call intervals that the
  native bridge requires.
- Zero-count and unused-provider obligations must be covered before selected
  transport can be admitted. Empty output does not waive them.

> **Implementation note.** The internal Raw replay bridge can discharge a
> retained control obligation with the checker of the accepted original
> artifact. It selects the actual instruction interval that replay consumes,
> its input and returned tokens and its ordered source basis forest. It then
> submits a fresh `control-owners` request. It takes no producer-supplied call
> body, matrix or success receipt.
>
> Work is shared across these decisions within the exact-work ceiling. The
> checked Raw entry shares this budget across all body and root decisions. It
> refuses an increased ceiling, exhaustion or an unavailable checker.
> Regression tests use original public control source graphs as well as
> private graph mutations.

Proof scope:

- `Protocol.NativeContract.ControlAcceptance` and `check_acceptance` retain
  the original body and request bytes, the exact decoded signature and axes,
  and the actual checker execution.
- `Qleisli.NativeContract.control_meaning` connects the same action to
  original-root `BodyMeaning`, its exact interface, the sector condition and
  the inverse laws.
- `control_reference` proves projector commutation on arbitrary joint complex
  amplitudes with any external reference. Phase kickback and entanglement are
  permitted. The result does not assert an unchanged reduced control state or
  separability.
- `checked_owners_meaning` and `checked_owners_action_project` bind the actual
  root, its dependencies and the full complex action to the sector law.
- `ControlOwnersAcceptance` retains the decoded ordered forest and
  coordinates, the original packet bytes and the actual checking execution.
- `control_owners_meaning` and `control_owners_reference` extend the
  original-body result and the arbitrary-reference result to the
  `control-owners` request.

Not established:

- The `control` request alone does not enable source `ctrl` calls.
- Original source places, call-specific artifact identity, aliasing, access
  lifetimes, lowering and execution correspondence, and quantitative resource
  and scheduling claims are separate obligations.
- The two kinds introduce no native mode, external schema admission or
  constitutional guarantee.
- Neither an annotation nor native unitarity alone supplies control-sector
  evidence.
- Host source lowering and interval extraction are not a Lean
  source-preservation theorem.
- AST-to-step preservation, Rust decoding and interval extraction are
  separate obligations. The Raw replay bridge is a host bridge, not a Lean
  source-preservation theorem.

### Original-artifact observing instrument requests

The mode `--qirf-contract` accepts `kind = "instrument"` in
`qleisli.native-contract` version 1. Its exact fields are `format`, `version`,
`kind` and the four below:

| Field | Content |
| --- | --- |
| `actual_signature`, `expected_signature` | Each signature has exactly `input` and `result`. `input` is the QIRF basis tree. `result` is a complete result tree. |
| `identity` | Exactly `implementation`, `specification` and `sources`. Each source has exactly `path` and `text`. |
| `expected_artifact` | The original expected QIRF JSON as a UTF-8 string |

The complete result tree uses these exact objects:

| Result | Fields |
| --- | --- |
| Ordinary Unit or Bit | `{"tag":"unit"}` or `{"tag":"bit"}` |
| Ordinary Bits | `{"tag":"bits","width":N}`, with a u32 natural width, including zero |
| Quantum owner | `{"tag":"quantum","basis":B}`, with the complete QIRF basis tree |
| Pair | `{"tag":"pair","left":L,"right":R}` |
| Tuple of at least three values | `{"tag":"tuple","fields":[...]}` |

Rules:

- Supplied matrices, receipts, success flags, missing fields and extra fields
  reject.
- The actual QIRF is the original QLV1 body. The checker freshly checks both
  complete graphs, both selected roots and the dependency evidence.
- The kind changes neither the QLV1 framing, the QIRF representation nor the
  other request kinds.
- The signatures must agree as entire trees, including Unit, Bits<0>,
  zero-width quantum owners and product nodes.
- The ordered quantum owners and the classical projection must match the
  original roots.
- Source consumers select this contract by caller-visible Observe effects.
- The native profile requires genuinely observing original artifacts. A
  conservative Observe bound on a pure body neither rewrites its Raw
  classification nor authorizes a pure contract fallback.
- Unsupported concrete pairs refuse, including unused ones.
- The native profile has one quantum input and no runtime classical inputs.
- Signatures are requested type data. Native widths alone do not reconstruct
  the full types of the source or prove their preservation.
- The equality has no tolerance.

| Limit | Value |
| --- | --- |
| Sources in `identity` | 128, with the name and path bounds |
| Aggregate identity bytes | 1 MiB |
| Depth of a result tree | 64 |
| Nodes of a result tree | 4,096 |
| Dense reconstruction | Six bits, with the shared work and JSON limits |
| Transport | 16 MiB |

> **Implementation note.** The private Rust instrument handle retains both
> original accepted artifacts, the complete signature, the source identity and
> the fresh paired native decision. Both concrete `apply_contract` adapters
> execute only the implementation. They check its actual emitted interval
> again against the immutable reference. Each private call sidecar retains the
> original ports, instructions, result IDs and source span. The enclosing root
> has its separate ordinary acceptance. Unused original closed obligations
> are also checked.
>
> Selected Raw preparation independently replays the original implementation.
> It then checks the consumed instruction interval, the actual input owner and
> the ordered result through a fresh native equation. The retained proposal
> keeps the original pairs and private call sidecars. Later source validation
> checks again with the checker of the accepted artifact. Dependencies, unused
> declarations and zero-count children keep their original obligations.
> Hierarchy lowering and checker-free emission reject this overload.

Proof scope:

- `Protocol.NativeContract.InstrumentAcceptance` retains the original decoded
  request, the original expected text, the fresh expected graph and continuous
  checking states.
- `Qleisli.NativeContract.instrument_meaning`, `check_sound` and
  `check_encoded_sound` connect success to both original-body instrument
  meanings, complete Kraus sums and untruncated dimensions. They also connect
  it to identical unnormalized public outcome maps on any joint matrix with a
  finite external reference.
- The independent reference in `Qleisli.Semantics.InstrumentEquality` sums all
  hidden histories. Neither their count nor their labels are public outcomes.

Not established:

- The check grants no observing Meaning, coherent control or adjoint access.
  Pure Meaning retains its exact phase rule.
- The sidecars do not change QIRF. They do not set `request_checked` or
  `source_meaning_verified` of a request-free root to true. Request-free
  whole-root inspection reports no independent requested meaning.
- Source, decoder, native compilation/runtime and emitted-artifact
  preservation are separate obligations.
- The lemmas admit no constitutional guarantee.

## Finite nominal carrier requests

The internal mode `--carrier-pure-check` checks a pure body between two
nominal owner forests against an independent exact logical matrix.

| Item | Value |
| --- | --- |
| Format | `qleisli.carrier-request` |
| Version | 1, strict |
| Profile | `finite-carrier-pure-v1` |
| Fields | `format`, `version`, `profile`, `attached`, `required` and `logical` |

Rules:

- Both interfaces retain complete ordered owner forests and public effects.
- Nominal atoms retain their original module, declaration and source
  identities and their member order, independently of logical cardinality and
  physical width.
- Singleton enums and empty records are distinct from Unit and Bits<0>.
- `Protocol.Carrier.check` reconstructs the original declarations, import
  paths and existing field Nat helpers before it checks the actual graph and
  root.
- The core freshly checks both canonical code Gram equations, the Gram
  equation of the logical map and `physical * E_in = E_out * logical`.
- Logical dimensions govern the Unitary label. A larger physical unitary does
  not justify a logical Unitary claim.
- Observation, reset and discard cannot be hidden as pure.
- Extra source rows require exact nominal origins after source checking.
  Ordinary checking keeps its own source-use rule. Uncovered helper rows and
  import-only rows refuse.
- The source, matrix and work limits apply.

> **Implementation note.** The explicit source adapter uses the
> [common judgment](source-text.md), the selected Builder and the Raw emitter.
> It requires an independent logical request and replays retained source steps
> against the checked body. Its sealed `CheckedSourceCarrier` retains that
> source graph and always reports `source_meaning_verified() == false`.
> Descriptors and source preparation grant no acceptance.

Proof scope:

- `CheckedCarrier.run_binding` binds the execution-only QLV3 packet and the
  actual QDV1 comparison of the graph, both interfaces and the logical matrix.
  The binding retains the original packet and the exact QDV1 comparison.
- Its `Binding.root_safe` follows the actual checked root to the independent
  ownership and classical-scope properties.
- The core postcondition binds the actual body/code equations and the Gram
  equations.
- The source adapter adds retained-step replay. It adds no ordinary runtime,
  no inverse or control access and no AST-preservation theorem.

Not established:

- Neither this result nor the private native carrier holder converts to an
  ordinary execution handle or grants inverse or control access.
- The closed ordinary-result runtime route is the separate mode of
  [Ordinary input/result requests](#ordinary-inputresult-requests).
- This component does not supply general nominal functions, quantum owners,
  full qmatch or original AST-to-step preservation.
- These component results admit no guarantee and do not widen the two
  existing ledger scopes.

## Ordinary input/result requests

The internal mode `--ordinary-root-check` checks the declared ordinary
parameters and result of one original declaration over its complete input
domain.

| Item | Value |
| --- | --- |
| Format | `qleisli.ordinary-root-request` |
| Version | 2 |
| Profile | `finite-ordinary-root-v2` |
| Fields | `format`, `version`, `profile`, `selection`, `module`, `declaration`, `parameters`, `input_storage`, `input_rows`, `basis`, `storage` and `public_effect` |

The field `selection` names one of three selections:

| Selection | Declaration that it denotes |
| --- | --- |
| Project | Exactly closed `main::main`, including a private ordinary main |
| Exported | An original public declaration |
| Internal | An original private non-entry declaration. Checking does not export its name. |

Rules:

- The fields are strict. Version1 requests and unknown fields or profiles
  reject without fallback.
- Original parameter and result types must be ordinary finite types. This
  mode does not support quantum ports.
- An explicit public `main` selection uses the exported rule. The project-main
  restrictions are separate.
- The basis retains the complete nominal prefix representation. Storage
  separately retains Unit, Bit, Bits, pair, tuple, enum origin and SSA
  coordinates, and record origin and ordered named children. Zero-width nodes
  cannot be discarded.
- The checker freshly reads the original ordered parameter forest and the
  declared result, and compares them with the request. Argument count and
  zero-width arguments stay explicit.
- The original Raw root, dependency, ownership, effect and scope checks run
  before complete exact instrument reconstruction.
- Lean independently enumerates the entire canonical parameter domain, first
  argument on low coordinates. It requires exact equality with the proposed
  `input_rows`.
- Lean checks typed input storage for every row. It then interprets every
  actual hidden history, including zero-probability histories, with the
  independent ordinary-value relation.
- Flattened input and output SSA maps must equal the original Raw lists.
- An invalid enum code, a changed nominal identity, a reordered field or axis,
  or a hidden Observe under a pure label refuses.
- A declared public Observe bound is retained even for a pure implementation.
- The six-bit instrument limit and the carrier and work limits apply.

Rules for source rows:

- Source rows require the actual selected original, exact checked nominal
  origins, or actual original type-resolution paths from the selected
  parameter and result types and recursive record fields.
- The ordinary and mixed runtime gates use the original body reader when
  signature and graph evidence leave source rows uncovered. This binds
  body-only type paths, including paths through called helpers, before the
  shared Raw root check.
- The shared independent resolver retains its exact query, original lookup
  bytes, visibility and import and reexport edges.
- An arbitrary row or a validated unused Nat helper cannot supply type-path
  coverage.
- Projection and both coverage scans are precharged within the work limit.
- Coverage binds source relevance to the checked artifact.

Rules for execution and transport:

- Closed simulation and sampling inspect the retained parameter forest. They
  reject a nonempty forest even when every parameter has zero width: Unit,
  Bits<0> and empty records require an actual invocation even when the Raw
  input lists are empty. A nullary typed result is closed.
- The `run_closed`/`sample_closed` APIs reject any nonclosed root. Checking
  parameters adds no unchecked arbitrary-input execution API.
- Untyped rechecking and portable export refuse until the complete typed
  artifact transport exists.
- Untrusted portable nominal emission refuses until its complete typed request
  is transported.
- Text and JSON reports distinguish this declared result and history check
  from an independent external algorithm specification.

> **Implementation note.** Nongeneric public selected functions use this gate
> through the common original-source compiler. The gate covers small quantum
> temporaries, which it checks over every hidden history. Interfaces are
> ordinary in this mode. Mixed quantum interfaces use
> [Mixed runtime root requests](#mixed-runtime-root-requests). Selection
> retains the exact original instantiation, the complete checked host bindings
> and the accepted request. Ordinary source callers use the common
> original-body lowering.

> **Implementation note.** The source wrapper discharges dormant function
> pairs through the same contract gate as project checking. It prepares the
> original Meaning and body dependencies that global obligations visit.

> **Implementation note.** The private ordinary proposal decoder of Rust
> accounts for the path and text of every proposed source under the aggregate
> identity limit. It then defers relevance to this native gate and returns no
> accepted handle. Other decoding routes keep their unused-row refusal. The
> ordinary execution view compares every retained original source byte before
> a fresh accepted handle is bound. The private accepted program retains the
> same typed request, the complete checked input rows and the graph.

Proof scope:

- `Protocol.OrdinaryRoot.check_binding` retains the original packet, the fresh
  artifact and request reads and the actual root check.
- The execution-only QDV comparison and the native dispatcher retain this
  binding through `CheckedOrdinaryRoot` and `run_typed_ordinary_binding`.

Not established:

- This mode does not check a declaration with static parameters. A selected
  root with Basis/Nat actuals uses the mode of
  [Mixed runtime root requests](#mixed-runtime-root-requests), whose emitter
  also closes ordinary Basis/Nat dependencies.
- Full qmatch and nominal finite-table consumers are separate work.
- Source-to-Raw correspondence is a separate obligation.
- No source-body, decoder, native-compiler, simulator or target preservation
  theorem follows. No external schema, inverse or control capability or
  guarantee follows.

## Mixed runtime root requests

The internal mode `--runtime-root-check` checks a root whose interface mixes
ordinary values and quantum owners.

| Item | Value |
| --- | --- |
| Format | `qleisli.runtime-root-request` |
| Version | 2, strict |
| Profile | `finite-runtime-root-v2` |
| Fields | `format`, `version`, `profile`, `selection`, `module`, `declaration`, `parameters`, `input_storage`, `input_rows`, `result`, `storage`, `public_effect`, `static_bases` and `static_naturals` |

Rules:

- Version1 requests reject.
- Full parameter and result prefixes preserve each `Q` boundary, nominal
  declaration, ordinary tuple and zero-width owner.
- Storage binds actual ordinary SSA values and ordered quantum ports.
- The original runtime signature check and the shared Raw root checks are
  independent of these producer descriptions.
- The request must name complete Basis/Nat actuals, including unused formals.
  The checker rechecks the original premises and nominal declarations before
  it instantiates the actual header tokens.
- QLV3/QDV retains these actuals even when they do not change the runtime
  graph.
- For every independently enumerated ordinary input, `RuntimeFamily`
  reconstructs all hidden maps and checks ordinary results even on
  zero-probability histories. It checks the exact input and output code-space
  equations and their complete logical Gram sum.
- Physical padding may not leak into a logical result.
- Observation stays Observe, and a Unitary label requires equal logical
  dimensions.
- The six-bit dense component limit and the work limits apply.
- QLV3/QDV compares the complete request and the actual retained graph.
- The native decision is execution-only. Inspection and caller scopes refuse.
- Original parameters prevent closed execution even at zero physical width.
- Portable export cannot erase the metadata of
  `AcceptedProgram::runtime_result`.

Rules for the choice of request:

- The compiler selects the request before native root checking. It never
  retries a failed native decision.
- The selected entry uses this mode when every selection has its own
  whole-circuit check and the original operation closure does not require
  version 5.
- Nominal source gates, wider selection sectors and original operation closure
  transport use the bounded request of
  [Version 5: source-body requests](#version-5-source-body-requests). That
  section also specifies the checks of coherent basis lifts, `with_computed`,
  access receipts, `qfor` and Meaning applications.
- A small nominal named-arm qmatch function also submits its complete actual
  callee fragment to the version-4 mode of
  [Qmatch source requests](#named-arm-qmatch-component-requests), before
  whole-root runtime acceptance.

> **Implementation note.** `Kernel::check_runtime_root` and fresh
> `check_program` rechecking bind the same objects to the native decision.
> `AcceptedProgram::runtime_result` exposes read-only metadata. The common
> project and selected emitter uses this gate for mixed runtime interfaces. It
> retains actual input storage before call expansion, and complete output
> types and owners afterward.

> **Implementation note.** Selected roots with Basis/Nat actuals use the same
> emitter and gate, including unused nominal actuals and closed observing
> bodies. Their complete original source judgment is repeated, and actual
> trees are rebound to its original interface. Ordinary Basis/Nat dependencies
> use the same original call plans and bounded closure. Concrete nominal
> arguments use the `type(T)` form. Forwarded formals retain their original
> binder identities. Nominal fields keep their declaration scope. Complete
> closed siblings are checked even when a different actual is unresolved.
> Unused nominal actuals also require typed checking when the global dormant
> pass materializes a closed dependency.

> **Implementation note.** Selected built-in qmatch and its ordinary callers
> also use this emitter. Named operation arms require their original provider
> bodies to pass the finite evidence gates. The actual emitted circuit also
> passes the separate six-bit encoded equation.

Proof scope:

- `RuntimeRoot.check_binding`, `CheckedRuntimeRoot.run_binding` and
  `NativeContext.run_typed_runtime_binding` connect actual reads and
  comparisons.
- The root safety theorem reuses the original Raw gate without enlarging
  either human-admitted guarantee.

Not established:

- This mode does not enable operation-formal closure. The version-5 request
  transports the original operation closure.
- This mode checks a coherent selection only through its whole-circuit check.
  The version-5 request checks wider selection sectors within its bounds.
- Exact computation witnesses are separate from complex denotation,
  source-body preservation and numerical runtime correspondence.
- Independent host-expression visibility and source/body preservation are
  separate obligations.
- No external schema, inverse or control capability, guarantee admission or
  broader QS/PR/RS/EXACT discharge follows from this mode.

<a id="named-arm-qmatch-component-requests"></a>

## Qmatch source requests

Two modes read a `qleisli.qmatch-request`. Each accepts one version of the
request:

| Version | Mode | Profile | Subject |
| --- | --- | --- | --- |
| 4 | `--qmatch-source-check` | `finite-source-qmatch-context-v4` | The named-arm component: [Version 4](#version-4-named-arm-component-requests) |
| 5 | `--qmatch-source-v5-check` | One of four profiles | The original source body: [Version 5](#version-5-source-body-requests) |

The **full qmatch profile** is the twelve-joined-bit, 64-label source contract
of `qmatch`. Neither version validates the full qmatch profile.

The production compile path dispatches both versions, and a successful reply
of either mode has the claim `accepted`. A version-4 success binds the private
component `QmatchChecked`. A version-5 success binds an accepted program.

### Version 4: named-arm component requests

The internal mode `--qmatch-source-check` checks the **named-arm component**:
the `qmatch` selections with named arms in one complete structural quantum
function, together with every literal Raw interval of that function.

| Item | Value |
| --- | --- |
| Format | `qleisli.qmatch-request` |
| Version | 4 |
| Profile | `finite-source-qmatch-context-v4` |
| Scope | Execution only |
| Fields and QDV record | [The request and QDV schema](execution-view.md#internal-named-arm-qmatch-component) specifies them. |

Rules:

- The request and the QDV record bind the complete typed interfaces of every
  site, its original source byte occurrence, its literal Raw interval and its
  actual evidence and control indices to one fresh graph.
- Every original selection appears in order. The intervals exhaust the
  complete call without gaps or overlaps. Each interval retains its actual
  owner frame and passes its own exact equations.
- Original source reads determine the canonical labels, types, owners, public
  effects and source rows. Actual receipt inputs and dependency snapshots bind
  the named arm bodies.
- The pure finite/Raw/QIRF/nominal gates check exact main/U/CU sector
  equations.
- The request binds the selected pair separately, in selector/target order. It
  retains additional arguments, zero-width owners and the outer public effect.
- Nominal enum and record targets, including empty records, retain their full
  original types with enum or built-in ordinal selectors. Their physical arm
  entries and controls are untrusted proposals. The mode binds the full target
  type, the actual body and the code equations. It issues no provider
  capability.
- The ordinary source-root wrapper keeps its original main-only roots and its
  empty extra source-query extension.
- The check spends from the
  [shared exact-work ceiling](#shared-exact-work-ceiling).

Rules for the ordered Raw frame:

- The frame requires a complete structural source return. Checked renaming,
  ordinary tuple moves and the final expression retain the original logical
  owner identities, basis trees and returned order.
- Unknown suffix expressions, hidden observation or discard, and missing or
  duplicated owners refuse.
- A legal source return that changes owner order requires a matching Raw
  output mapping. Equal types or empty wire lists do not justify reusing the
  unswapped Raw subject.
- The original Raw operations transport an independently derived logical
  owner tree. Explicit joins retain ordered children. Splits recover those
  children. Owner-moving operations retain their complete source roles.
- The actual output-token order must match the original source return.
  Reversing two empty Raw ports cannot pass for a canonical source return. A
  matching source/Raw zero-width permutation is accepted.
- Physical widths constrain a split without identifying a logical owner. A
  producer supplies no role table and no cached tree.

> **Implementation note.** `Kernel::check_qmatch_source` invokes the mode. The
> Rust walker describes the actual retained graph and the circuit and matrix
> caches. The same allocations enter `QmatchChecked` only after exact QDV
> matching and native product, edition, mode, scope and request matching.

> **Implementation note.** A small nominal named-arm qmatch function submits
> its complete actual callee fragment to this mode before whole-root runtime
> acceptance. The fragment retains its original complete quantum argument and
> result order, its structural body and its named-arm evidence. Suspended
> caller owners stay in the complete outer Raw state. The bounded source
> adapter retains the actual complete call and restores the frame of the
> suspended caller. It does not synthesize a replacement source function or
> expose a raw conversion of `QmatchChecked`. The component uses an internal
> canonical owner frame. That frame is not a language restriction.

> **Implementation note.** Shared conformance cases cover three- and
> four-label nominal selectors on two physical bits with a distinct zero-width
> Unit target, reordered written arms and exact relative phases. The
> three-state code leaves its padding label outside the logical interface.
> Literal retained-view expectations include the four dyadic coordinates of an
> eighth-root phase. Phase, control-polarity and evidence faults must reach
> the equation gate. Original nominal, arm and owner substitutions reach the
> request gate, and stale compared output reaches QDV refusal.

Proof scope:

- The structural execution proof recovers the historical snapshot of each
  entry from the same successful graph run. It preserves every dependency that
  the entry references in the final root. It transports the original IR
  execution with identical exact operators, hidden histories, failures and
  unspent work. It covers references in both branches even when the condition
  is constant. Unrelated slots may differ. The common context result retains
  this execution property in its ordered original arm-binding relation. The
  proof does not prove the meaning or the lowering of the original source
  body.
- The original-arm continuation is not wired into source or transport
  admission. It reuses the actual checked signature and body through the
  common source traversal. It then checks the IR of the realized entry under
  those same final dependencies. Supported bodies inherit the explicit scope
  of the common reader. Selections require their recursive arm equations. The
  continuation enables no native request, handle or broader source
  preservation claim.
- Generic success bindings retain the original Raw ownership and
  classical-scope properties without enlarging either human-admitted
  guarantee.

Not established:

- No public conversion yields an ordinary `AcceptedProgram`, an inverse
  capability or a controlled capability.
- Data constructors, request encoding and source headers alone supply no
  source-function theorem.
- The component checks alone supply neither ordinary source execution nor the
  full qmatch profile. The bounded compiler adapter also requires separate
  whole-root runtime acceptance.
- General source expressions and call frames, other valid mappings,
  constructed, static and generic arms, and the full qmatch profile are
  pending.
- The structural-return check does not establish general source/arm lowering
  or expose ordinary source execution.
- Splitting an opaque source owner, allocation and release, and a changed
  representation each need their own checked source rule or refinement. The
  structural component does not establish every valid Raw mapping or complete
  source preservation.
- Fresh native conformance, canonical proof maintenance and full CI are
  required. Original source-body lowering, decoder, walker and native
  compilation, runtime and target preservation, and broader QS/PR/RS/EXACT
  duties are separate.

### Version 5: source-body requests

The mode `--qmatch-source-v5-check` checks the **source body** of one original
invocation: its coherent selections, basis lifts, computed intervals, access
calls and Meaning applications, each against its literal Raw interval. The
request also carries the runtime-root request of the same root.

`Kernel::check_qmatch_source_v5` submits the request that the compiler
selects. The accepted program records the checked profile, which
[CLI success reports](#cli-success-reports) names.

| Item | Value |
| --- | --- |
| Format | `qleisli.qmatch-request` |
| Version | 5 |
| Profile | One of the four profiles below |
| Scope | Execution only |

| Profile | Body that earns it |
| --- | --- |
| `finite-source-qmatch-context-v5` | A body with checked selections |
| `finite-source-meaning-context-v5` | A standalone Meaning application. The native traversal binds an actual application interval and discharges the original Meaning duties of the selected invocation. Other roots retain their pending positions for separate checks. |
| `finite-source-basis-context-v5` | A body with no selection or Meaning context and with an actual checked basis lift or computed interval. The check discharges the original duties of the selected invocation and retains pending positions that belong to other invocations. |
| `finite-source-access-context-v5` | A standalone original access body. The native replay finds an access receipt in the actual checked steps of the selected invocation, its named calls or its branches. |

Rules:

- The checker checks the original nominal declarations and import paths that
  constructors and field projections use in the body, even when the types do
  not occur in the selected interface.
- The check spends from the
  [shared exact-work ceiling](#shared-exact-work-ceiling).

Rules for coherent basis lifts:

- Selected bodies and project bodies may include coherent basis lifts with
  nominal values.
- The native checker independently derives the logical table from the original
  finite expression and the pure helper bodies. It checks the dependencies of
  every ordinary match arm, and binds the canonical rows to the actual Raw
  lift interval.

Rules for `with_computed`:

- This mode also checks a protected two-argument `with_computed` with an
  original nominal predicate. Lean evaluates the total classical predicate on the
  exact logical codes and requires zero in the padding rows. It checks the
  original one-Bit use body against both exact diagonal entries of the literal
  Raw use. The same interval retains the original data owner and its
  spectators.
- Selected runtime functions and projects that use this mode support circuit
  synthesis for first-order Boolean predicates on built-in basis inputs. Lean
  checks the ordered controls and both compute passes against the original
  predicate. It then checks the protected use on both auxiliary values. This
  path checks the predicate and both circuits in their structural
  representation.
- The synthesis path charges work for the source expression, intermediate
  clause products, literal circuit fields and owner-frame checks. The charge
  includes intermediate conjunction products, even when the final circuit is
  smaller. The path uses one private scratch bit and the work and interface
  limits.
- For example, a two-bit increment modulo four can use the checked carry
  predicate `word[0] and word[1]` as a controlled phase between Hadamards on
  the high bit, followed by a low-bit flip.
- The literal `take_bit` and `put_bit` intervals retain the original register
  coordinates and arbitrary reference amplitudes.
- A finite transform such as a specialized adjoint, control or power selects
  the checked finite representation when it prepares its original body.
- The three-argument certified form binds the original use body and the
  logical supplier independently to their literal circuits, on the exact data
  and auxiliary codes.
- Explicit pair splits and joins retain their written owner order and the
  exact logical axes, including padding in the product code.
- The native cleanup equation covers the complete physical domain.

Rules for access receipts:

- An access receipt binds the written arguments and their roles to the actual
  callee, the ordered quantum ports, the returns and the Raw interval.
- Ordinary `Unit` arguments keep their original positions in the call.
- A routed exclusive named call also checks its original `Bit` arguments, its
  ordinary branch, its parked owners and the complete extraction and
  reinsertion.
- The checker verifies complete coverage of the selected invocation. It
  retains the pending positions of the other invocations.
- The separate provider proof of a transform does not supply this receipt.
- The access profile is part of the compared QDV1 execution view.

Rules for inline arms and `qfor`:

- For `qif` and `qmatch`, a written inline arm submits its original arm index,
  its source positions and its literal Raw body. Lean replays the original
  block in the isolated target frame. It compares the resulting exact action
  with the controlled implementation and with the Raw sector of the caller.
  Mixed named and inline arms use that same sector check.
- For a supported original `qfor` with closed bounds, Lean follows the written
  iteration order. It checks that the literal Raw intervals cover the loop
  body contiguously. It checks the carried register and the surviving owner
  frames at the boundaries, including zero-width owners.

Rules for Meaning applications:

- A selected coherent arm can use an original classical Meaning helper with
  nominal intermediate values when the ports of the Meaning are supported
  built-in types. Lean checks the helper against the original canonical inputs
  and compares the exact Meaning with the applied arm. Standalone applications
  can use the same equation check.
- Standalone applications also check endomorphic `permutation_by` and
  `phase_by` Meanings with finite nominal ports through the same native path.
  Lean checks the original provider body, the exact logical action on its
  canonical codes and the literal application.
- A composed Meaning can pass through a nominal intermediate type. Tensor
  Meanings retain the ordered logical axes of their nominal and built-in
  components.
- A reused Meaning evaluation requires the same original declarations,
  reference occurrences, exact ports, ordered graph edges and dependency rows
  in both source queries.
- A rectangular application through a named call retains the written
  `checked_op` at its supplying argument, even when the callee leaves the
  argument unused. A rectangular application checks the distinct input and
  output codes against the actual Raw interval and preserves the spectator
  frame.
- A Meaning declared on an operation formal checks the exact supplied
  argument, including unused actuals. The original header duty and any
  `checked_op` written at the call site each retain their own source
  occurrence.

Rules for operation arguments and Meaning duties:

- The internal common-body duty continuation authenticates every original
  operation argument in scalar-free Op calls, including unused siblings,
  against the complete ordered header keys. A forwarded formal retains its
  original mixed-header ordinal.
- The supplying assertion and the enclosing arm retain separate original
  queue positions, source tokens, provider occurrences and exact Meaning
  equations under the same final native root.
- An authenticated interior formal path may locate a supplying assertion
  inside a constructed argument. The continuation requires exactly one
  original requested node with fully bound children. It checks every other
  local provider and ordered descendant.
- Unknown providers, further missing requests and ambiguous supplying
  occurrences are residual.
- The complete original call and the mixed-header keys of the supplying root
  are checked again. An enclosing equation cannot replace the inner equation.

> **Implementation note.** For a basis lift, the producer evaluates only the
> original logical rows and completes unused physical inputs injectively. For
> predicate synthesis, the compiler emits controlled XOR steps from constants,
> input bits, literal `Bits<n>` coordinates, Boolean operations, tuple
> bindings and supported helper calls.

> **Implementation note.** The retained two-qubit general-composition
> development regression has an explicit preparation-work exception, which
> [History](#history) cites. The regression runs nonaccepting source
> preparation and the unchanged normal-budget whole-body action separately. It
> reports aggregate work and independently checks all sixteen exact I4
> entries. It issues no handle and is not one bounded production acceptance.
> The public 20,000,000 ceiling and its entry guard are unchanged.

#### Proof scope of version 5

The theorems below concern a successful version-5 check and the original body
that it reads. Their namespaces begin with `Runtime`, or are `RawFiniteRows`,
and are defined in `lean/Qleisli/`.

Several theorems concern three adjacent original named calls: the **pre**
call, the **middle** call, which holds the selection, and the **post** call.
The proofs name the middle call "choose". A **three-call root** is an original
root whose Raw events are the slices of these three calls and one final
reorder.

Coherent selection:

- `RuntimeSelectionAction.caller_action` covers a Bit selector and a Bit
  target. It relates the literal Raw events to both indexed logical arm
  matrices on the complete returned owner code. It covers a single `quantumIf`
  and the compiler's `join`, `apply_unitary`, `split` sequence. The original
  logical selector and target determine which matrix and row act, including
  when the selected wires are reversed or separated by spectators.
- `RuntimeSelectionGram.logical_gram` proves inner-product preservation for
  arbitrary joint caller and reference amplitudes under the same two arm
  receipts.
- `RuntimeSelectionGram.checked_selection` obtains both receipts and the
  canonical order `[0, 1]` from the source layout reads and from the logical
  matrix comparison that the native selection node retains.
- `RuntimeMultiwayAction.checked_selection` covers any checked finite selector
  with a Bit target, under the same literal interval and owner-code premises.
  Each encoded selector label determines one original arm. On valid encoded
  inputs, the physical output agrees with that arm at every output row,
  including zero amplitude on padding labels. The same arm receipts preserve
  the logical inner product with an arbitrary external reference.

Predicate synthesis:

- Lean proves the exact work that the predicate compiler debits and that both
  circuit comparisons debit.

The three-call root and the source flow:

- `RuntimeNamedThreeRoot.Whole.instrument_decomposition` factors the
  independent instrument meaning of the original root into the three actual
  event slices and its final output permutation. It retains complete
  intermediate history families, including hidden and zero-weight outcomes,
  without normalization or reassociation of the bounded evaluator.
- `RuntimeNamedCodeTransport` proves that the checked original child-to-caller
  return map preserves complete basis trees, ports, the independent
  sparse-code interpretation and ordered axes in the same caller frame.
- These two results are return-transport and Raw-instrument laws. They do not
  compose the different source-level encodings and logical actions.
- `RuntimeNamedSourceFlow.original_body` derives the named-boundary state
  chain from the actual common body loop and its retained successful
  traversal. It retains the real initial owner reorder and the final
  source-return read. The proof follows both fresh and planned event
  traversal, including selected static continuations, with the original
  continuous work counter. It factors the recursive iteration without
  changing its guards, reads or charges.
- `original_three` connects the actual pre, middle and post calls through
  their complete source states, including ordered bindings, full bases, ports
  and issuance history. Equal physical widths and assumed code equations are
  not premises.
- The state-flow invariant is administrative. Other step kinds receive no
  named-boundary assertion from it. It establishes no whole-source code,
  logical-action or observing-history composition.
- `RuntimeNamedChildRuns.original_body` strengthens the same loop proof with
  the actual recursive run of every named child on its original callee and
  native block. The retained input read binds the original parameter owners of
  the callee to the selected ports and original input owners of the caller.
  The recursive call uses the same checked visible ordinary SSA. It starts
  with the work that the input read leaves. Its exact result determines the
  stored child steps, the returned history and the ordinary state.
- The same stored step list carries an `OrdinaryRun` from the actual initial
  SSA state to the actual returned SSA state. It retains the tables and
  measurement keys across gaps, observations, named calls and conditionals,
  with pure steps preserving both. Its literal partition covers the complete
  original Raw operation list in order.
- `RuntimeLiteralBody.original_body_trace` reads each exact interval through
  the independent observing reader. Adjacent steps share the full Raw boundary
  state, and their events concatenate to the trace of the original body.
- `RuntimeLiteralBody.original_body_execution` splits a successful independent
  run at those exact boundaries. Each step runs on every incoming history and
  keeps the result order of the interpreter. The execution induction follows
  the same source-owner and SSA chains. A proved local invariant therefore
  applies to every returned history of the original body.
- The weaker state-flow law is derived from this single strengthened proof.
  `original_child_runs` supplies those computations for the actual pre, middle
  and post view. Other step constructors receive no child-provenance assertion
  here. The proof establishes no whole-source code or action composition and
  no observing-history composition.

The pre and post calls:

- The state-flow proof aligns actual primitive nodes with both their complete
  source input history and their checked output history. Its primitive
  handler, operation and selection case proofs share the existing loop. Other
  step constructors acquire no state or code assertion.
- `RuntimeNamedPrimitiveInputs.original_pre_post_inputs` derives the original
  pre and post primitive input carriers from the actual callee recursion and
  argument construction. The real parameter reorder preserves the same
  assigned map. Complete basis trees and ordered ports, not equal widths,
  determine the retained input-code read of the primitive.
- `RuntimeNamedInputAction.original_input_action` substitutes the complete
  authentic caller encoding into the same original parent Raw-event
  source-action law. The original child input proof and the checked selected
  ports derive its carrier and axis equalities. The independent sparse forest
  coefficients construct an arbitrary correlated spectator and reference
  fibre. No factorization of the joint state, supplied encoding equation or
  dense caller reconstruction is assumed. Native singleton code equality
  follows from the actual primitive reader. The equation retains the real
  final local reorder and the output code.
- `original_pre_post_input_actions` applies these input laws to the pre and
  post event lists of the same original root, under the literal coverage and
  slice start and length premises. It does not infer those premises from
  matching widths.
- The input-action laws do not transport the output fibre to the complete
  caller output encoding or source order. They do not compose the logical
  action or the observing history of the whole function. They are mathematical
  laws, not an additional native acceptance gate, a bounded availability claim
  or a guarantee admission. They change no executable kernel or Rust rule,
  effect label, work limit or public capability.
- `RuntimeNamedPrimitiveOutputs.original_pre_post_outputs` derives the native
  output carriers through each real callee run, its original return reorder
  and the actual caller owner mapping. It retains complete basis trees and
  ports.
- `actual_occurrence_output_code` attaches that same native code computation
  to the returned caller binding in its complete checked frame.
- The interval-state identity lemmas compare successful reads of the same
  original block, start and count. Their derived empty checkpoints are erased
  proofs. They are not fabricated runtime receipts or extra work for the
  nonempty interval.
- `RuntimeNamedOutputEncoding.complete_output_encoding` factors the complete
  caller output encoding through that native code. It retains arbitrary
  correlated spectator and reference coefficients.
- Its `original_pre_post_output_encodings` consumer derives the target, the
  retained owner code and the native code read from each actual original call
  and its complete output frame. None is an assumed encoding equation.
- `RuntimeNamedOutputOrder` transports dense logical coefficients by the exact
  cardinalities of the original owners, including padding and dimension-one
  owners. Its separate code identity requires equality of full ordered
  source-owner and wire pairs and the actual Raw frame. Code equality does not
  establish those source premises.
- `RuntimeNamedHeadCoefficients` identifies the actual source input fibre and
  updates its exact logical coefficients with the true input and output
  cardinalities.
- `RuntimeNamedCallerGeometry` derives the returned basis, the wires, the full
  Raw frame and the unchanged spectator bindings from the actual callee and
  caller boundary.
- `RuntimeNamedCallerAction.actual_whole_caller_action` combines those facts
  with the same native output-code read. It proves the exact action on the
  complete returned caller encoding, for arbitrary correlated logical and
  reference states. It removes the final self-reorder only on actual finite
  physical rows. No unbounded identity of that event is assumed.
- `original_pre_post_actions` instantiates both laws with the real child
  executions and exactly the event lists that the original root decomposition
  retains. The supplied complete checked frames are explicit premises. The
  theorem does not prove their construction for every source body.

The middle call:

- `RuntimeNamedSelectionInputs.original_middle_source` derives the complete
  original input carriers of the middle selection from the real argument
  construction and child run. The strengthened common-loop invariant retains
  its exact before binding map and full returned source state. The actual
  final written return, including its reorder, starts at that selection
  after-map. All nominal trees, ports, spectators and separate zero-width
  owners stay in those maps. The theorem supplies source-state provenance. It
  supplies no caller coefficient or action equation and no proof of arbitrary
  intermediate frame availability.
- `RuntimeNamedSelectionFrames.original_middle_frames` derives both
  mathematical child Frames from the complete caller input Frame. It selects
  the actual ordered argument owners and transports their existing receipts by
  full port and basis equality. It uses the original owner flow of the same
  selection for its after Frame. No final child Frame, successful `readFrame`
  invocation or bound on unspent work is supplied or fabricated.
- `RuntimeNamedBlockEncoding` partitions the actual complete caller code into
  its original selected owners and retained spectators. It derives
  selected-token uniqueness from the real call input gate, including
  empty-wire owners, and does not infer it from physical axes. Exact owner
  cardinalities reindex the arbitrary joint and reference coefficients. No
  separability premise is introduced.
- `RuntimeNamedCarrierEncoding` connects the actual input code of the retained
  child to those selected coefficients, by full ordered port and basis
  equality and the real Raw frame.
- `RuntimeNamedBlockSpectators` derives disjoint axes from the complete valid
  caller. It proves that scattering selected axes leaves every spectator
  coefficient unchanged.
- `RuntimeNamedSelectionInputEncoding.actual_occurrence_source_action`
  combines those facts with the same original child run, indexed Literal,
  coverage and parent-event source law. The source carrier equality is derived
  from that run, not supplied by a caller.
- Its `original_three_input_actions` consumer retains all three complete-input
  action laws on the same original root event lists.
- The selection output proof uses the actual return permutation of the child
  and the original mapping to caller owners. It transports the corresponding
  sparse coefficients through the exact output axes and applies each source
  arm on every spectator coordinate of the joint input. This yields the
  complete caller output in its original owner order, with all reference
  correlations.

Composition of the three calls and observation:

- `RuntimeNamedThreeFrameChain.original_three_composed` takes its first frame
  from the original input storage and entry read. At both joins the same
  native state and source owner map carry the preceding output into the next
  call.
- `RuntimeNamedThreePackedOutput.original_three_packed` also identifies the
  actual final Raw reorder and the owner reindex of the original return. Its
  finite-row equation includes the complete packed output for every joint
  logical input and reference coordinate.
- `RuntimeNamedThreePackedInstrument.original_three_observing` connects that
  equation to the same independently read observing event list.
- `RuntimeObservingPrefix.checkOps_reference` derives the same quantum
  interface in the independent reader after each successfully checked prefix,
  including erasure, reset and both sides of classical branches.
- `root_interval_histories` uses that agreement to locate an adjacent pure
  interval in the original observing root. The interpreter preserves every
  inherited history. It applies the pure action to each operator before it
  continues with the original suffix and final reorder.
- `original_adjacent_observing` locates the three original calls in a longer
  source traversal and retains the selection at its actual global rank. The
  same Raw events drive both the source-action equation and every inherited
  operator column that the checked input frame represents. The law requires
  that input representation, the supported call shapes and exact adjacency of
  their Raw slices. The packed root law uses explicit whole-slice coverage.
  The original-body theorem below uses the complete checked traversal. The
  law changes neither native acceptance nor the work limits.
- `RuntimeOriginalObservation.original_observation_histories` covers a checked
  original `measure_z` or `discard`. It identifies the actual Raw erasure
  event and every emitted outcome. Each unnormalized operator on the surviving
  owner code is the basis effect of the original consumed owner on that
  outcome, with the same arbitrary reference coordinates. The theorem retains
  all hidden outcomes and the original visible measurement identifier. It
  requires the input code representation on finite Raw rows.
- `RuntimeNamedObservationEntry.original_supplies_histories` transports every
  outcome into the entry frame of an immediately following original named
  call, through the exact source-state and Raw interval joins.
- `RawFiniteRows.checked_slice` retains the finite input and output widths of
  the original checked event slices. Their action on each inherited history
  depends only on its finite input coefficients.
- `RuntimeNamedObservationEntry.original_erasure_then_adjacent` ties the exact
  prefix, erasure, three-call interval and continuation to one original
  observing IR program. For each erasure outcome, the same three-call source
  equation acts on the unnormalized projected state in the checked post-call
  frame. It keeps the visible measurement and hidden outcome through all three
  calls. The equation applies to every finite post-call row and reference
  column of a represented incoming history.
- When the post call ends both the original source traversal and the Raw
  operations, the actual suffix is the final permutation. The same theorem
  gives the packed source result in the original return order for every
  outcome. It identifies the list of histories that the original interpreter
  returns.

Branches and ordinary values:

- `RuntimeNamedChildRuns.original_body` retains the actual input and output
  owner states for classical gaps and conditionals. For each conditional it
  keeps both original recursive arm reads and the successful join on their
  returned owner states and ordinary SSA tables, with the original work
  counters.
- `RuntimeOriginalBranch.original_branch_events` identifies the exact Raw
  branch event, both arm traces and their final permutations. On a history
  whose ordinary values agree with the checked source expressions,
  `original_branch_step` selects the arm by the source condition.
- `RuntimeOriginalClassicalJoin.original_branch_classical_join` uses the
  original Raw freshness check for every classical phi destination. Suppose
  that the selected arm returns histories with their checked SSA agreement and
  issued identities. The literal merge then produces one corresponding history
  per arm result, in order. Its visible values agree with the checked
  post-branch source expressions. Its quantum operator and hidden outcomes are
  those of that arm result.
- `RuntimeOriginalQuantumPhi.original_quantum_phi_action` ties the actual
  arm-final Raw permutation to the complete original owner pairing. It retains
  the exact carrier layout of each owner, including separate zero-width
  owners, and derives the source output frame in its checked owner order. The
  equation holds for every finite output row and reference column. A
  represented arm history keeps its ordinary values and hidden outcomes
  through that exact permutation.
- `RuntimeOriginalBranchJoin.original_branch_join` composes the source
  condition, the original arm run, its quantum return permutation and the
  literal classical merge. The original parent step returns one checked
  quantum and ordinary history for each actual arm-body result, in order.
- `RuntimeObservingValueRetention.run_values` proves that each successful
  literal history retains all incoming values and only adds IDs from its
  trace.
- `RuntimeObservingPrefix.checkOps_reference_with_writes` relates those
  writes, including recursive arm writes and phi destinations, to the issued
  IDs of the original check. The branch theorem derives this correspondence
  for every arm result from the support of the incoming history at the checked
  boundary.
- `checked_program_values` obtains the same support for a complete original
  run from its own input bindings and native verification.
- `RuntimeOriginalOrdinaryGap.original_gap` interprets the exact original
  classical interval with its checked SSA table. Each output is fresh in the
  actual Raw state. The independent run returns one history whose values agree
  with the resulting table. The history retains its operator and hidden
  outcomes.
- `RuntimeOriginalObservationValues.observation_agreement` binds each actual
  measurement bit to the source measurement key that its checked call path
  transports. The valuation preserves every earlier successful expression,
  including the selected arm of a `choose` expression. Discard preserves the
  ordinary table. Both instructions preserve issued-ID support for the resulting
  history.
- `original_gap_values` derives agreement in the valuation of the returned
  history itself. `observation_step_values` gives the same agreement for every
  history of the actual erasure event.

The complete original body:

- `RuntimeLiteralBody.original_body_recursive_refinement` composes these laws
  for the complete staged original-body traversal. At each step the source
  operator follows the original primitive meaning, graph receipt, written
  transform or selection table. A written transform uses the exact logical
  matrix read from its checked forward body and the source-specified power,
  adjoint or control. Its ordered return replaces the selected owners and
  preserves the spectator bindings, including zero-width owners.
- The same recursion follows actual named child reads and the arm that the
  checked ordinary condition selects. It applies the written return order to
  every result and relates the complete history lists in order. The statement
  starts with a successful checked body and a finite representation of the
  input operator. It retains the visible SSA agreement and hidden outcomes for
  each returned history. Validation of the full qmatch profile and release
  validation are separate from this theorem.
- `original_body_graph_refinement` derives coherent selection coefficients
  from the original named arm graphs and checked inline bodies. For a mixed
  selection, each nominal selector ordinal is paired with its written arm in
  the actual checked table. An inline arm uses its own original source
  evaluation at a smaller runner depth, including its input encoding and
  literal Raw return order. The resulting coefficients give the same action as
  the corresponding sectors of the Raw program of the caller. The full result
  follows the source prefix and selected path, including named calls and
  ordinary branches.
- `native_qmatch_body_graph_refinement` connects this theorem to successful
  `Protocol.NativeContext.run .qmatchSourceV5` on the original packet. The
  same decision supplies the body and the compared execution view. The result
  preserves the complete ordered history family with `List.Forall₂`, the
  literal return order, visible SSA values and hidden outcomes.
- `native_qmatch_input_rows` supplies the original row for every canonical
  ordinary input assignment.
- The initial source/Raw encoding relation and successful independent
  mathematical execution are explicit premises of these theorems.

#### Not established by version 5

- Validation of the full qmatch profile is open.
- Release validation is separate.
- Nonstructural `qfor` bodies are pending.
- The duty checks do not close all general nested duties or establish
  source-action composition.
- Caller-frame construction and availability for arbitrary source bodies are
  separate obligations.
- The theorems do not prove native compilation, IO, Rust simulation or target
  preservation. They admit no guarantee.
- Independent host-expression visibility and source/body preservation are
  separate obligations.
- No external schema, inverse or control capability, guarantee admission or
  broader QS/PR/RS/EXACT discharge follows from this mode.

## Root loading and compatibility during generic migration

This section states which sources a load checks, what provenance a receipt
retains, and which compatibility duties a migration to generic rules keeps.

Rules for loading:

- `frontend::project::Project` loads every `.qli` module beneath its selected
  source root and all bundled ordinary sources.
- Ordinary project compilation checks every materialized concrete ordinary
  function root, including unused functions.
- Classical bodies and Meaning declarations have their separate preparation
  and checking obligations.
- Common source checking covers every declaration, including unused
  declarations and both branch bodies.
- `QrateSource` in `src/frontend/project/manifest.rs` provides opt-in
  selection of an explicitly declared `[source].root`. That selection chooses
  the source tree. It does not introduce reachable-only loading or exempt
  unused siblings inside the tree.
- Explicit module-map `ParsedProgram::parse` checks every supplied module and
  the bundled registry before it selects a concrete entry.

Rules for the provenance of receipts:

- Ordinary finite-frontend function and instrument receipts and local equation
  sidecars retain source provenance separately from the loading policy.
- Each retained declaration contributes its original resolved lexical
  dependencies, including type and Nat expressions, Meaning references,
  inactive branches and zero-count operations.
- Actual bound Op descriptors and checked Raw receipt dependencies contribute
  their original source records as well.
- Pure providers retain their original declaration and equation association.
  Instrument calls also retain the original caller and its concrete Op
  bindings for source-span binding.
- The resulting closure retains complete original module text, including
  comments, and shares immutable module records across receipts. Unrelated
  loaded modules need not appear in each receipt.
- The metadata limits and the aggregate native transport limits apply.
- This selection changes neither loading nor eager checking of every loaded
  declaration. It does not implement a reachable-module policy.
- These records provide provenance. They are not a source-preservation proof
  or acceptance authority.

Rules for a reachable-module policy, which this chapter does not enable:

- Such a policy must specify entry roots, transitive imports, providers and
  Meaning dependencies, independent checking of the selected graph,
  bundled-library validation and the treatment of unused sources.
- It must retain original module, root and dependency identities and reject
  stale, missing or replaced references.
- It must preserve the permitted import-only cycles. Imports have no runtime
  action.
- Forbidden call, Meaning and provider dependency cycles retain the rules of
  their actual profiles, including any explicitly admitted decreasing
  recursion.
- Diagnostics and source-selection migration need review before a change of
  the all-source behavior.

Rules for compatibility:

- The
  [five-role architecture](primitive-boundary.md#generic-acceptance-and-library-owned-algorithms)
  assigns compatibility duties for flat Raw IR, both QIRF profiles, finite
  contracts, five hierarchy modes, component protocols, source/qrate and
  module-map entrypoints, Rust/Python clients, foreign adapters and research
  comparisons.
- The five hierarchy modes are `--hierarchy-pending`,
  `--hierarchy-request-pending`, `--hierarchy-fourier-pending`,
  `--instrument-pending` and `--qpe-instrument-pending`. The architecture
  records no compatibility duty for the sixth, `--hierarchy-control-pending`.
- A later migration must preserve each supported contract, or state its
  explicit versioned replacement, its unsupported cases and its migration
  tests.
- Replaced wrappers and their proofs must stay built and audited until their
  supported callers and obligations migrate.
- Missing or incompatible native checking must reject through every route.
- Retired APIs are not compatibility promises to resurrect. `frontend::sized`
  moved to `frontend::compile`, and the `qleisli sized` command prefix was
  removed with explicit migration diagnostics.
- The separate research and Python comparison readers do not restore that
  production namespace or supply alternative source acceptance.
- Edition 2026 identifies the constitutional regime. Source, API and protocol
  compatibility is versioned separately.

## Status and limits

### Publication and proof are separate

- Implementation unification, publication, proof compilation, tests and
  audits are distinct evidence.
- All of S05-C1–C5 are open. Full supported-profile Soundness is targeted at
  version 0.5.0.
- Neither this inventory nor an existing helper theorem automatically
  discharges a guarantee in the constitutional ledger.
- Two scoped guarantees are admitted: `QS-QLV1-OWNERSHIP-2026-01` for
  ownership and `QS-QLV1-SCOPE-2026-01` for classical scope. Both concern the
  original decoded ordinary root. The broader obligations of the
  interpretations QS-2026-01, PR-2026-01, RS-2026-01 and EXACT-2026-01 are
  pending. No theorem that this chapter cites admits another guarantee.
- Edition 2026 identifies the constitutional regime, independently of release
  and syntax compatibility.
- The native executable, its transport, its decoder and the execution
  correspondence are explicit assumptions. Having Lean source does not prove
  compilation or the entire pipeline correct.

### Shared exact-work ceiling

- Ordinary and source-`qmatch` checks share a public ceiling of 20,000,000
  exact-work units per request. The limit is inclusive.
- Decoding, source and graph checks, and execution-view comparison spend from
  the same counter.
- Rust also charges native receipts against the unspent exact work of the
  compilation, across all sites and calls.

### CLI success reports

Without an explicit `--entry`, `qleisli check <source-root>` and
`qleisli check <directory> --qrate` use the
[project route](diagnostics.md#routes). They check the source project and its
concrete lowered roots.

- A successful request-free native decision establishes the applicable IR
  structure, ownership, interface and classical-scope checks. It does not
  establish an independently requested algorithm, the full meaning of the
  source, or preservation from source to IR.
- The text success report names this scope and the actual canonical checker
  paths. It states whether independent requests were checked, and it states
  that source preservation is not proved.
- The JSON report is the version-1
  [result envelope](diagnostics.md#the-result-envelope) with `outcome: "ok"`.
  Its `diagnostics` array holds only warnings and may be empty.

The `result` of a whole-project source check has these fields:

| Field | Meaning |
| --- | --- |
| `checker_paths` | Distinct canonical executable paths captured from actual successful native invocations, rather than resolved again after checking. Several paths can occur if a selected symlink changes between invocations. |
| `checker_identity` | `"unpinned"`: the executable was selected and invoked, but its bytes were not checked against a trusted binary identity. A canonical path is not attestation. |
| `native_decisions.count` | Number of successful native acceptance decisions observed during this source check, including repeated decisions and decisions for partial source contracts. |
| `native_decisions.requests_checked` | Number of those decisions with a separate native request payload checked by Lean. This counts decisions, not distinct source declarations or whole-source meanings. |
| `native_decisions.complete` | Whether the metadata covers every successful decision and its checker path. If false, the bounded report is incomplete and its path list or counts must not be treated as exhaustive. |
| `entry.present` | Whether the ordinary project has a supported `main::main` entry. A library without that entry can check successfully. |
| `entry.request_checked` | Whether that entry's own accepted artifact has a separately checked native request payload; `null` when there is no entry. Producer-generated typed requests count here without establishing an independent algorithm specification. Requests on other roots or partial contracts do not change this value. |
| `entry.ordinary_result_checked` | Whether this entry retains the native ordinary-v2 input/result and all-hidden-history check. False for absent entries and other modes. |
| `entry.runtime_result_checked` | Whether this entry retains the native `finite-runtime-root-v2` check of complete type/storage, quantum code space and all hidden histories. True also for a version-5 decision, whose request carries the runtime-root request. False for absent entries and other modes. |
| `entry.source_body_scope` | Optional. Present only when the entry retains a version-5 decision. Its value is the checked profile name, such as `finite-source-qmatch-context-v5`. The text report prints it on the line `entry source body checked:`. |
| `concrete_ir_roots.local`, `concrete_ir_roots.bundled` | Counts of checked concrete ordinary function roots, separating loaded project/dependency modules from bundled library modules. |
| `source_preservation_verified` | `false`: this command does not prove source-to-IR preservation. |

Rules for reading the counts:

- All loaded bundled concrete functions are checked, including unused ones.
  Their decisions and roots therefore contribute to the report.
- Generic operation expansions occur within enclosing concrete roots. A
  registered specialization is not an additional root.
- Constructing or declaring an unused Meaning does not imply that Lean checked
  a corresponding equation.
- Pure, function and instrument contract requests have their individual
  native scopes. When they are separate external requests, their successful
  decisions contribute to `requests_checked`. They assert no whole-entry
  Meaning or general source preservation. A positive aggregate request count
  can accompany `entry.request_checked: false`.
- The request fields describe the separate external request payload, not
  Meaning entries embedded in an ordinary QIRF artifact. A zero request count
  does not claim that no embedded Meaning was checked.
- A reachable `FunctionEvidence` dependency is checked with its ordinary QIRF
  root. That invocation contributes to the decision count and has no separate
  request payload. Reading the counters does not identify or prove its exact
  dependency equation.
- Request data can itself be producer generated. Checking it does not
  establish an independent specification of the original source.

Reports of the other commands:

- On the [selected-entry route](diagnostics.md#routes), `check --entry ...`
  reports the singular actual `checker_path` of the selected root,
  `checker_identity: "unpinned"`, `request_checked` and
  `source_preservation_verified: false`, beside its `verification` scope and
  `request_origin`. These fields describe the receipt of the selected root.
  They are not an aggregate of every native decision made while preparing and
  checking the source.
- The native-validity scope of the Raw route is distinct from the hierarchy
  composition, Fourier, instrument and named-QPE request scopes.
- Finite artifact reports also expose `ordinary_result_checked` and
  `runtime_result_checked`, with the meanings of the project-entry fields.
  They expose the optional `source_body_scope` in the same way, and the text
  report prints it on the line `source body checked:`.
- `request_checked: true` also applies to a checked producer-consistency
  request. It does not assert an independent specification of the Meaning of
  the source. `source_meaning_verified: false` stays explicit.
- `verify-ir` reports the singular actual `checker_path` of the checked
  artifact, `checker_identity: "unpinned"` and `request_checked`. With
  `--against`, the request result applies to that exact supplied pair of
  artifact and request.
- `emit-ir` reports its output `path` with the checker and request metadata of
  the emitted root.
- The text successes of `verify-ir` and `emit-ir` state the IR and request
  scope. Success of neither command establishes preservation from a source, a
  trusted binary identity, or correctness of downstream execution or export.
- `interop check` uses the same singular actual-root metadata in its JSON
  success. Importing foreign source and accepting its lowered artifact do not
  prove translation preservation.
- Request-free success is a successful structural check. No independent
  Meaning is inferred from it.
- The report fields alter no acceptance rule, proof scope or admitted
  constitutional guarantee.

### Public operations that confer no acceptance

| Operation | Scope |
| --- | --- |
| `RawProgram`, `RawOp`, `native::Proposal::{new,from_raw}` | Untrusted IR or serialized proposals. Structural validity does not imply native acceptance. The 22 RawOp constructor coverage entries describe their checking coverage, not constructor authority. |
| `Circuit::new`, `Encoding::{new,identity}`, `Contract::new`, `FiniteMeaning::{permutation,phase,matrix,target_ir}`, `UnitaryBoundary::new`, matrix codecs | Descriptions, exact arithmetic and bounded host construction. A proposed meaning is not evidence that an implementation has that meaning. |
| `qleisli doc` → `render_markdown` | Reads/parses documentation and returns before source compilation. It confers no type or semantic acceptance. |
| Source loading, edition configuration and `Kernel::new` | Configure files or a checker path. Later checking can fail. |
| Checked-object accessors and `check_binding` / `check_entry` | Retain or compare the original checked identity and scope; they do not perform a fresh semantic acceptance decision. |
| Foreign export | Consumes `AcceptedProgram` and emits target text. The terminal OpenQASM adapter can project a closed typed source result to its ordered measured bits, or emit no bits for Unit. Input acceptance does not prove preservation of the emitted OpenQASM/QIR or target execution. QIRF export separately performs a fresh native validity check on its output; output validity alone is not a translation theorem. |
| `sim`, `host`, hierarchy execution and sampling | Execute already checked descriptions numerically. Acceptance and bounded reference tests do not establish runtime or floating-point preservation. |

Rules for the `H; Z; H` replacement in OpenQASM/QIR export:

- Export may replace three adjacent actual expanded function steps,
  `H; Z; H`, with the existing X/CX/CCX word. The target axis and the ordered
  zero, one or two controls, including polarity, must match in all three
  steps. Z must have identity permutation and exact eighth-turn phases
  `[0,4]`.
- No source name or inferred label authorizes this replacement, and no step
  commutes across another. Nonmatching words keep the emitter policy. The
  original accepted graph, source types, owners and dependencies stay intact.
- A final target-word pass also recognizes exactly adjacent uncontrolled
  `H; Z; H` on one identical physical operand, including words separated by
  pure Raw operation boundaries. It reads the actual emitted gate definitions
  and operand maps. It uses the same native equation gate, receipt cache and
  export-wide work counter.
- Allocation, singleton preparation, measurement and discard boundaries
  prevent a window from crossing them. No phase folding, commuting or
  source-name lookup creates a window.
- The final pass starts only after the gate stream from cursor normalization
  and lowering has satisfied the 4,096-gate cap. Final shortening cannot admit
  an otherwise over-limit emitted stream. Other target limits and original
  checked obligations are unchanged.
- Each distinct compact pair of original and replacement Raw requires the
  native function-equation check under the checker of the input
  `AcceptedProgram`. The local comparison retains full scalar phase and
  ordered control polarities.
- An export retains at most seven complete-body local receipts. It shares the
  20,000,000 exact-work budget across all Raw operations.
- Unavailable checking, rejection or exhausted capacity produces no artifact
  and no alternate acceptance path.
- This bounded local comparison is not a general source, target-emission,
  physical-resource or external-QIS preservation theorem. The local equations
  do not establish general source/export, resource or external QIS
  preservation. The two adopted guarantees and the pending QS/PR/RS/EXACT
  obligations keep their scopes.

Rules for explicit module-map source selection:

- Explicit module-map source selection parses, instantiates, elaborates and
  lowers untrusted proposals. Ordinary commands with explicit entry and
  module bindings use the shared source execution plan.
- `emit-proposal` writes transport without constructing a kernel and reports
  `untrusted-proposal`.
- The preselected Raw route uses ordinary native acceptance. It then
  separately compares the accepted instructions with the retained source
  steps.
- The hierarchy route retains dedicated request, Fourier, instrument or
  named-QPE checking and the required initialization-move binding.
- A native failure cannot switch routes or discard the request of the caller.
- Selected checking and execution results retain
  `source_meaning_verified: false`. Native validity, producer consistency,
  caller composition and named-QPE requests have distinct scopes.
- Neither source-step comparison nor general lowering preservation follows
  merely from an accepted proposal.
  [Selected-source execution](type-model.md#selected-source-execution) states
  the other invocation and checking-profile boundaries.

Rules for the Isometry profile of the hierarchy route:

- A source root with a checked public Isometry contract and an actual Unitary
  or Isometry body uses the supported Isometry profile through the
  `check_instrument_native` boundary. The profile has fresh-zero preparation,
  checked unitary evolution and a readout with zero measurements. A unitary
  body needs no preparation step.
- This transport selection preserves the public bound. It does not rewrite the
  actual source-step or Raw effect to Isometry.
- The quantum entry and result trees, zero-width owners and the complete live
  frame are part of the proposal and its initialization-move comparison.
- At most one ordinary `Bits<0>` result may accompany the quantum results. The
  empty outcome of the transport does not create a source Observe effect.
- Isometry execution returns its single unnormalized branch with scalar phase
  retained.
- Sampling requires a checked public Observe contract and an actually
  observing supported artifact.
- Conservative public bounds cannot recover sharper source eligibility or
  fabricate actual operations. The Raw profile keeps its actual classification
  and explicit support limits. A public Observe contract over a pure body is
  outside this hierarchy profile.
- This adapter reuses component checks. It introduces no native primitive,
  accepted-handle authority, formal theorem or constitutional guarantee. The
  ordinary QLV1 ownership and scope admissions do not extend to this hierarchy
  path.
- An independent hierarchy request must fit the supported composition
  language. A whole-root finite-matrix request cannot replace the required
  child structure of a composite root.
- Producer consistency, the bounded initialization and source-step comparison
  and numerical execution observations keep their separate scopes. General
  source preservation and the complete native analytic/operator and runtime
  correspondence duties are pending.

### Numerical result presentation

- Closed-project `run` reports a numerical reference distribution. Text uses
  scientific notation with twelve digits after the decimal point. JSON retains
  numeric probabilities under the output range policy.
- Sampling uses the numerical execution model. A small floating-point residue
  can appear at a mathematically zero outcome.
- For project-mode text `run`, `--show-exact-zeros` appends `[exact zero]` to
  a displayed row when a bounded calculation finds its exact amplitude equal
  to zero. Each numerical value and output word stays in the original order.
  The formatter uses no probability threshold and leaves unlisted rows absent.
  The option is exclusive to project-mode text `run`.
- The calculation uses the retained Raw of a closed, already accepted program.
  The profile permits vacuum preparation, structural register and Unit
  operations, injective `LiftBasis`, exact Hadamard and monomial steps, and
  sealed coherent selection with its full phase.
- Each `LiftBasis` appends fresh zero axes and uses the actual table in
  declared axis order. Terminal Z measurement reads each axis once, and the
  result contains each measured bit once.
- A program outside this profile, or an exhausted resource or arithmetic
  limit, prints the numeric distribution and reports why the exact annotation
  is unavailable. Default text, JSON and seeded sampling keep their numerical
  behavior.
- The annotation is presentation evidence within this bounded Raw profile.
  The native checker is the authority for exact contracts and accepted
  handles.

| Limit of the exact annotation | Value |
| --- | --- |
| Allocated axes | Six |
| Raw operations | 2,048 |
| Expanded steps | 1,024 |
| Exact evaluation budget | One million units, separate, with the finite dyadic complex arithmetic used for circuit proposals |

### Coverage checks

- `tests/fixtures/verification_v029/coverage.json.xz` separates current
  implementation, published 0.2.9 validation, unpublished development and
  open proof obligations. It records the current coverage groups, boundary
  entry lists, constructor variants and classified paths.
- Engineering comparisons and the check-only nominal carrier component have
  distinct classifications. Mixed boundary rows refer to individually
  classified paths. A public surface that contains a constructor or `doc` is
  not counted wholesale as native acceptance.
- `scripts/check_production_coverage.py` checks the reviewed public surface,
  complete path classifications, all native modes and dispatch targets, named
  source and declaration bindings and existing regression functions.
- The script fails on an omitted route, an exposed boundary that the inventory
  lacks, changed dispatch, a missing binding or a proposal misclassified as
  acceptance. The native-contract proof scope also retains the explicit
  encoded-equation and guarantee-admission limits.
- These checks detect inventory drift. Source markers and test existence are
  not formal proof or evidence that a test has just run. The underlying
  inventories, actual tests, proof builds and audits are necessary.
- Existing regression bindings include `tests/native_paths.rs`,
  `tests/function_evidence.rs`, `tests/semantic_contracts.rs`,
  `tests/finite_leaf.rs`, `scripts/test_source_kernel.py`,
  `scripts/test_interop_native.py`, `tests/hierarchical_host.rs`,
  `tests/hierarchical_qpe_host.rs`, `tests/sized_source.rs`, and the explicit
  no-kernel proposal test in `tests/sized_cli.rs`. The separate `doc`
  regression is in `tests/cli.rs`.
- Their bounded observations do not replace S05 proofs or human review of the
  intended semantics.

## History

- Production acceptance completed the adopted migration to one native Lean
  implementation under the
  [single-verifier decision #276](https://github.com/MGYamada/Qleisli/issues/276).
- Version 0.2.9 was published and verified. Its immutable record is
  `tests/fixtures/releases/v0.2.9/publication.json`. The record binds source
  commit `a77e68f4d3942cd75cb4c4710350aab9a99f8c8b`, the full CI run, the
  registry and GitHub distribution checks, the native bundles and fresh
  installation evidence.
- The selected development version 0.3.0-beta is unpublished. The historical
  release record does not certify the changed beta tree or its future
  packages.
- The earlier VM29 first-slice, comparison and cutover records are historical
  evidence with their original scopes and results.
- The shared exact-work ceiling was 10,000,000 and then 13,000,000 units. A
  client that uses either earlier ceiling must update the Rust frontend and
  the Lean checker together.
- The changelog calls dispatch of the version-5 request from the public
  compile path "public v5", and the full qmatch profile "full12/64". The
  production compile path dispatches the version-5 request.
- The preparation-work exception of the two-qubit general-composition
  development regression is tracked by
  [#472](https://github.com/MGYamada/Qleisli/issues/472).
- The whole-project `result` fields replaced the former `{"verified":true}`.
  A client that used the former source-check `verified` boolean must inspect
  the explicit scope fields. The former unqualified `verified: true` of
  `verify-ir` and `interop check` is also retired.
- Binary identity pinning is tracked by
  [#302](https://github.com/MGYamada/Qleisli/issues/302).
- The reachable-module policy is the subject of
  [#273](https://github.com/MGYamada/Qleisli/issues/273).

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
