import Qleisli.RuntimeSparseBlockEncoding
import Qleisli.CodeSpaceAction
import Qleisli.RuntimeNamedSourceFlow
import Qleisli.RawProtectedEvaluation
import Qleisli.RuntimeCallHistoryPure
import Qleisli.RuntimeLiteralStructuralRefinement

/-! Lift a checked local code-space map over an ordered block of original
source owners. Each coefficient keeps the full spectator and reference
amplitudes. The physical map is supplied by the original local matrix read.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeSparseOperationAction
open QleisliKernel QleisliKernel.Qirf
open Semantics.Finite (gather)
open Semantics.FiniteCarrier (encoding)
open Semantics.Exact (Matrix)
open RuntimeOwnerMap (Binding Map)
open RuntimeForestCode (carrierOwners forestAxes ofLayout_agrees)
open Qleisli.RuntimeSemanticForest
  (Available Frame action product forest_read frame_exists regroup_action)
open Qleisli.RuntimeSparseBlockEncoding (coefficient block_action product_width)
open Qleisli.RuntimeForestProduct (gather_bound)
open Qleisli.RuntimeNamedHeadCoefficients
  (fibre applyHead headEncoding head_code_action_total head_operator_encoding_total)
open Qleisli.RuntimeForestRegroup (sourceDimension)
open Qleisli.MixedRadix (recode)
open Qleisli.Semantics.Exact (scalar)

/-- The matrix read by the native checker is the code of the complete
source-ordered owner block. Its layout proof includes zero-width owners. -/
theorem original_block_code {bindings : Map} {native : Matrix}
    (read : RuntimeInterval.Computed (Carrier.ownerCode (carrierOwners bindings)) native) :
    Available bindings ∧ native = encoding (product bindings) := by
  obtain ⟨work,left,performed⟩ := read
  obtain ⟨⟨start,finish,codeRead⟩,owners⟩ := Carrier.ownerCode_conditions _ _ work left performed
  have available : Available bindings := by
    intro binding member
    obtain ⟨layout,layoutRead,bits,wires⟩ :=
      owners _ (List.mem_map_of_mem (f := fun binding : Binding =>
        (⟨binding.port,binding.owner.basis⟩ : Semantics.CarrierInterface.Owner)) member)
    exact ⟨⟨layout,layoutRead,bits,wires⟩⟩
  obtain ⟨layout,_,_,actual,same,_⟩ :=
    QleisliKernel.FiniteCarrier.code_conditions _ _ start finish codeRead
  exact ⟨available,same.trans (congrArg encoding
    (Option.some.inj (actual.symm.trans (forest_read available))))⟩

private theorem selected_bound {selected : Map} (available : Available selected)
    (physicalFrame : List Nat) (row : Nat) :
    gather row (forestAxes physicalFrame selected) < (encoding (product selected)).rows := by
  change _ < 2^(product selected).bits
  rw [product_width available]
  simpa only [forestAxes,List.length_map] using gather_bound row (forestAxes physicalFrame selected)

/-- Expose the original selected block's native code action on a sparse
source frame in selected-then-spectator order. -/
theorem block_native_encoding {selected spectators : Map} (frame : Frame (selected++spectators))
    (physicalFrame : List Nat) {Reference : Type} (joint : Nat → Reference → ℂ)
    (row : Nat) (reference : Reference) :
    action frame physicalFrame joint row reference =
      headEncoding (encoding (product selected)) (product spectators).labels.length
        (coefficient spectators physicalFrame row) joint
        (gather row (forestAxes physicalFrame selected)) reference := by
  have available : Available selected := fun binding member =>
    frame.available binding (List.mem_append_left _ member)
  rw [head_code_action_total,block_action]
  unfold Qleisli.Semantics.Exact.action
  apply Qleisli.Exact.sum_map_congr
  intro digit member
  have bounded : digit < (product selected).labels.length := List.mem_range.mp member
  have rowBound := selected_bound available physicalFrame row
  have equal := (ofLayout_agrees (product selected)).encodingEntry
    (gather row (forestAxes physicalFrame selected)) digit rowBound bounded
  unfold coefficient Qleisli.Semantics.Exact.entry
  rw [equal]
  rfl

private theorem bindings_unique {roles state} (checked : RuntimeOwnerMap.Checked roles state) :
    checked.bindings.Nodup :=
  List.Pairwise.of_map (fun binding : Binding => binding.port.token)
    (fun _ _ different same => different (congrArg (fun binding : Binding => binding.port.token) same))
    checked.tokensDistinct

private noncomputable def groupedInput {Reference : Type}
    (incoming selected spectators : Map) (joint : Nat → Reference → ℂ) : Nat → Reference → ℂ :=
  fun logical reference =>
    joint (recode (selected++spectators) incoming (sourceDimension incoming) logical) reference

/-- Apply the selected source matrix on each spectator coordinate, then
restore the caller's original output owner order. -/
noncomputable def applySourceBlock {Reference : Type}
    (incoming outgoing selected returned spectators : Map) (logical : Matrix)
    (joint : Nat → Reference → ℂ) : Nat → Reference → ℂ :=
  fun index reference =>
    applyHead logical (groupedInput incoming selected spectators joint)
      (recode outgoing (returned++spectators) (sourceDimension (returned++spectators)) index) reference

/-- An input and output encoding on the original caller owner order.
Every native row is evaluated on its corresponding spectator fibre. -/
def BlockCodeLift {inputRoles outputRoles before after}
    (incoming : RuntimeOwnerMap.Checked inputRoles before)
    (outgoing : RuntimeOwnerMap.Checked outputRoles after)
    (input : Frame incoming.bindings)
    (selected returned spectators : Map) (inputCode physical logical : Matrix) : Prop :=
    ∃ output : Frame outgoing.bindings,
      ∀ {Reference : Type} (joint : Nat → Reference → ℂ) (row : Nat) (reference : Reference),
        let grouped := groupedInput incoming.bindings selected spectators joint
        let initial := fibre inputCode.cols (product spectators).labels.length
          (coefficient spectators before.quantum.frame row) grouped
        let final := fibre inputCode.cols (product spectators).labels.length
          (coefficient spectators after.quantum.frame row) grouped
        action input before.quantum.frame joint row reference =
          Qleisli.Semantics.Exact.action inputCode initial
            (gather row (forestAxes before.quantum.frame selected)) reference ∧
        action output after.quantum.frame
            (applySourceBlock incoming.bindings outgoing.bindings selected returned spectators logical joint) row reference =
          Qleisli.Semantics.Exact.action physical
            (fun digit ref => Qleisli.Semantics.Exact.action inputCode final digit ref)
            (gather row (forestAxes after.quantum.frame returned)) reference

/-- For every caller row, the full output code of the evolved source block
equals the checked physical map on the matching spectator/reference fibre.
The input identity is on the same actual caller owner order. -/
theorem operation_code_lift {inputRoles outputRoles before after}
    (incoming : RuntimeOwnerMap.Checked inputRoles before)
    (outgoing : RuntimeOwnerMap.Checked outputRoles after)
    (input : Frame incoming.bindings)
    {selected returned spectators : Map}
    (beforeOrder : (selected++spectators).Perm incoming.bindings)
    (afterOrder : (returned++spectators).Perm outgoing.bindings)
    {inputCode outputCode physical logical : Matrix}
    (inputRead : RuntimeInterval.Computed (Carrier.ownerCode (carrierOwners selected)) inputCode)
    (outputRead : RuntimeInterval.Computed (Carrier.ownerCode (carrierOwners returned)) outputCode)
    (checked : QleisliKernel.CodeSpace.Map inputCode outputCode physical)
    (same : checked.logical = logical) :
    BlockCodeLift incoming outgoing input selected returned spectators inputCode physical logical := by
  obtain ⟨_,inputEq⟩ := original_block_code inputRead
  obtain ⟨returnedAvailable,outputEq⟩ := original_block_code outputRead
  have availableOut : Available (returned++spectators) := by
    intro binding member
    rcases List.mem_append.mp member with operated | untouched
    · exact returnedAvailable binding operated
    · exact input.available binding (beforeOrder.subset (List.mem_append_right _ untouched))
  obtain ⟨groupedIn⟩ := frame_exists (fun binding member => input.available binding (beforeOrder.subset member))
  obtain ⟨groupedOut⟩ := frame_exists availableOut
  obtain ⟨output⟩ := frame_exists (fun binding member => availableOut binding (afterOrder.symm.subset member))
  have uniqueOut := afterOrder.symm.nodup (bindings_unique outgoing)
  refine ⟨output,?_⟩
  intro Reference joint row reference grouped initial final
  constructor
  · rw [regroup_action input groupedIn beforeOrder.symm (bindings_unique incoming)]
    change action groupedIn before.quantum.frame grouped row reference = _
    rw [block_native_encoding,← inputEq,head_code_action_total]
  · change action output after.quantum.frame
      (fun index ref => applyHead logical grouped
        (recode outgoing.bindings (returned++spectators) (sourceDimension (returned++spectators)) index) ref)
      row reference = _
    rw [← regroup_action groupedOut output afterOrder uniqueOut after.quantum.frame (applyHead logical grouped) row reference]
    rw [block_native_encoding,← outputEq]
    have dimensions := checked.logicalShape
    rw [same] at dimensions
    rw [head_operator_encoding_total _ _ _ _ _ _ _ dimensions.2.symm,dimensions.1]
    have bounded : gather row (forestAxes after.quantum.frame returned) < physical.rows := by
      rw [checked.physicalShape.2,outputEq]
      exact selected_bound returnedAvailable _ _
    rw [Qleisli.CodeSpace.map_reference_action checked final _ reference bounded,same]

private theorem carrier_order (bindings : Map) :
    carrierOwners bindings =
      ((bindings.map (·.port)).zip (bindings.map (·.owner))).map
        (fun (port,role) => (⟨port,role.basis⟩ : Semantics.CarrierInterface.Owner)) := by
  induction bindings with
  | nil => rfl
  | cons first rest ih =>
    simp only [carrierOwners,List.map_cons,List.zip_cons_cons] at ih ⊢
    rw [ih]

/-- The actual literal operation supplies the ordered native code reads
and the local program's independent matrix meaning. These determine the
full caller code action whenever the two owner partitions share the
same spectators. -/
theorem original_operation_code_lift {dependencies program block arity start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block arity start count inputs outputs roles)
    {before after : RuntimeStructuralAction.SourceState}
    (ownerOrder : Qleisli.RuntimeNamedSourceFlow.OperationOwnerOrder frame before after)
    {inputRoles outputRoles}
    (incoming : RuntimeOwnerMap.Checked inputRoles frame.interval.before)
    (outgoing : RuntimeOwnerMap.Checked outputRoles frame.interval.after)
    (initial : incoming.bindings = before.bindings) (final : outgoing.bindings = after.bindings)
    (input : Frame incoming.bindings)
    {inputCode outputCode physical logical : Matrix}
    (inputRead : RuntimeInterval.Computed
      (Carrier.ownerCode ((frame.selected.zip roles).map fun (port,role) => ⟨port,role.basis⟩)) inputCode)
    (outputRead : RuntimeInterval.Computed
      (Carrier.ownerCode ((frame.returned.zip roles).map fun (port,role) => ⟨port,role.basis⟩)) outputCode)
    (physicalRead : RuntimeInterval.Computed
      (Raw.ProtectedEvaluation.reconstruct dependencies
        (RuntimePureInterval.fragment frame.selected frame.operations outputs)) physical)
    (checked : QleisliKernel.CodeSpace.Map inputCode outputCode physical)
    (same : checked.logical = logical) :
    ∃ selected returned,
      RuntimeInterval.Computed (RuntimeOwnerMap.order roles incoming.bindings) selected ∧
      RuntimeInterval.Computed (RuntimeOwnerMap.order roles outgoing.bindings) returned ∧
      frame.selected = selected.map (·.port) ∧ frame.returned = returned.map (·.port) ∧
      Qleisli.Semantics.Raw.ProgramMeaning dependencies
        (RuntimePureInterval.fragment frame.selected frame.operations outputs) physical ∧
      ∀ spectators, (selected++spectators).Perm incoming.bindings →
        (returned++spectators).Perm outgoing.bindings →
        BlockCodeLift incoming outgoing input selected returned spectators inputCode physical logical := by
  obtain ⟨inputOrder,outputOrder⟩ := ownerOrder.ordered_ports incoming outgoing initial final
  obtain ⟨selected,selectedRead,_,selectedRoles,selectedPorts⟩ := initial.symm ▸ inputOrder
  obtain ⟨returned,returnedRead,_,returnedRoles,returnedPorts⟩ := final.symm ▸ outputOrder
  obtain ⟨work,left,reconstructed⟩ := physicalRead
  refine ⟨selected,returned,selectedRead,returnedRead,selectedPorts,returnedPorts,
    Qleisli.Raw.ProtectedEvaluation.reconstruct_denotes dependencies _ physical work left reconstructed,?_⟩
  intro spectators beforeOrder afterOrder
  apply operation_code_lift incoming outgoing input beforeOrder afterOrder _ _ checked same
  · simpa only [carrier_order,selectedRoles,← selectedPorts] using inputRead
  · simpa only [carrier_order,returnedRoles,← returnedPorts] using outputRead

private theorem owner_projection (parent : Semantics.RawTrace.Interface) (bindings : Map) (row : Nat) :
    Qleisli.RuntimeCallHistory.project parent (RuntimeCallTraceFrames.WireOrder (bindings.map (·.port))) row =
      gather row (forestAxes parent.frame bindings) := by
  simp only [Qleisli.RuntimeCallHistory.project,Semantics.RawTrace.axes,forestAxes,List.flatMap_map]

/-- The paired literal event lists identify the full caller's finite rows
with the local matrix on their exact spectator fibre. The output uses the
same caller history and its original source owner order. -/
theorem operation_events_lift {dependencies inputRoles outputRoles before after}
    (incoming : RuntimeOwnerMap.Checked inputRoles before)
    (outgoing : RuntimeOwnerMap.Checked outputRoles after)
    (input : Frame incoming.bindings)
    {selected returned spectators : Map} {inputCode physical logical : Matrix}
    (lifted : BlockCodeLift incoming outgoing input selected returned spectators inputCode physical logical)
    {child childAfter : Semantics.RawTrace.Interface}
    (childEntry : child.frame = RuntimeCallTraceFrames.WireOrder (selected.map (·.port)))
    (childExit : RuntimeCallTraceFrames.WireOrder (returned.map (·.port)) ⊆ childAfter.frame)
    {parentEvents childEvents : List Semantics.Raw.Event}
    (bounded : RawFiniteRows.BoundedEvents before.quantum.frame.length parentEvents after.quantum.frame.length)
    (paired : Qleisli.RuntimeCallHistory.PureAction dependencies before.quantum.reference child
      after.quantum.reference childAfter (spectators.map (·.port)) parentEvents childEvents)
    (localMatrix : ∀ {Reference : Type} (joint : Nat → Reference → ℂ) row reference,
      row < 2^childAfter.frame.length →
      Qleisli.Semantics.RawAction.events dependencies childEvents (fun digit => joint digit reference) row =
        Qleisli.Semantics.Exact.action physical joint
          (Qleisli.RuntimeCallHistory.project childAfter
            (RuntimeCallTraceFrames.WireOrder (returned.map (·.port))) row) reference)
    (source : Nat → Nat → ℂ) (actual : Qleisli.Semantics.ObservingAction.History)
    (represents : Qleisli.RuntimeStructuralHistory.Represents input before actual source) :
    ∃ output : Frame outgoing.bindings,
      Qleisli.RuntimeStructuralHistory.Represents output after
        (Qleisli.RuntimeNamedThreePackedInstrument.pureHistory dependencies parentEvents actual)
        (applySourceBlock incoming.bindings outgoing.bindings selected returned spectators logical source) := by
  obtain ⟨output,encodings⟩ := lifted
  refine ⟨output,?_⟩
  intro column row within
  let grouped := groupedInput incoming.bindings selected spectators source
  let joint := fun digit high ref =>
    Qleisli.Semantics.Exact.action inputCode
      (fibre inputCode.cols (product spectators).labels.length
        (fun logical => scalar (RuntimeForestCode.sparseEntry (.ofLayout (product spectators)) high logical)) grouped)
      digit ref
  have beforeAction (physical : Nat) :
      action input before.quantum.frame source physical column =
        joint (Qleisli.RuntimeCallHistory.project before.quantum.reference child.frame physical)
          (Qleisli.RuntimeCallHistory.project before.quantum.reference
            (RuntimeCallTraceFrames.WireOrder (spectators.map (·.port))) physical) column := by
    rw [childEntry,owner_projection,owner_projection]
    exact (encodings source physical column).1
  have exactInputs := funext beforeAction
  have result := Qleisli.RuntimeNamedThreePackedInstrument.pureHistory_operator_congr bounded dependencies actual
    (fun physical ref => action input before.quantum.frame source physical ref) represents column row within
  have localRow : Qleisli.RuntimeCallHistory.project after.quantum.reference childAfter.frame row < 2^childAfter.frame.length := by
    simpa only [Qleisli.RuntimeCallHistory.project,Semantics.RawTrace.axes,List.length_map] using
      gather_bound row (Semantics.RawTrace.axes after.quantum.reference childAfter.frame)
  have actualLocal := paired (fun digit high => joint digit high column) row within
  rw [exactInputs,actualLocal] at result
  rw [localMatrix _ _ column localRow] at result
  have returnedRow :
      Qleisli.RuntimeCallHistory.project childAfter (RuntimeCallTraceFrames.WireOrder (returned.map (·.port)))
        (Qleisli.RuntimeCallHistory.project after.quantum.reference childAfter.frame row) =
      Qleisli.RuntimeCallHistory.project after.quantum.reference
        (RuntimeCallTraceFrames.WireOrder (returned.map (·.port))) row :=
    Qleisli.RuntimeOriginalObservation.gather_retained _ _ _ _ rfl childExit row
  rw [returnedRow,owner_projection,owner_projection] at result
  exact result.trans (encodings source row column).2.symm

/-- Carry the independently established operator equation back to the
same actual pure step. SSA values and the hidden/measurement history
come from that literal run, including any enclosing scope's IDs. -/
theorem pure_step_history_lift {dependencies program block}
    (node : RuntimePureBody.Node dependencies program block)
    (inputs : List Nat) (inherited : Option (Nat → Prop))
    {before after : RuntimeStructuralAction.SourceState} {ordinary : RuntimeOrdinaryBody.State}
    {outputRoles} (outgoing : RuntimeOwnerMap.Checked outputRoles (Qleisli.RuntimeLiteralBody.nodeSpan node).checked.after)
    (outputOrder : outgoing.bindings = after.bindings)
    (source : Qleisli.RuntimeLiteralBody.SourceHistory) (actual : Qleisli.Semantics.ObservingAction.History)
    (operator : Nat → Nat → ℂ) {events results} :
    let span := Qleisli.RuntimeLiteralBody.nodeSpan node
    Qleisli.RuntimeLiteralBody.SemanticHistoryAgreesWithInherited inherited inputs span.checked.before before ordinary
      source actual →
    Semantics.Observation.readOps block.fuel span.checked.before.quantum.reference span.operations =
      some (span.checked.after.quantum.reference,events) →
    Qleisli.Semantics.ObservingAction.run dependencies block.fuel events actual = some results →
    (∀ operations rawEvents, span.operations = operations.map Semantics.Observation.Op.pure →
      RuntimeLocalEvents.trace span.checked.before.quantum.reference operations =
        some ⟨span.checked.after.quantum.reference,rawEvents,span.checked.before.quantum.frame.length⟩ →
      ∃ output : Frame outgoing.bindings,
        Qleisli.RuntimeStructuralHistory.Represents output span.checked.after
          (Qleisli.RuntimeNamedThreePackedInstrument.pureHistory dependencies rawEvents actual) operator) →
    List.Forall₂ (Qleisli.RuntimeLiteralBody.SemanticHistoryAgreesWithInherited inherited inputs
      span.checked.after after ordinary) [{source with owners := after, operator}] results := by
  intro span agrees read executed represents
  obtain ⟨operations,rawEvents,literal,trace,rfl,ordinaryAfter⟩ :=
    Qleisli.RuntimeLiteralHistory.pure_history_with_inherited node inherited inputs ordinary actual
      agrees.2.2.2.1 read executed
  obtain ⟨output,encoded⟩ := represents operations rawEvents literal trace
  exact .cons ⟨rfl,agrees.2.1,agrees.2.2.1,ordinaryAfter,_,outgoing,outputOrder,
    outputOrder ▸ output,Qleisli.RuntimeLiteralBody.cast_represents outputOrder output encoded⟩ .nil

#print axioms original_block_code
#print axioms operation_code_lift
#print axioms original_operation_code_lift
#print axioms operation_events_lift
#print axioms pure_step_history_lift
end Qleisli.RuntimeSparseOperationAction
