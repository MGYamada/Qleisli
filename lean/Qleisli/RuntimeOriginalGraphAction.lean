import Qleisli.RuntimeSparseOperationAction
import Qleisli.RawProtectedMatrixAction

/-! The graph operation's original checked interval and reconstructed local
matrix supply the same full caller history, including its inherited SSA.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeOriginalGraphAction
open QleisliKernel QleisliKernel.Qirf
open QleisliKernel.Semantics.Exact (Matrix)
open Qleisli.Semantics.Exact (action)
open Qleisli.RuntimeLiteralBody (SourceHistory SemanticHistoryAgreesWithInherited cast_represents
  StepRefinement WithChunkWriteBound)
open Qleisli.RuntimeNamedSourceFlow (OperationOwnerOrder)
open Qleisli.RuntimeSparseOperationAction
open Qleisli.RuntimeCallHistory (project)
open RuntimeCallTraceFrames (WireOrder)
open RuntimeOwnerMap (Binding Map Owner)

private def returnedBindings (roles : List Owner) (ports : List Semantics.Raw.Port) : Map :=
  (roles.zip ports).map fun (owner,port) => ⟨owner,port⟩

/-- Reorder the written returns and the untouched bindings in the original
source owner order. No after-state or physical matrix supplies the action. -/
noncomputable def sourceGraphHistory (roles : List Owner) (ports : List Semantics.Raw.Port)
    (logical : Matrix) (source : SourceHistory) : Option (List SourceHistory) := do
  let incoming := source.owners.bindings
  let selected ← roles.mapM (RuntimeOwnerMap.byOwner incoming)
  let returned := returnedBindings roles ports
  let spectators := RuntimeSelectionPartition.complement incoming selected
  let outgoing ← (incoming.map Binding.owner).mapM (RuntimeOwnerMap.byOwner (returned++spectators))
  let operator := applySourceBlock incoming outgoing selected returned spectators logical source.operator
  return [{source with owners := {source.owners with bindings := outgoing}, operator}]

private theorem binding_zip (bindings : Map) :
    returnedBindings (bindings.map Binding.owner) (bindings.map Binding.port) = bindings := by
  induction bindings with
  | nil => rfl
  | cons binding rest ih =>
    rcases binding with ⟨owner,port⟩
    exact congrArg (List.cons ⟨owner,port⟩) ih

private theorem ordered_lookup {roles state} (checked : RuntimeOwnerMap.Checked roles state)
    (bindings : Map) (order : bindings.Perm checked.bindings) :
    (checked.bindings.map Binding.owner).mapM (RuntimeOwnerMap.byOwner bindings) = some checked.bindings := by
  let ordinal := fun binding : Binding => binding.owner.ordinal
  have unique : (checked.bindings.map ordinal).Nodup := by
    simpa only [ordinal,← checked.ordered,List.map_map,Function.comp_def] using checked.ownersDistinct
  have distinct := (order.map ordinal).nodup_iff.mpr unique
  have lookup (binding : Binding) (member : binding ∈ checked.bindings) :
      RuntimeOwnerMap.byOwner bindings binding.owner = some binding := by
    have present := order.mem_iff.mpr member
    unfold RuntimeOwnerMap.byOwner
    cases read : bindings.find? (fun value => value.owner == binding.owner) with
    | none => exact False.elim (List.find?_eq_none.mp read binding present (by simp))
    | some found =>
      have equalOwner : found.owner = binding.owner := beq_iff_eq.mp
        (List.find?_some (p := fun value : Binding => value.owner == binding.owner) read)
      have equal := RuntimeOwnerTransitionAction.map_unique ordinal bindings distinct
        found (List.mem_of_find?_eq_some read) binding present (congrArg (·.ordinal) equalOwner)
      rw [equal]
  have walk (remaining : Map) (present : remaining ⊆ checked.bindings) :
      (remaining.map Binding.owner).mapM (RuntimeOwnerMap.byOwner bindings) = some remaining := by
    induction remaining with
    | nil => rfl
    | cons head tail ih =>
      simp [List.mapM_cons,lookup head (present List.mem_cons_self),ih (fun b member =>
        present (List.mem_cons_of_mem _ member))]
  exact walk checked.bindings (fun _ member => member)

private theorem fragment_action {dependencies program block start count inputs outputs effect}
    (frame : @RuntimePureInterval.Literal dependencies program block start count inputs outputs effect)
    {physical : Matrix}
    (read : RuntimeInterval.Computed (Raw.ProtectedEvaluation.reconstruct dependencies
      (RuntimePureInterval.fragmentWithEffect frame.selected frame.operations outputs effect)) physical)
    (rows : physical.rows = 2^frame.pureBody.state.frame.length)
    {entry : Raw.State} {childEvents}
    (entryRef : entry.reference = ⟨frame.selected,WireOrder frame.selected⟩)
    (trace : RuntimeLocalEvents.trace entry.reference frame.operations =
      some ⟨frame.pureBody.state.reference,childEvents,entry.frame.length⟩)
    {Reference : Type} (joint : Nat → Reference → ℂ) (row : Nat) (reference : Reference)
    (bound : row < 2^frame.pureBody.state.frame.length) :
    Qleisli.Semantics.RawAction.events dependencies childEvents (fun col => joint col reference) row =
      action physical joint (project frame.pureBody.state.reference (WireOrder frame.returned) row) reference := by
  obtain ⟨_,permutation⟩ := Qleisli.RuntimeCallHistory.fragment_finish frame entryRef trace
  have width := permutation.length_eq.trans List.length_range
  have packedBound : project frame.pureBody.state.reference (WireOrder frame.returned) row < physical.rows := by
    simpa only [project,width,rows] using Qleisli.RuntimeForestProduct.gather_bound row
      (Semantics.RawTrace.axes frame.pureBody.state.reference (WireOrder frame.returned))
  obtain ⟨original,readTrace,evaluated⟩ := Qleisli.RuntimeCallHistory.fragment_prefix_action
    frame entryRef trace (fun col => joint col reference) row bound
  obtain ⟨work,left,reconstructed⟩ := read
  exact evaluated.symm.trans
    (Qleisli.Raw.ReconstructedAction.program_action dependencies _ physical work left reconstructed original
      readTrace joint _ reference packedBound).symm

private theorem fragment_represents {dependencies program block start count inputs outputs effect}
    (frame : @RuntimePureInterval.Literal dependencies program block start count inputs outputs effect)
    {interval : RuntimeInterval.Checked block start count} (sameInterval : frame.interval = interval)
    {inputRoles outputRoles}
    (incoming : RuntimeOwnerMap.Checked inputRoles interval.before)
    (outgoing : RuntimeOwnerMap.Checked outputRoles interval.after)
    (input : Qleisli.RuntimeSemanticForest.Frame incoming.bindings)
    {selected returned spectators : Map}
    (beforeOrder : (selected++spectators).Perm incoming.bindings)
    (selectedPorts : frame.selected = selected.map Binding.port)
    (returnedPorts : frame.returned = returned.map Binding.port)
    {inputCode physical logical : Matrix}
    (physicalRead : RuntimeInterval.Computed (Raw.ProtectedEvaluation.reconstruct dependencies
      (RuntimePureInterval.fragmentWithEffect frame.selected frame.operations outputs effect)) physical)
    (rows : physical.rows = 2^frame.pureBody.state.frame.length)
    (lifted : BlockCodeLift incoming outgoing input selected returned spectators inputCode physical logical)
    (operator : Nat → Nat → ℂ) (actual : Qleisli.Semantics.ObservingAction.History)
    (represented : Qleisli.RuntimeStructuralHistory.Represents input interval.before actual operator)
    (operations : List Semantics.Raw.Op) (emitted : List Semantics.Raw.Event)
    (literal : (block.operations.drop start).take count = operations.map Semantics.Observation.Op.pure)
    (traced : RuntimeLocalEvents.trace interval.before.quantum.reference operations =
      some ⟨interval.after.quantum.reference,emitted,interval.before.quantum.frame.length⟩) :
    ∃ output : Qleisli.RuntimeSemanticForest.Frame outgoing.bindings,
      Qleisli.RuntimeStructuralHistory.Represents output interval.after
        (Qleisli.RuntimeNamedThreePackedInstrument.pureHistory dependencies emitted actual)
        (applySourceBlock incoming.bindings outgoing.bindings selected returned spectators logical operator) := by
  subst interval
  have live := incoming.complete.symm.trans (beforeOrder.symm.map Binding.port)
  rw [List.map_append,← selectedPorts] at live
  obtain ⟨entry,parentEvents,childEvents,entryRef,parentTrace,childTrace,exitWires,_,bounded,paired⟩ :=
    Qleisli.RuntimeCallHistory.literal_interval_events frame (spectators.map Binding.port) live
  have entryWires : entry.reference.frame = WireOrder (selected.map Binding.port) := by
    rw [entryRef,selectedPorts]
  rw [returnedPorts] at exitWires
  have localMatrix {Reference : Type} (joint : Nat → Reference → ℂ) row reference
      (bound : row < 2^frame.pureBody.state.frame.length) :
      Qleisli.Semantics.RawAction.events dependencies childEvents (fun col => joint col reference) row =
        action physical joint (project frame.pureBody.state.reference (WireOrder (returned.map Binding.port)) row) reference := by
    simpa only [returnedPorts] using fragment_action frame physicalRead rows entryRef childTrace joint row reference bound
  have sameOps : frame.operations = operations :=
    (List.map_inj_right (f := Semantics.Observation.Op.pure)
      (fun _ _ same => Semantics.Observation.Op.pure.inj same)).mp (frame.literal.symm.trans literal)
  subst operations
  have sameEvents : emitted = parentEvents :=
    congrArg Semantics.RawTrace.Prepared.events (Option.some.inj (traced.symm.trans parentTrace))
  subst emitted
  exact operation_events_lift incoming outgoing input lifted entryWires exitWires bounded paired localMatrix
    operator actual represented

/-- The actual source-ordered graph application supplies the finite operator,
owner state, inherited SSA and hidden history in a single literal result. -/
theorem original_graph_history {dependencies program block arity start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block arity start count inputs outputs roles)
    {inputCode outputCode physical logical : Matrix}
    (inputRead : RuntimeInterval.Computed
      (Carrier.ownerCode ((frame.selected.zip roles).map fun (port,role) => ⟨port,role.basis⟩)) inputCode)
    (outputRead : RuntimeInterval.Computed
      (Carrier.ownerCode ((frame.returned.zip roles).map fun (port,role) => ⟨port,role.basis⟩)) outputCode)
    (physicalRead : RuntimeInterval.Computed (Raw.ProtectedEvaluation.reconstruct dependencies
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) physical)
    (checked : QleisliKernel.CodeSpace.Map inputCode outputCode physical)
    (equation : checked.logical = logical)
    {before after : RuntimeStructuralAction.SourceState} {ordinary : RuntimeOrdinaryBody.State}
    (ownerOrder : Qleisli.RuntimeNamedSourceFlow.OperationOwnerOrder frame before after)
    (rootInputs : List Nat) (inherited : Option (Nat → Prop))
    {source : SourceHistory} {actual : Qleisli.Semantics.ObservingAction.History}
    (agrees : SemanticHistoryAgreesWithInherited inherited rootInputs frame.interval.before before ordinary source actual)
    {events results}
    (read : Semantics.Observation.readOps block.fuel frame.interval.before.quantum.reference
      ((block.operations.drop start).take count) = some (frame.interval.after.quantum.reference,events))
    (executed : Qleisli.Semantics.ObservingAction.run dependencies block.fuel events actual = some results) :
    ∃ expected, sourceGraphHistory roles frame.returned logical source = some expected ∧
      List.Forall₂ (SemanticHistoryAgreesWithInherited inherited rootInputs frame.interval.after after ordinary)
        expected results := by
  have originalAgreement := agrees
  obtain ⟨sourceOwners,_,_,_,_,incoming,initial,input,represented⟩ := agrees
  have retained := ownerOrder
  obtain ⟨afterOwners,_,originalInterval,originalIncoming,transport,originalOrder,final,_⟩ := retained
  let sameExit := Qleisli.RuntimeIntervalStates.same_after originalInterval frame.interval
  let outgoing := Qleisli.RuntimeNamedThreeFrameChain.checkedAt sameExit transport.after
  have outgoingOrder : outgoing.bindings = after.bindings :=
    (Qleisli.RuntimeNamedThreeFrameChain.checkedAt_bindings sameExit transport.after).trans final
  obtain ⟨selected,returned,spectators,selectedRead,returnedRead,selectedPorts,returnedPorts,spectatorOrder,
    beforeOrder,afterOrder,rows,_,lifted⟩ :=
    original_operation_code_lift frame ownerOrder incoming outgoing initial outgoingOrder (initial.symm ▸ input)
      inputRead outputRead physicalRead checked equation
  let node : RuntimePureBody.Node dependencies program block :=
    .operation frame inputCode outputCode physical logical inputRead outputRead physicalRead checked equation
  let operator := applySourceBlock incoming.bindings outgoing.bindings selected returned spectators logical source.operator
  have refined := pure_step_history_lift node rootInputs inherited outgoing outgoingOrder source actual operator
    originalAgreement read executed (fragment_represents frame.toLiteral rfl incoming outgoing (initial.symm ▸ input)
      beforeOrder selectedPorts returnedPorts physicalRead rows lifted source.operator actual
      (cast_represents initial.symm input represented))
  have chosen := Qleisli.RuntimeLiteralHistory.order_source selectedRead
  rw [initial] at chosen
  have returnedRoles := (RuntimeSelectionPartition.order_values _ _ _ returnedRead).2
  have resultBindings : returnedBindings roles frame.returned = returned := by
    rw [returnedPorts]
    exact congrArg (fun order => returnedBindings order (returned.map Binding.port)) returnedRoles.symm |>.trans
      (binding_zip returned)
  have ownerOrder : outgoing.bindings.map Binding.owner = before.bindings.map Binding.owner :=
    (congrArg (List.map Binding.owner)
      (Qleisli.RuntimeNamedThreeFrameChain.checkedAt_bindings sameExit transport.after)).trans
      (transport.after.ordered.trans (congrArg (List.map Binding.owner) originalOrder))
  have rebuilt := ordered_lookup outgoing _ afterOrder
  rw [ownerOrder,outgoingOrder] at rebuilt
  have originalSpectators : RuntimeSelectionPartition.complement before.bindings selected = spectators :=
    initial ▸ spectatorOrder.symm
  let originalOperator := applySourceBlock before.bindings after.bindings selected returned spectators logical source.operator
  refine ⟨[{source with owners := after, operator := originalOperator}],?_,?_⟩
  · simp only [List.mapM_map] at rebuilt
    simpa [sourceGraphHistory,sourceOwners,chosen,resultBindings,originalSpectators,rebuilt,originalOperator] using
      afterOwners.symm
  · simpa only [node,Qleisli.RuntimeLiteralBody.nodeSpan,operator,initial,outgoingOrder,originalOperator] using refined

#print axioms original_graph_history

noncomputable def sourceRectangularHistory (input output : Owner) (returned : Semantics.Raw.Port)
    (logical : Matrix) (source : SourceHistory) : Option (List SourceHistory) := do
  let binding ← RuntimeOwnerMap.byOwner source.owners.bindings input
  let after := RuntimeRectangularOperation.continued source.owners input output returned
  let spectators := RuntimeSelectionPartition.complement source.owners.bindings [binding]
  let operator := applySourceBlock source.owners.bindings after.bindings [binding] [⟨output,returned⟩]
    spectators logical source.operator
  return [{source with owners := after, operator}]

private theorem singleton_order {role bindings} (entry : RuntimePrimitiveSource.PortAt role bindings) :
    RuntimeInterval.Computed (RuntimeOwnerMap.order [role] bindings) [⟨role,entry.port⟩] := by
  obtain ⟨work,left,ran⟩ := entry.original
  unfold RuntimePrimitiveSource.rolePorts at ran
  obtain ⟨ordered,middle,read,returned⟩ := Finite.bind_success _ _ _ _ _ ran
  have ports := (Finite.pure_success _ _ _ _ returned).1
  have roles := (RuntimeSelectionPartition.order_values _ _ _ ⟨work,middle,read⟩).2
  rcases ordered with _ | ⟨binding,tail⟩
  · cases roles
  · cases tail with
    | nil =>
      have roleEq := List.cons.inj roles |>.1
      have portEq := List.cons.inj ports |>.1
      cases binding
      dsimp at roleEq portEq
      subst role
      cases portEq
      exact ⟨work,middle,read⟩
    | cons next rest =>
      simp only [List.map_cons,List.cons.injEq,List.cons_ne_nil,and_false] at roles

/-- Lift the checked local equation to the full caller frame. The two codes
refer to distinct source owners and every spectator and reference is retained. -/
theorem original_rectangular_history {sources caller dependencies program block start count before expected}
    {event : SourceTypes.SourceOperationApplication.Event sources caller}
    {interval : @RuntimeInterval.Checked dependencies program block start count}
    (checked : RuntimeRectangularOperation.Checked event interval before expected)
    (inputs : List Nat) (inherited : Option (Nat → Prop)) {ordinary : RuntimeOrdinaryBody.State}
    {source : SourceHistory} {actual : Qleisli.Semantics.ObservingAction.History}
    (agrees : SemanticHistoryAgreesWithInherited inherited inputs checked.frame.interval.before before ordinary source actual)
    {events results}
    (read : Semantics.Observation.readOps block.fuel checked.frame.interval.before.quantum.reference
      ((block.operations.drop start).take count) = some (checked.frame.interval.after.quantum.reference,events))
    (executed : Qleisli.Semantics.ObservingAction.run dependencies block.fuel events actual = some results) :
    ∃ histories, sourceRectangularHistory checked.source.input checked.source.output checked.returned expected source =
      some histories ∧ List.Forall₂ (SemanticHistoryAgreesWithInherited inherited inputs checked.frame.interval.after
        (RuntimeRectangularOperation.continued before checked.source.input checked.source.output checked.returned)
        ordinary) histories results := by
  have originalAgreement := agrees
  obtain ⟨sourceOwners,_,_,_,_,incoming,initial,input,represented⟩ := agrees
  let selected : Map := [⟨checked.source.input,checked.entry.port⟩]
  let returned : Map := [⟨checked.source.output,checked.returned⟩]
  let spectators := RuntimeSelectionPartition.complement incoming.bindings selected
  let after := RuntimeRectangularOperation.continued before checked.source.input checked.source.output checked.returned
  let frame := checked.frame
  have sameExit : interval.after = frame.interval.after :=
    congrArg (·.after) checked.sameInterval.symm
  let outgoing := Qleisli.RuntimeNamedThreeFrameChain.checkedAt sameExit checked.after
  have outgoingOrder : outgoing.bindings = after.bindings :=
    (Qleisli.RuntimeNamedThreeFrameChain.checkedAt_bindings sameExit checked.after).trans checked.afterBindings
  have selectedRead : RuntimeInterval.Computed
      (RuntimeOwnerMap.order [checked.source.input] incoming.bindings) selected :=
    initial.symm ▸ singleton_order checked.entry
  obtain ⟨selectedIn,selectedRoles⟩ := RuntimeSelectionPartition.order_values _ _ _ selectedRead
  have incomingUnique : incoming.bindings.Nodup :=
    List.Pairwise.of_map (fun binding : Binding => binding.port.token)
      (fun _ _ different same => different (congrArg (fun binding : Binding => binding.port.token) same))
      incoming.tokensDistinct
  have beforeOrder : (selected++spectators).Perm incoming.bindings :=
    RuntimeNamedBlockEncoding.partition_perm _ _ incomingUnique (by simp [selected]) selectedIn
  have spectatorOrder := owner_complement incoming selectedIn selectedRoles
  have afterOrder : (returned++spectators).Perm outgoing.bindings := by
    rw [outgoingOrder]
    change (returned++spectators).Perm
      (before.bindings.filter (fun binding => binding.owner != checked.source.input) ++ returned)
    dsimp only [spectators]
    rw [spectatorOrder,initial]
    simpa only [List.contains_cons,List.contains_nil,Bool.or_false,bne] using
      (List.perm_append_comm : (returned ++ before.bindings.filter
        (fun binding => binding.owner != checked.source.input)).Perm _)
  have localInputs : frame.selected = selected.map Binding.port := checked.entryPort
  have localOutputs : frame.returned = returned.map Binding.port := checked.returnPort
  have inputRead : RuntimeInterval.Computed (Carrier.ownerCode (RuntimeForestCode.carrierOwners selected))
      checked.inputCode := checked.inputRead
  have outputRead : RuntimeInterval.Computed (Carrier.ownerCode (RuntimeForestCode.carrierOwners returned))
      checked.outputCode := checked.outputRead
  obtain ⟨available,code⟩ := original_block_code outputRead
  obtain ⟨returnOrder,valid⟩ := Qleisli.RuntimeCallHistory.literal_return_ports frame
  have wires := ((returnOrder.flatMap_right Semantics.Raw.Port.wires).trans
    (RuntimeCallTraceFrames.native_wires _ valid)).length_eq
  rw [localOutputs,List.flatMap_map] at wires
  have rows : checked.physical.rows = 2^frame.pureBody.state.frame.length := by
    rw [checked.action.physicalShape.2,code]
    change 2^(Qleisli.RuntimeSemanticForest.product returned).bits = _
    rw [Qleisli.RuntimeSparseBlockEncoding.product_width available,wires]
  let node : RuntimePureBody.Node dependencies program block := .rectangularOperation checked
  let operator := applySourceBlock incoming.bindings outgoing.bindings selected returned spectators expected source.operator
  have lifted := operation_code_lift incoming outgoing (initial.symm ▸ input)
    beforeOrder afterOrder inputRead outputRead checked.action checked.equation
  have refined := pure_step_history_lift node inputs inherited outgoing outgoingOrder source actual operator
    originalAgreement read executed (fragment_represents frame rfl incoming outgoing (initial.symm ▸ input)
      beforeOrder localInputs localOutputs checked.physicalRead rows lifted source.operator actual
      (cast_represents initial.symm input represented))
  have chosen := Qleisli.RuntimeLiteralHistory.order_source selectedRead
  rw [initial] at chosen
  have found : RuntimeOwnerMap.byOwner before.bindings checked.source.input = some ⟨checked.source.input,checked.entry.port⟩ := by
    change ([checked.source.input] : List Owner).mapM (RuntimeOwnerMap.byOwner before.bindings) = some
      [⟨checked.source.input,checked.entry.port⟩] at chosen
    cases lookup : RuntimeOwnerMap.byOwner before.bindings checked.source.input with
    | none => simp [List.mapM_cons,lookup] at chosen
    | some binding => simpa [List.mapM_cons,lookup] using chosen
  refine ⟨[{source with owners := after,operator}],?_,refined⟩
  simp [sourceRectangularHistory,sourceOwners,found,operator,initial,outgoingOrder,after,selected,returned,spectators]

/-- Apply the written transform's forward-derived operator, replacing the
selected source owners in the order given by the original return. -/
noncomputable def sourceTransformHistory {sources caller}
    (event : SourceTypes.SourceRuntimeContext.TransformEvent sources caller)
    (ports : List Semantics.Raw.Port) (logical : Matrix) (source : SourceHistory) : Option (List SourceHistory) := do
  let incoming := source.owners.bindings
  let selected ← (RuntimeTransformOwners.inputs event).mapM (RuntimeOwnerMap.byOwner incoming)
  let returned := returnedBindings (RuntimeTransformOwners.outputs event) ports
  let spectators := RuntimeSelectionPartition.complement incoming selected
  let roles := event.held ++ RuntimeTransformOwners.outputs event ++
    SourceTypes.SourceRuntimeValues.owners event.remaining
  let outgoing ← roles.mapM (RuntimeOwnerMap.byOwner (returned++spectators))
  let operator := applySourceBlock incoming outgoing selected returned spectators logical source.operator
  return [{source with owners := ⟨outgoing,source.owners.issued ++ event.allocated,event.afterOrdinal⟩, operator}]

/-- The exact written transform equation lifts to the caller's full
operator and leaves its ordinary SSA and measurement history in place. -/
theorem original_transform_history {dependencies program block artifact caller}
    {event : SourceTypes.SourceRuntimeContext.TransformEvent artifact.sources caller}
    {position request before} {interval : @RuntimeInterval.Checked dependencies program block position.start position.count}
    (sourceRequest : RuntimeTransformRequest.Checked event position request)
    (original : RuntimeInterval.Computed (RuntimeTransformRequest.read event position request) sourceRequest)
    (forward : RuntimeTransformAction.Forward artifact dependencies sourceRequest)
    {forwardReturned : Map} (logical : RuntimeTransformAction.ForwardMap forward forwardReturned)
    (held : RuntimeTransformOwners.Checked interval event before)
    (transform : RuntimeTransformAction.Checked held logical.code.logical)
    (children : RuntimePureBody.Nodes dependencies forward.program forward.prepared.block)
    (inputs : List Nat) (inherited : Option (Nat → Prop)) {ordinary : RuntimeOrdinaryBody.State}
    {source : SourceHistory} {actual : Qleisli.Semantics.ObservingAction.History}
    (agrees : SemanticHistoryAgreesWithInherited inherited inputs held.literal.interval.before before ordinary source actual)
    {events results}
    (read : Semantics.Observation.readOps block.fuel held.literal.interval.before.quantum.reference
      ((block.operations.drop position.start).take position.count) =
        some (held.literal.interval.after.quantum.reference,events))
    (executed : Qleisli.Semantics.ObservingAction.run dependencies block.fuel events actual = some results) :
    ∃ expected, sourceTransformHistory event held.literal.returned transform.original source = some expected ∧
      List.Forall₂ (SemanticHistoryAgreesWithInherited inherited inputs held.literal.interval.after held.after ordinary)
        expected results := by
  have originalAgreement := agrees
  obtain ⟨sourceOwners,_,_,_,_,incoming,initial,input,represented⟩ := agrees
  let returned := RuntimeTransformOwners.assigned event held.returned
  let spectators := RuntimeSelectionPartition.complement held.inputFrame.bindings held.selected
  obtain ⟨beforeOrder,afterOrder,ports⟩ := transform_partitions held
  have inputOrder : incoming.bindings = held.inputFrame.bindings := initial.trans held.sameInput.symm
  let sameExit := RuntimeIntervalStates.same_after interval held.literal.interval
  let outgoing := Qleisli.RuntimeNamedThreeFrameChain.checkedAt sameExit held.afterFrame
  have outputOrder : outgoing.bindings = held.afterFrame.bindings :=
    Qleisli.RuntimeNamedThreeFrameChain.checkedAt_bindings sameExit held.afterFrame
  have beforeOrder : (held.selected++spectators).Perm incoming.bindings := inputOrder.symm ▸ beforeOrder
  have afterOrder : (returned++spectators).Perm outgoing.bindings := outputOrder.symm ▸ afterOrder
  have lifted := operation_code_lift incoming outgoing (initial.symm ▸ input)
    beforeOrder afterOrder transform.inputRead transform.outputRead transform.code transform.equation
  obtain ⟨available,outputCode⟩ := original_block_code transform.outputRead
  obtain ⟨returnOrder,valid⟩ := Qleisli.RuntimeCallHistory.fragment_return_ports held.literal
  have wires := ((returnOrder.flatMap_right Semantics.Raw.Port.wires).trans
    (RuntimeCallTraceFrames.native_wires _ valid)).length_eq
  rw [← ports,List.flatMap_map] at wires
  have rows : transform.actual.rows = 2^held.literal.pureBody.state.frame.length := by
    rw [transform.code.physicalShape.2,outputCode]
    change 2^(Qleisli.RuntimeSemanticForest.product returned).bits = _
    rw [Qleisli.RuntimeSparseBlockEncoding.product_width available,wires]
  let node : RuntimePureBody.Node dependencies program block :=
    .transform sourceRequest original forward forwardReturned logical held transform children
  let operator := applySourceBlock incoming.bindings outgoing.bindings
    held.selected returned spectators transform.original source.operator
  have refined := pure_step_history_lift node inputs inherited outgoing
    (after := held.after) outputOrder source actual operator originalAgreement read executed
    (fragment_represents held.literal.toLiteral rfl incoming outgoing (initial.symm ▸ input)
      beforeOrder held.selectedPorts ports.symm transform.actualRead rows lifted source.operator actual
      (cast_represents initial.symm input represented))
  have chosen := Qleisli.RuntimeLiteralHistory.order_source held.selectedRead
  have returnedBindingsEq : returnedBindings (RuntimeTransformOwners.outputs event) held.literal.returned = returned := by
    rw [held.returnedPorts]
    simp only [returnedBindings,returned,RuntimeTransformOwners.assigned,List.zip_map_right,List.map_map,Function.comp_def]
    rfl
  have rebuilt := ordered_lookup outgoing _ afterOrder
  rw [outputOrder,held.afterFrame.ordered] at rebuilt
  have originalSpectators : RuntimeSelectionPartition.complement before.bindings held.selected = spectators := by
    simp only [spectators,held.sameInput]
  let originalOperator := applySourceBlock before.bindings held.afterFrame.bindings
    held.selected returned spectators transform.original source.operator
  refine ⟨[{source with owners := held.after, operator := originalOperator}],?_,?_⟩
  · simp only [sourceTransformHistory,sourceOwners,chosen,bind,Option.bind,pure,returnedBindingsEq,
      originalSpectators,rebuilt,originalOperator,RuntimeTransformOwners.Checked.after]
  · simpa only [node,Qleisli.RuntimeLiteralBody.nodeSpan,operator,initial,outputOrder,originalOperator] using refined

#print axioms original_transform_history

private theorem primitive_owner_order {dependencies program block start count input output role kind}
    {primitive : @RuntimePrimitiveAction.Checked dependencies program block start count input output role kind}
    (original : RuntimePrimitiveSource.Checked primitive) :
    OperationOwnerOrder primitive.interval original.history original.after := by
  refine ⟨rfl,⟨[original.inputPort.port],[original.outputPort.port],?_,original.outputPort.original,?_,?_⟩,
    original.interval,original.frame,original.owners,original.sameHistory,rfl,original.ownerRead⟩
  · simpa only [← original.sameHistory] using original.inputPort.original
  · exact congrArg List.singleton original.inputToken
  · exact congrArg List.singleton original.outputToken

private theorem singleton_ports {state token ports}
    (read : PureInterval.ports state [token] = some ports) : ∃ port, ports = [port] := by
  unfold PureInterval.ports PureInterval.portsOf at read
  simp only [List.mapM_cons,List.mapM_nil] at read
  cases found : state.quantum.live.find? (fun port => port.token == token) <;> simp_all
  exact ⟨_,read.symm⟩

/-- The source kind and basis determine the matrix before any literal Raw
operation is evaluated. The primitive and graph proofs share the same lift. -/
noncomputable def sourcePrimitiveHistory {dependencies program block start count input output role kind}
    (primitive : @RuntimePrimitiveAction.Checked dependencies program block start count input output role kind)
    (source : SourceHistory) : Option (List SourceHistory) := do
  let logical ← Semantics.PrimitiveOperator.meaning kind role.basis
  sourceGraphHistory [role] primitive.interval.returned logical source

/-- Lift the independently specified primitive over its entire checked
interval. The exact local code equation handles every admitted lowering. -/
theorem original_primitive_history {dependencies program block start count input output role kind}
    (primitive : @RuntimePrimitiveAction.Checked dependencies program block start count input output role kind)
    (original : RuntimePrimitiveSource.Checked primitive)
    (rootInputs : List Nat) (inherited : Option (Nat → Prop))
    {ordinary : RuntimeOrdinaryBody.State} {source : SourceHistory}
    {actual : Qleisli.Semantics.ObservingAction.History}
    (agrees : SemanticHistoryAgreesWithInherited inherited rootInputs primitive.interval.interval.before
      original.history ordinary source actual)
    {events results}
    (read : Semantics.Observation.readOps block.fuel primitive.interval.interval.before.quantum.reference
      ((block.operations.drop start).take count) = some (primitive.interval.interval.after.quantum.reference,events))
    (executed : Qleisli.Semantics.ObservingAction.run dependencies block.fuel events actual = some results) :
    ∃ expected, sourcePrimitiveHistory primitive source = some expected ∧
      List.Forall₂ (SemanticHistoryAgreesWithInherited inherited rootInputs primitive.interval.interval.after
        original.after ordinary) expected results := by
  obtain ⟨_,entry⟩ := singleton_ports primitive.interval.atEntry
  obtain ⟨_,exit⟩ := singleton_ports primitive.interval.atExit
  have inputRead : RuntimeInterval.Computed (Carrier.ownerCode
      ((primitive.interval.selected.zip [role]).map fun (port,owner) => ⟨port,owner.basis⟩))
      primitive.inputCode := by
    simpa only [entry] using primitive.inputRead
  have outputRead : RuntimeInterval.Computed (Carrier.ownerCode
      ((primitive.interval.returned.zip [role]).map fun (port,owner) => ⟨port,owner.basis⟩))
      primitive.outputCode := by
    simpa only [exit] using primitive.outputRead
  obtain ⟨expected,sourceRead,paired⟩ := original_graph_history primitive.interval inputRead outputRead
    primitive.physicalRead primitive.action primitive.equation (primitive_owner_order original)
    rootInputs inherited agrees read executed
  exact ⟨expected,by simpa only [sourcePrimitiveHistory,primitive.reference,bind,Option.bind] using sourceRead,paired⟩

def NeedsNonPrimitive {dependencies program block} : @RuntimePureBody.Step dependencies program block → Prop
  | .pure (.primitive ..) => False
  | _ => True

noncomputable def withPrimitive {dependencies program block}
    (fallback : List (@RuntimePureBody.Step dependencies program block) → RuntimePureBody.Step dependencies program block →
      SourceHistory → Option (List SourceHistory))
    (prior : List (@RuntimePureBody.Step dependencies program block)) (step : RuntimePureBody.Step dependencies program block)
    (source : SourceHistory) : Option (List SourceHistory) :=
  match step with
  | .pure (.primitive primitive _) => sourcePrimitiveHistory primitive source
  | _ => fallback prior step source

/-- The shared history induction uses the primitive's exact matrix law for
any checked interval, including one with multiple literal operations. -/
theorem sourceStep_with_primitive {dependencies program block}
    (steps : List (@RuntimePureBody.Step dependencies program block)) (inputs : List Nat) (inherited : Option (Nat → Prop))
    (certifies : RuntimePureBody.Step dependencies program block → Prop)
    (fallback : List (@RuntimePureBody.Step dependencies program block) → RuntimePureBody.Step dependencies program block →
      SourceHistory → Option (List SourceHistory))
    (remaining : StepRefinement steps (fun step => certifies step ∧ NeedsNonPrimitive step)
      fallback (fun _ => SemanticHistoryAgreesWithInherited inherited inputs)
      (inherited.map (fun holds id => ¬ holds id))) :
    StepRefinement steps certifies (withPrimitive fallback) (fun _ => SemanticHistoryAgreesWithInherited inherited inputs)
      (inherited.map (fun holds id => ¬ holds id)) := by
  intro prior first later position certified ownerBefore ownerAfter ordinaryBefore ordinaryAfter
    owners ordinary chunk read
  refine WithChunkWriteBound.of_trace ?_
  intro writes source history outputs agrees executed
  cases first
  case pure node =>
    cases node
    case primitive action original =>
      change ownerBefore = original.history ∧ ownerAfter = original.after at owners
      rcases owners with ⟨rfl,rfl⟩
      cases ordinary
      exact original_primitive_history action original inputs inherited agrees read executed
    all_goals
      exact ((remaining prior _ later position ⟨certified,trivial⟩ owners ordinary read).apply writes) agrees executed
  all_goals
    exact ((remaining prior _ later position ⟨certified,trivial⟩ owners ordinary read).apply writes) agrees executed

#print axioms original_primitive_history
#print axioms sourceStep_with_primitive

def NeedsNonGraph {dependencies program block} : @RuntimePureBody.Step dependencies program block → Prop
  | .pure (.operation ..) | .pure (.rectangularOperation _) | .pure (.transform ..) | .pure (.workspace ..) => False
  | _ => True

private noncomputable def workspaceHistory {sources caller dependencies program block start count event children
    original interval before literal}
    (map : @RuntimeWorkspace.CallerMap sources caller dependencies program block start count event children
      original interval before literal) (source : SourceHistory) : List SourceHistory :=
  [{source with
    owners := literal.continuation
    operator := applySourceBlock literal.frame.bindings literal.after.bindings map.selected map.returned
      map.spectators map.logical source.operator}]

/-- The checked local workspace map extends to the actual caller frame,
including inherited outcomes and reference amplitudes. -/
theorem original_workspace_history {sources caller dependencies program block start count before}
    {event : SourceTypes.SourceRuntimeContext.WorkspaceEvent sources caller} {children}
    {interval : @RuntimeInterval.Checked dependencies program block start count}
    (location : RuntimeSourceEvent.Location (.workspace event children) start count)
    (original : RuntimeWorkspace.Original event children) (literal : RuntimeWorkspace.Literal original interval before)
    (map : RuntimeWorkspace.CallerMap literal)
    (inputs : List Nat) (inherited : Option (Nat → Prop)) {ordinary : RuntimeOrdinaryBody.State}
    {source : SourceHistory} {actual : Qleisli.Semantics.ObservingAction.History}
    (agrees : SemanticHistoryAgreesWithInherited inherited inputs interval.before before ordinary source actual)
    {events results}
    (read : Semantics.Observation.readOps block.fuel interval.before.quantum.reference
      ((block.operations.drop start).take count) = some (interval.after.quantum.reference,events))
    (executed : Qleisli.Semantics.ObservingAction.run dependencies block.fuel events actual = some results) :
    List.Forall₂ (SemanticHistoryAgreesWithInherited inherited inputs interval.after literal.continuation ordinary)
      (workspaceHistory map source) results := by
  have originalAgreement := agrees
  obtain ⟨_,_,_,_,_,_,_,input,represented⟩ := agrees
  have incomingOrder : before.bindings = literal.frame.bindings := literal.sameFrame.symm
  let node : RuntimePureBody.Node dependencies program block := .workspace interval location original literal map
  let operator := applySourceBlock literal.frame.bindings literal.after.bindings map.selected map.returned
    map.spectators map.logical source.operator
  apply pure_step_history_lift node inputs inherited literal.after literal.afterBindings source actual operator
    originalAgreement read executed
  intro operations rawEvents ops trace
  obtain ⟨available,code⟩ := original_block_code map.outputRead
  obtain ⟨returnOrder,valid⟩ := Qleisli.RuntimeCallHistory.literal_return_ports map.native
  have wires := ((returnOrder.flatMap_right Semantics.Raw.Port.wires).trans
    (RuntimeCallTraceFrames.native_wires _ valid)).length_eq
  rw [map.returnPorts,List.flatMap_map] at wires
  have rows : map.physical.rows = 2^map.native.pureBody.state.frame.length := by
    rw [map.action.physicalShape.2,code]
    change 2^(Qleisli.RuntimeSemanticForest.product map.returned).bits = _
    rw [Qleisli.RuntimeSparseBlockEncoding.product_width available,wires]
  have encoded := cast_represents incomingOrder input represented
  let originalInput := incomingOrder ▸ input
  have lifted := operation_code_lift literal.frame literal.after originalInput map.inputPartition
    map.outputPartition map.inputRead map.outputRead map.action map.equation
  exact fragment_represents map.native map.nativeInterval _ _ originalInput map.inputPartition map.entryPorts map.returnPorts
    map.physicalRead rows lifted source.operator actual encoded operations rawEvents ops trace

noncomputable def withGraph {dependencies program block}
    (fallback : List (@RuntimePureBody.Step dependencies program block) → RuntimePureBody.Step dependencies program block →
      SourceHistory → Option (List SourceHistory))
    (prior : List (@RuntimePureBody.Step dependencies program block)) (step : RuntimePureBody.Step dependencies program block)
    (source : SourceHistory) : Option (List SourceHistory) :=
  match step with
  | .pure (.operation (roles := roles) frame _ _ _ logical ..) => sourceGraphHistory roles frame.returned logical source
  | .pure (.rectangularOperation (expected := expected) checked) =>
    sourceRectangularHistory checked.source.input checked.source.output checked.returned expected source
  | .pure (.transform (event := event) _ _ _ _ _ held transform _) =>
    sourceTransformHistory event held.literal.returned transform.original source
  | .pure (.workspace _ _ _ _ map) => some (workspaceHistory map source)
  | _ => fallback prior step source

/-- In planned execution this evaluator uses the source occurrence's
ordered roles and the independently consumed action of that same graph. -/
theorem withGraph_staged {artifact root}
    {preparation : RuntimeGraphOperation.Preparation artifact}
    {continuation : RuntimeGraphOperation.StagedConsumption preparation root (RuntimePureBody.Island root.dependencies)}
    {program block} (node : RuntimePureBody.Node root.dependencies program block)
    (authentic : Qleisli.RuntimeNamedChildRuns.OperationOrigin (.planned preparation continuation) node)
    (fallback : List (@RuntimePureBody.Step root.dependencies program block) → RuntimePureBody.Step root.dependencies program block →
      SourceHistory → Option (List SourceHistory))
    (prior : List (@RuntimePureBody.Step root.dependencies program block)) (source : SourceHistory) :
    match node with
    | original@(.operation frame ..) =>
      ∃ (owner : String) (event : SourceTypes.SourceOperationApplication.Event artifact.sources owner)
        (receipt : RuntimeGraphOperation.StagedReceipt continuation),
        HEq receipt.request.graph event.operation.graph ∧
        withGraph fallback prior (.pure original) source =
          sourceGraphHistory event.inputOwners frame.returned (continuation.action receipt.evidence) source
    | original@(.rectangularOperation (event := retained) checked) =>
      ∃ (owner : String) (event : SourceTypes.SourceOperationApplication.Event artifact.sources owner)
        (receipt : RuntimeGraphOperation.StagedReceipt continuation),
        HEq event retained ∧ HEq receipt.request.graph event.operation.graph ∧
        withGraph fallback prior (.pure original) source =
          sourceRectangularHistory checked.source.input checked.source.output checked.returned
            (continuation.action receipt.evidence) source
    | _ => True := by
  have staged := authentic.staged_action
  cases node
  case operation =>
    obtain ⟨owner,event,receipt,roles,graph,logical⟩ := staged
    exact ⟨owner,event,receipt,graph,by simp only [withGraph,roles,logical]⟩
  case rectangularOperation =>
    obtain ⟨owner,event,receipt,original,graph,logical⟩ := staged
    exact ⟨owner,event,receipt,original,graph,by simp only [withGraph,logical]⟩
  all_goals exact True.intro

/-- The original graph branch supplies its own ordered history law in the
common execution induction, including an inherited ordinary scope. -/
theorem sourceStep_with_graph {dependencies program block}
    (steps : List (@RuntimePureBody.Step dependencies program block)) (inputs : List Nat) (inherited : Option (Nat → Prop))
    (certifies : RuntimePureBody.Step dependencies program block → Prop)
    (fallback : List (@RuntimePureBody.Step dependencies program block) → RuntimePureBody.Step dependencies program block →
      SourceHistory → Option (List SourceHistory))
    (remaining : StepRefinement steps (fun step => certifies step ∧ NeedsNonGraph step)
      fallback (fun _ => SemanticHistoryAgreesWithInherited inherited inputs)
      (inherited.map (fun holds id => ¬ holds id))) :
    StepRefinement steps certifies (withGraph fallback) (fun _ => SemanticHistoryAgreesWithInherited inherited inputs)
      (inherited.map (fun holds id => ¬ holds id)) := by
  intro prior first later position certified ownerBefore ownerAfter ordinaryBefore ordinaryAfter
    owners ordinary chunk read
  refine WithChunkWriteBound.of_trace ?_
  intro writes source history outputs agrees executed
  cases first
  case pure node =>
    cases node
    case operation =>
      rename_i inputCode outputCode physical logical checked equation frame inputRead outputRead physicalRead
      cases ordinary
      exact original_graph_history frame inputRead outputRead physicalRead checked equation owners
        inputs inherited agrees read executed
    case rectangularOperation checked =>
      rcases owners with ⟨rfl,rfl⟩
      cases ordinary
      exact original_rectangular_history checked inputs inherited agrees read executed
    case workspace =>
      rename_i position original literal map
      rcases owners with ⟨rfl,rfl⟩
      cases ordinary
      exact ⟨_,rfl,original_workspace_history (by assumption) original literal map inputs inherited agrees read executed⟩
    case transform =>
      rename_i sourceRequest original forward forwardReturned logical children interval held transform
      change ownerBefore = _ ∧ ownerAfter = held.after at owners
      rcases owners with ⟨rfl,rfl⟩
      cases ordinary
      exact original_transform_history sourceRequest original forward logical held transform children
        inputs inherited agrees read executed
    all_goals
      exact ((remaining prior _ later position ⟨certified,trivial⟩ owners ordinary read).apply writes) agrees executed
  all_goals
    exact ((remaining prior _ later position ⟨certified,trivial⟩ owners ordinary read).apply writes) agrees executed

#print axioms sourceStep_with_graph
end Qleisli.RuntimeOriginalGraphAction
