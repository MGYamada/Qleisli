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

private theorem fragment_action {dependencies program block arity start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block arity start count inputs outputs roles)
    {physical : Matrix}
    (read : RuntimeInterval.Computed (Raw.ProtectedEvaluation.reconstruct dependencies
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) physical)
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
  have live := incoming.complete.symm.trans (beforeOrder.symm.map Binding.port)
  rw [List.map_append,← selectedPorts] at live
  obtain ⟨entry,parentEvents,childEvents,entryRef,parentTrace,childTrace,exitWires,_,bounded,paired⟩ :=
    Qleisli.RuntimeCallHistory.pure_interval_events frame (spectators.map Binding.port) live
  have entryWires : entry.reference.frame = WireOrder (selected.map Binding.port) := by
    rw [entryRef,selectedPorts]
  rw [returnedPorts] at exitWires
  have localMatrix {Reference : Type} (joint : Nat → Reference → ℂ) row reference
      (bound : row < 2^frame.pureBody.state.frame.length) :
      Qleisli.Semantics.RawAction.events dependencies childEvents (fun col => joint col reference) row =
        action physical joint (project frame.pureBody.state.reference (WireOrder (returned.map Binding.port)) row) reference := by
    simpa only [returnedPorts] using fragment_action frame physicalRead rows entryRef childTrace joint row reference bound
  obtain ⟨output,representedAfter⟩ := operation_events_lift incoming outgoing (initial.symm ▸ input)
    lifted entryWires exitWires bounded paired localMatrix source.operator actual
    (cast_represents initial.symm input represented)
  let node : RuntimePureBody.Node dependencies program block :=
    .operation frame inputCode outputCode physical logical inputRead outputRead physicalRead checked equation
  let operator := applySourceBlock incoming.bindings outgoing.bindings selected returned spectators logical source.operator
  have refined := pure_step_history_lift node rootInputs inherited outgoing outgoingOrder source actual operator
    originalAgreement read executed (by
      intro operations emitted literal traced
      have sameOps : frame.operations = operations :=
        (List.map_inj_right (f := Semantics.Observation.Op.pure)
          (fun _ _ same => Semantics.Observation.Op.pure.inj same)).mp (frame.literal.symm.trans literal)
      subst operations
      have sameEvents : emitted = parentEvents :=
        congrArg Semantics.RawTrace.Prepared.events (Option.some.inj (traced.symm.trans parentTrace))
      subst emitted
      exact ⟨output,representedAfter⟩)
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
  | .pure (.operation ..) => False
  | _ => True

noncomputable def withGraph {dependencies program block}
    (fallback : List (@RuntimePureBody.Step dependencies program block) → RuntimePureBody.Step dependencies program block →
      SourceHistory → Option (List SourceHistory))
    (prior : List (@RuntimePureBody.Step dependencies program block)) (step : RuntimePureBody.Step dependencies program block)
    (source : SourceHistory) : Option (List SourceHistory) :=
  match step with
  | .pure (.operation (roles := roles) frame _ _ _ logical ..) => sourceGraphHistory roles frame.returned logical source
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
    | _ => True := by
  have staged := authentic.staged_action
  cases node
  case operation =>
    obtain ⟨owner,event,receipt,roles,graph,logical⟩ := staged
    exact ⟨owner,event,receipt,graph,by simp only [withGraph,roles,logical]⟩
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
    all_goals
      exact ((remaining prior _ later position ⟨certified,trivial⟩ owners ordinary read).apply writes) agrees executed
  all_goals
    exact ((remaining prior _ later position ⟨certified,trivial⟩ owners ordinary read).apply writes) agrees executed

#print axioms sourceStep_with_graph
end Qleisli.RuntimeOriginalGraphAction
