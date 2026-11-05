import Qleisli.RuntimeIntervalStates
import Qleisli.RuntimeNamedPrimitiveInputs
import Qleisli.RuntimeNamedCodeTransport
import Qleisli.RuntimeOwnerBindingFacts
import QleisliKernel.Qirf.RuntimeNamedReturnAxes

/-! Derive native output carriers and code reads from the actual original
named primitive run, source return order and caller owner map. These are
source/code links, not whole-function logical-action or history composition.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeNamedPrimitiveOutputs
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite
open RuntimePureBody

/-- Keep the complete original owner/port association from the real lookup. -/
theorem port_binding {role bindings} (selected : RuntimePrimitiveSource.PortAt role bindings) :
    ∃ binding ∈ bindings, binding.owner = role ∧ binding.port = selected.port := by
  obtain ⟨work,left,ran⟩ := selected.original
  unfold RuntimePrimitiveSource.rolePorts at ran
  obtain ⟨ordered,middle,orderRead,returned⟩ := bind_success _ _ _ _ _ ran
  have facts := RuntimeSelectionPartition.order_values bindings [role] ordered
    ⟨work,middle,orderRead⟩
  have member : selected.port ∈ ordered.map RuntimeOwnerMap.Binding.port := by
    rw [← (pure_success _ _ _ _ returned).1]
    exact List.mem_cons_self
  obtain ⟨binding,present,same⟩ := List.mem_map.mp member
  have ownerMember := List.mem_map (f := RuntimeOwnerMap.Binding.owner).mpr ⟨binding,present,rfl⟩
  rw [facts.2] at ownerMember
  exact ⟨binding,facts.1 present,List.mem_singleton.mp ownerMember,same⟩

/-- The original owner lookup selects a full port in the actual complete frame. -/
theorem port_live {roles state role} (frame : RuntimeOwnerMap.Checked roles state)
    (selected : RuntimePrimitiveSource.PortAt role frame.bindings) :
    selected.port ∈ state.quantum.live := by
  obtain ⟨binding,present,_owner,same⟩ := port_binding selected
  exact frame.complete.mem_iff.mp (List.mem_map.mpr ⟨binding,present,same⟩)

/-- Original source and native output reads refer to the same full port, not
only its width. Their independently retained successful interval states are
proved identical; no caller-supplied state equality is a premise. -/
theorem primitive_output_port {dependencies program block start count input output role kind}
    {action : @RuntimePrimitiveAction.Checked dependencies program block start count input output role kind}
    (binding : RuntimePrimitiveSource.Checked action) :
    action.interval.returned = [binding.outputPort.port] := by
  have states := RuntimeIntervalStates.same_after binding.interval action.interval.interval
  have live := port_live binding.owners.after binding.outputPort
  have native := action.interval.atExit
  rw [← states] at native
  change PureInterval.portsOf binding.interval.after.quantum.live [output] =
    some action.interval.returned at native
  cases found : binding.interval.after.quantum.live.find? (fun p => p.token == output) with
  | none => simp [PureInterval.portsOf,List.mapM_cons,found] at native
  | some port =>
    have returned : action.interval.returned = [port] := by
      simpa [PureInterval.portsOf,List.mapM_cons,found] using native.symm
    have distinct : (binding.interval.after.quantum.live.map (·.token)).Nodup := by
      apply (binding.owners.after.complete.map (·.token)).nodup_iff.mp
      simpa only [List.map_map,Function.comp_def] using binding.owners.after.tokensDistinct
    have same : port = binding.outputPort.port :=
      RuntimeOwnerTransitionAction.map_unique (fun p : Semantics.Raw.Port => p.token) _ distinct
        port (List.mem_of_find?_eq_some found) binding.outputPort.port live
        ((beq_iff_eq.mp (List.find?_some (p := fun p : Semantics.Raw.Port => p.token == output) found)).trans binding.outputToken.symm)
    rw [returned,same]

/-- A true singleton original frame retains the primitive's complete output
carrier. This uses source identities and the real after-map order, rather than
inferring a nominal basis from the physical width. -/
theorem primitive_after_carriers {dependencies program block start count input output role kind}
    {action : @RuntimePrimitiveAction.Checked dependencies program block start count input output role kind}
    (binding : RuntimePrimitiveSource.Checked action)
    (single : (RuntimeForestCode.carrierOwners binding.history.bindings).length = 1) :
    RuntimeForestCode.carrierOwners binding.after.bindings =
      action.interval.returned.map (fun port => (⟨port,role.basis⟩ : Semantics.CarrierInterface.Owner)) := by
  have oldLength : binding.frame.bindings.length = 1 := by
    rw [binding.sameHistory]
    simpa only [RuntimeForestCode.carrierOwners,List.length_map] using single
  have afterLength : binding.owners.after.bindings.length = 1 := by
    have lengths := congrArg List.length binding.owners.after.ordered
    simpa only [List.length_map,oldLength] using lengths
  obtain ⟨entry,entries⟩ := List.length_eq_one_iff.mp afterLength
  obtain ⟨selected,present,sameOwner,samePort⟩ := port_binding binding.outputPort
  rw [entries] at present
  have sameEntry := List.mem_singleton.mp present
  subst selected
  change RuntimeForestCode.carrierOwners binding.owners.after.bindings = _
  rw [entries,primitive_output_port binding,← samePort]
  simp only [RuntimeForestCode.carrierOwners,List.map_cons,List.map_nil,sameOwner]

/-- The real checked return reorder keeps original bindings. -/
theorem reordered_subset {roles state bindings result}
    (checked : RuntimeInterval.Computed (reordered roles state bindings) result) :
    result.bindings ⊆ bindings := by
  obtain ⟨work,left,ran⟩ := checked
  unfold reordered at ran
  obtain ⟨ordered,middle,read,rest⟩ := bind_success _ _ _ _ _ ran
  unfold RuntimeOwnerMap.check at rest
  obtain ⟨certificate,budget,_checked,returned⟩ := bind_success _ _ _ _ _ rest
  have same : result = certificate.val := (pure_success _ _ _ _ returned).1
  subst result
  rw [certificate.property]
  exact (RuntimeSelectionPartition.order_values bindings roles ordered ⟨work,middle,read⟩).1

theorem returned_subset {dependencies program block roles before after}
    (returned : @RuntimeNamedSourceFlow.Returned dependencies program block roles before after) :
    after.bindings ⊆ before.bindings := by
  obtain ⟨native,_nativeRead,owners,read,same⟩ := returned
  rw [same]
  exact reordered_subset read

/-- A real one-primitive run followed by its actual original return has the
native complete output carrier when both retained source interfaces are single
owners. The singleton premises will come from the original named occurrence. -/
theorem returned_single_carriers {dependencies program block start count input output role kind}
    {action : @RuntimePrimitiveAction.Checked dependencies program block start count input output role kind}
    (binding : RuntimePrimitiveSource.Checked action) {initial last result roles}
    (flow : RuntimeNamedSourceFlow.Run initial [.pure (.primitive action binding)] last)
    (returned : RuntimeNamedSourceFlow.Returned block roles last result)
    (singleInput : (RuntimeForestCode.carrierOwners binding.history.bindings).length = 1)
    (singleResult : result.bindings.length = 1) :
    RuntimeForestCode.carrierOwners result.bindings =
      action.interval.returned.map (fun port => (⟨port,role.basis⟩ : Semantics.CarrierInterface.Owner)) := by
  have final : last = binding.after := by
    cases flow with
    | cons first rest => cases rest; exact first.2
  have subset := returned_subset returned
  rw [final] at subset
  have carriers := primitive_after_carriers binding singleInput
  have afterLength : binding.after.bindings.length = 1 := by
    have sizes := congrArg List.length carriers
    simpa only [RuntimeForestCode.carrierOwners,List.length_map,
      primitive_output_port binding,List.length_singleton] using sizes
  obtain ⟨entry,entries⟩ := List.length_eq_one_iff.mp afterLength
  obtain ⟨selected,selection⟩ := List.length_eq_one_iff.mp singleResult
  have present : selected ∈ result.bindings := by rw [selection]; exact List.mem_cons_self
  have same : selected = entry := by
    have member := subset present
    rw [entries] at member
    exact List.mem_singleton.mp member
  have maps : result.bindings = binding.after.bindings := by rw [selection,entries,same]
  rw [maps]
  exact carriers

def ReturnCounts {dependencies program block} (step : Step dependencies program block) : Prop :=
  match step with
  | .named (childHistory := child) _ _ _ _ boundary _ _ =>
    boundary.input.ordered.length = 1 ∧ child.bindings.length = 1
  | _ => True

theorem occurrence_counts {dependencies program block step}
    (held : @RuntimeNamedPrimitiveOccurrence.Occurrence dependencies program block step) :
    ReturnCounts step := by
  cases held with
  | @named start count inputs sources caller before childHistory childRetired ordinary first size input output role kind
      event scope body read boundary finalOrdinary action original bound =>
    refine ⟨by rw [bound.singleton]; rfl,?_⟩
    have lengths := (RuntimeNamedReturnAxes.mixed_ports scope boundary).length_eq
    rw [(RuntimeNamedReturnAxes.source_order boundary).1,List.length_map] at lengths
    have outputLength := congrArg List.length bound.outputs
    simp only [List.length_map,List.length_singleton] at outputLength
    exact lengths.trans outputLength

def NamedPrimitiveOutput {dependencies program block} (step : Step dependencies program block) : Prop :=
  match step with
  | .named (childHistory := child) _ _ _ _ _ _ (.cons (.pure (.primitive (role := role) action _)) .nil) =>
    RuntimeForestCode.carrierOwners child.bindings =
      action.interval.returned.map (fun port => (⟨port,role.basis⟩ : Semantics.CarrierInterface.Owner))
  | _ => True

/-- Both complete singleton interfaces are derived from the original named
occurrence. The real child callback and final reorder connect its native output
carrier to the original returned child history. -/
theorem actual_named_output {artifact root execution fuel program block step}
    (call : @RuntimeNamedChildRuns.ChildRun artifact root execution
      (runBlockCore artifact root execution (fuel+1)) program block step)
    (counts : ReturnCounts step) : NamedPrimitiveOutput step := by
  have inputs := RuntimeNamedPrimitiveInputs.actual_named_input call
  cases call with
  | @named start count inputTokens caller before ordinary event scope body bodyRead
      rootOwner rootName path request plan assigned result receipts boundary beforeInput afterInput afterChild inputRead childRead =>
    change boundary.input.ordered.length = 1 ∧ result.history.bindings.length = 1 at counts
    cases emitted : result.steps with
    | nil => trivial
    | cons first rest =>
      cases rest with
      | cons second rest =>
        cases first
        case pure node => cases node <;> trivial
        all_goals trivial
      | nil =>
        cases first
        case pure node =>
          cases node
          case primitive action binding =>
            have sameInput : RuntimeForestCode.carrierOwners binding.history.bindings =
                RuntimeForestCode.carrierOwners boundary.input.ordered := by
              simpa only [RuntimeNamedPrimitiveInputs.NamedPrimitiveInput,emitted,Steps.ofList,
                List.foldr_cons,List.foldr_nil] using inputs
            have singleInput : (RuntimeForestCode.carrierOwners binding.history.bindings).length = 1 := by
              rw [sameInput]
              simpa only [RuntimeForestCode.carrierOwners,List.length_map] using counts.1
            obtain ⟨ordered,_orderedRead,last,flow,returned⟩ :=
              RuntimeNamedChildRuns.core_flow artifact root execution fuel .localScope (.whole body) path
                scope.program request plan ⟨assigned,_,_⟩ scope.visible.ssa scope.prepared.block
                (result,receipts) ⟨afterInput,afterChild,childRead⟩
            rw [emitted] at flow
            simpa only [NamedPrimitiveOutput,Steps.ofList,List.foldr_cons,List.foldr_nil] using
              returned_single_carriers binding flow.source returned singleInput counts.2
          all_goals trivial
        all_goals trivial

def OccurrenceOutput {dependencies program block step}
    (held : @RuntimeNamedPrimitiveOccurrence.Occurrence dependencies program block step) : Prop :=
  match held with
  | .named (role := role) (boundary := boundary) (action := action) _ _ =>
    RuntimeForestCode.carrierOwners boundary.mapped =
      action.interval.returned.map (fun port => (⟨port,role.basis⟩ : Semantics.CarrierInterface.Owner))

/-- The actual original caller mapping preserves the child return's full basis
and port, so the real native output read is attached to these caller carriers. -/
theorem actual_occurrence_output {artifact root execution fuel program block step}
    (held : @RuntimeNamedPrimitiveOccurrence.Occurrence root.dependencies program block step)
    (call : RuntimeNamedChildRuns.ChildRun artifact root execution
      (runBlockCore artifact root execution (fuel+1)) step) : OccurrenceOutput held := by
  have output := actual_named_output call (occurrence_counts held)
  cases held with
  | @named start count inputs sources caller before childHistory childRetired ordinary first size inputToken outputToken role kind
      event scope body read boundary finalOrdinary action original bound =>
    exact (RuntimeNamedCodeTransport.returned_carriers boundary).trans output

/-- Both original primitive callees in pre/choose/post supply their authentic
native output carriers, derived from actual recursion and source return order. -/
theorem original_pre_post_outputs {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime)
    (view : RuntimeNamedThreeOccurrence.Three body.checked.result.steps) :
    OccurrenceOutput view.prePrimitive ∧ OccurrenceOutput view.postPrimitive := by
  obtain ⟨pre,_center,post⟩ := RuntimeNamedSourceFlow.original_child_runs body view
  exact ⟨actual_occurrence_output view.prePrimitive pre,actual_occurrence_output view.postPrimitive post⟩

def OccurrenceOutputCode {dependencies program block step}
    (held : @RuntimeNamedPrimitiveOccurrence.Occurrence dependencies program block step) : Prop :=
  match held with
  | .named (boundary := boundary) (action := action) _ _ =>
    ∃ target : RuntimeOwnerMap.Binding, boundary.mapped = [target] ∧
      target ∈ boundary.afterFrame.bindings ∧
      RuntimeInterval.Computed (Carrier.ownerCode [⟨target.port,target.owner.basis⟩]) action.outputCode

/-- Retain the SAME native output-code computation on the original mapped
caller binding; no rerun, extra budget, width equality or encoding premise. -/
theorem actual_occurrence_output_code {artifact root execution fuel program block step}
    (held : @RuntimeNamedPrimitiveOccurrence.Occurrence root.dependencies program block step)
    (call : RuntimeNamedChildRuns.ChildRun artifact root execution
      (runBlockCore artifact root execution (fuel+1)) step) : OccurrenceOutputCode held := by
  have carriers := actual_occurrence_output held call
  cases held with
  | @named start count inputs sources caller before childHistory childRetired ordinary first size inputToken outputToken role kind
      event scope body read boundary finalOrdinary action original bound =>
    change RuntimeForestCode.carrierOwners boundary.mapped = _ at carriers
    have lengths := congrArg List.length carriers
    have single : boundary.mapped.length = 1 := by
      simpa only [RuntimeForestCode.carrierOwners,List.length_map,primitive_output_port original,
        List.length_singleton] using lengths
    obtain ⟨target,one⟩ := List.length_eq_one_iff.mp single
    have present : target ∈ boundary.afterFrame.bindings := by
      rw [boundary.sameAfter,boundary.afterBindings,one]
      exact List.mem_append_right _ List.mem_cons_self
    have native := action.outputRead
    rw [← carriers] at native
    refine ⟨target,one,present,?_⟩
    simpa only [RuntimeForestCode.carrierOwners,one,List.map_cons,List.map_nil] using native

#print axioms original_pre_post_outputs
#print axioms actual_occurrence_output_code
end Qleisli.RuntimeNamedPrimitiveOutputs
