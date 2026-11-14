import Qleisli.RuntimeNamedCallerGeometry
import Qleisli.RuntimeSemanticForest
import Qleisli.RuntimeCallTraceFrames
import Qleisli.RuntimeIntervalRawFold
import QleisliKernel.Qirf.RuntimeBasisAction

/-! Derive the source basis operand and the unchanged spectator order from
the original owner lookup, using the actual before and after Raw frames.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeBasisOwnerGeometry
open QleisliKernel QleisliKernel.Finite QleisliKernel.Qirf
open RuntimeOwnerMap (Binding Map)
open Qleisli.RuntimeStructuralLayoutEvidence (SemanticOwnerLayout)

theorem selected_binding {owner bindings} (selected : RuntimePrimitiveSource.PortAt owner bindings) :
    (⟨owner,selected.port⟩ : Binding) ∈ bindings := by
  obtain ⟨work,left,read⟩ := selected.original
  unfold RuntimePrimitiveSource.rolePorts at read
  obtain ⟨ordered,middle,lookup,returned⟩ := bind_success _ _ _ _ _ read
  have facts := RuntimeSelectionPartition.order_values bindings [owner] ordered ⟨work,middle,lookup⟩
  have ports := (pure_success _ _ _ _ returned).1
  cases ordered with
  | nil => simp at ports
  | cons binding rest =>
    have headOwner := (List.cons.inj facts.2).1
    have headPort := (List.cons.inj ports).1
    exact facts.1 (by simpa only [← headOwner,headPort] using
      (List.mem_cons_self : binding ∈ binding :: rest))

theorem binding_partitions {sources caller dependencies program block start count event before roles}
    {interval : @RuntimeInterval.Checked dependencies program block start count}
    (action : @RuntimeBasisAction.Checked sources caller dependencies program block start count event interval before)
    (frame : RuntimeOwnerMap.Checked roles interval.before) (same : frame.bindings = before.bindings) :
    let operand : Binding := ⟨event.input,action.input.port⟩
    let returned : Binding := ⟨event.output,action.output⟩
    let spectators := before.bindings.erase operand
    (operand :: spectators).Perm before.bindings ∧
    (returned :: spectators).Perm action.after.bindings := by
  let operand : Binding := ⟨event.input,action.input.port⟩
  let returned : Binding := ⟨event.output,action.output⟩
  have member : operand ∈ before.bindings := selected_binding action.input
  have original := List.perm_cons_erase member
  refine ⟨original.symm,?_⟩
  rw [action.afterBindings]
  change (returned :: before.bindings.erase operand).Perm
    (RuntimeBasisAction.updatedBindings event before.bindings action.output)
  have previous : operand ∈ frame.bindings := same.symm ▸ member
  have complement : before.bindings.filter (fun binding => binding.owner != event.input) =
      before.bindings.erase operand := by
    rw [← same]
    simpa only [List.contains_cons,List.contains_nil,Bool.or_false,operand]
      using RuntimeNamedCallerGeometry.owner_complement frame operand previous
  unfold RuntimeBasisAction.updatedBindings
  split
  · let replace := fun binding : Binding => if binding.owner == event.input then returned else binding
    have unchanged : (before.bindings.erase operand).map replace = before.bindings.erase operand := by
      conv => rhs; rw [← List.map_id (before.bindings.erase operand)]
      apply List.map_congr_left
      intro binding present
      have old := (List.mem_filter.mp (complement.symm ▸ present)).2
      have different : (binding.owner == event.input) = false := by
        simpa only [bne, Bool.not_eq_true'] using old
      simp only [replace,different,Bool.false_eq_true,if_false,id_eq]
    have moved := original.map replace
    rw [List.map_cons,unchanged] at moved
    have head : replace operand = returned := by simp [replace,operand]
    rw [head] at moved
    exact moved.symm
  · rw [complement]
    exact List.perm_append_comm (l₁ := [returned]) (l₂ := before.bindings.erase operand)

/-- A returned owner's semantic carrier is fixed by the original event and
the actual port. Every untouched owner keeps its previous layout. -/
theorem after_available {sources caller dependencies program block start count event before roles}
    {interval : @RuntimeInterval.Checked dependencies program block start count}
    (action : @RuntimeBasisAction.Checked sources caller dependencies program block start count event interval before)
    (frame : RuntimeOwnerMap.Checked roles interval.before) (same : frame.bindings = before.bindings)
    (available : RuntimeSemanticForest.Available before.bindings) :
    RuntimeSemanticForest.Available action.after.bindings := by
  have order := (binding_partitions action frame same).2
  let returned : Binding := ⟨event.output,action.output⟩
  have returnedMember : returned ∈ action.after.bindings := order.mem_iff.mp List.mem_cons_self
  have portMember : action.output ∈ interval.after.quantum.live :=
    action.after.complete.mem_iff.mp (List.mem_map.mpr ⟨returned,returnedMember,rfl⟩)
  have wireShape := ((Raw.Ownership.valid _ interval.history.2.2.1).ports action.output portMember).1
  intro binding member
  rcases List.mem_cons.mp (order.mem_iff.mpr member) with output | untouched
  · subst binding
    exact ⟨⟨event.function.outputLayout,by simpa only [returned,action.sourceOwner.1] using action.codes.outputRead,
      action.widths.2,wireShape.symm.trans action.widths.2⟩⟩
  · exact available binding (List.mem_of_mem_erase untouched)

private theorem wire_partition {roles state} (frame : RuntimeOwnerMap.Checked roles state)
    (valid : Raw.stateValid state.quantum = true) (owner : Binding) (spectators : Map)
    (permutation : (owner :: spectators).Perm frame.bindings) :
    state.quantum.frame.Perm (owner.port.wires ++ spectators.flatMap (·.port.wires)) := by
  have ports := (permutation.map Binding.port).trans frame.complete
  have wires := ports.flatMap_right Semantics.Raw.Port.wires
  simp only [List.map_cons,List.flatMap_cons,List.flatMap_map] at wires
  exact ((RuntimeCallTraceFrames.native_wires _ valid).symm.trans wires.symm)

theorem wire_partitions {sources caller dependencies program block start count event before roles}
    {interval : @RuntimeInterval.Checked dependencies program block start count}
    (action : @RuntimeBasisAction.Checked sources caller dependencies program block start count event interval before)
    (frame : RuntimeOwnerMap.Checked roles interval.before) (same : frame.bindings = before.bindings) :
    let operand : Binding := ⟨event.input,action.input.port⟩
    let spectators := (before.bindings.erase operand).flatMap (·.port.wires)
    interval.before.quantum.frame.Perm (action.input.port.wires ++ spectators) ∧
    interval.after.quantum.frame.Perm (action.output.wires ++ spectators) := by
  obtain ⟨entry,exit⟩ := binding_partitions action frame same
  let operand : Binding := ⟨event.input,action.input.port⟩
  let returned : Binding := ⟨event.output,action.output⟩
  let others := before.bindings.erase operand
  exact ⟨wire_partition frame interval.history.1 operand others (by rw [same]; exact entry),
    wire_partition action.after interval.history.2.2.1 returned others exit⟩

/-- Recover the precise frame extension, literal event and table range from
the successful original Raw dispatch, using its checked selected input port. -/
theorem literal_geometry {sources caller dependencies program block start count event before roles}
    {interval : @RuntimeInterval.Checked dependencies program block start count}
    (action : @RuntimeBasisAction.Checked sources caller dependencies program block start count event interval before)
    (frame : RuntimeOwnerMap.Checked roles interval.before) (same : frame.bindings = before.bindings) :
    let input := action.input.port
    let output := action.output
    let prior := interval.before.quantum
    let next := interval.after.quantum
    let operation := Semantics.Raw.Op.liftBasis input.token output.token output.wires action.table
    let extra := output.wires.drop input.bits
    next.frame = prior.frame ++ extra ∧
    output.wires = input.wires ++ extra ∧
    (∀ code : Nat, action.table[code]?.getD 0 < 2^output.wires.length) ∧
    RuntimeLocalEvents.trace prior.reference [operation] = some
      ⟨next.reference,[.liftBasis prior.frame.length next.frame.length
        (input.wires.map prior.frame.idxOf) (output.wires.map next.frame.idxOf) action.table],prior.frame.length⟩ := by
  intro input output prior next operation extra
  obtain ⟨work,left,read⟩ := interval.intervalRead
  have originalRead : (Raw.Observation.checkOps dependencies block.fuel interval.before
      ([operation].map Semantics.Observation.Op.pure)).run work = (.ok interval.after,left) := by
    change (Raw.Observation.checkOps dependencies block.fuel interval.before
      ((block.operations.drop start).take count)).run work = (.ok interval.after,left) at read
    rw [action.literal] at read
    exact read
  obtain ⟨events,fold⟩ := RuntimeIntervalRawFold.checkOps_pure_raw_fold dependencies block.fuel
    interval.before interval.after [operation] work left originalRead
  change [operation].foldlM (Raw.advance (dependencies.map (·.signature)))
    ⟨prior,[],prior.frame.length⟩ = .ok ⟨next,events,prior.frame.length⟩ at fold
  have traced : RuntimeLocalEvents.trace prior.reference [operation] =
      some ⟨next.reference,events,prior.frame.length⟩ :=
    Raw.operations_reference _ [operation] ⟨prior,[],prior.frame.length⟩ ⟨next,events,prior.frame.length⟩ fold
  cases step : Raw.step (dependencies.map (·.signature)) prior operation with
  | error failure =>
    simp only [List.foldlM_cons,Raw.advance,step,bind,Except.bind] at fold
    cases fold
  | ok transition =>
    have result : transition.state = next ∧ transition.events = events := by
      simpa only [List.foldlM_cons,List.foldlM_nil,Raw.advance,step,bind,Except.bind,pure,Except.pure,
        List.nil_append,Except.ok.injEq,Raw.Prepared.mk.injEq,and_true] using fold
    have dispatch := (Raw.step_conditions _ _ _ _ step).2.1
    change Raw.dispatch (dependencies.map (·.signature)) prior
      (.liftBasis input.token output.token output.wires action.table) = .ok transition at dispatch
    simp only [Raw.dispatch] at dispatch
    obtain ⟨⟨port,taken⟩,take,rest⟩ := except_bind_success _ _ _ dispatch
    have lookup := (Raw.Ownership.take_state prior taken input.token port take).1
    have portMember := List.mem_of_find?_eq_some lookup
    have tokenMatch := List.find?_some (p := fun item : Semantics.Raw.Port => item.token == input.token) lookup
    have portToken : port.token = input.token := beq_iff_eq.mp tokenMatch
    have selected : (⟨event.input,input⟩ : Binding) ∈ frame.bindings :=
      same.symm ▸ selected_binding action.input
    have inputMember : input ∈ prior.live :=
      frame.complete.mem_iff.mp (List.mem_map.mpr ⟨_,selected,rfl⟩)
    have actual : port = input :=
      RuntimeNamedCallerGeometry.full_port_unique frame port input portMember inputMember portToken
    subst port
    obtain ⟨_,guard,rest⟩ := except_bind_success _ _ _ rest
    obtain ⟨reserved,_,rest⟩ := except_bind_success _ _ _ rest
    obtain ⟨inserted,_,returned⟩ := except_bind_success _ _ _ rest
    have constraints := Raw.require_success _ guard
    simp only [Raw.tableValid,Bool.and_eq_true,beq_iff_eq] at constraints
    have wirePrefix : output.wires.take input.bits = input.wires := constraints.1.2
    have bounded := constraints.2.1.2
    simp only [pure,Except.pure,Except.ok.injEq] at returned
    have growth : next.frame = prior.frame ++ extra := by
      rw [← result.1,← returned]
    have eventList : events = [.liftBasis prior.frame.length next.frame.length
        (input.wires.map prior.frame.idxOf) (output.wires.map next.frame.idxOf) action.table] := by
      rw [growth,← result.2,← returned]
      rfl
    refine ⟨growth,?_,?_,eventList ▸ traced⟩
    · exact (List.take_append_drop input.bits output.wires).symm.trans (by rw [wirePrefix])
    · intro code
      cases entry : action.table[code]? with
      | none => simp
      | some value =>
        have valid := List.all_eq_true.mp bounded value (List.mem_of_getElem? entry)
        simpa only [entry,Option.getD_some,decide_eq_true_eq] using valid

#print axioms binding_partitions
#print axioms after_available
#print axioms literal_geometry

end Qleisli.RuntimeBasisOwnerGeometry
