import Qleisli.RuntimeBasisOwnerGeometry
import QleisliKernel.Qirf.RuntimeCertifiedComputed

/-! Geometry of the actual protected computation in its caller. The scratch
wire is reserved without entering the caller's frame. The original ordered
data axes and complete live output are recovered from the literal Raw read.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeComputedGeometry
open QleisliKernel QleisliKernel.Finite QleisliKernel.Qirf
open RuntimeOwnerMap (Binding)
open RuntimeComputedPredicate (ProtectedInterval)

theorem literal_geometry {sources caller dependencies program block start count event source interval before}
    (checked : @ProtectedInterval sources caller dependencies program block start count event source interval before) :
    let prior := interval.before.quantum
    let next := interval.after.quantum
    let axes := checked.input.port.wires.map prior.frame.idxOf
    next.frame = prior.frame ∧
    Raw.tableValid checked.input.port.bits 1 checked.table false = true ∧
    Raw.usesValid checked.input.port.bits 1 0 checked.uses = true ∧
    RuntimeLocalEvents.trace prior.reference [checked.operation] = some
      ⟨next.reference,[.protectedComputed prior.frame.length axes checked.input.port.bits 1 checked.table checked.uses],
        prior.frame.length⟩ := by
  intro prior next axes
  obtain ⟨work,left,read⟩ := interval.intervalRead
  rw [checked.literal] at read
  obtain ⟨events,fold⟩ := RuntimeIntervalRawFold.checkOps_pure_raw_fold dependencies block.fuel
    interval.before interval.after [checked.operation] work left read
  change [checked.operation].foldlM (Raw.advance (dependencies.map (·.signature)))
    ⟨prior,[],prior.frame.length⟩ = .ok ⟨next,events,prior.frame.length⟩ at fold
  have traced := Raw.operations_reference _ [checked.operation] ⟨prior,[],prior.frame.length⟩
    ⟨next,events,prior.frame.length⟩ fold
  cases step : Raw.step (dependencies.map (·.signature)) prior checked.operation with
  | error failure =>
    simp only [List.foldlM_cons,Raw.advance,step,bind,Except.bind] at fold
    cases fold
  | ok transition =>
    have result : transition.state = next ∧ transition.events = events := by
      simpa only [List.foldlM_cons,List.foldlM_nil,Raw.advance,step,bind,Except.bind,pure,Except.pure,
        List.nil_append,Except.ok.injEq,Raw.Prepared.mk.injEq,and_true] using fold
    have dispatch := (Raw.step_conditions _ _ _ _ step).2.1
    change Raw.dispatch (dependencies.map (·.signature)) prior
      (.computeUseUncompute checked.input.port.token checked.output.token [] [checked.auxiliary]
        checked.table checked.uses) = .ok transition at dispatch
    rw [Raw.dispatch.eq_13] at dispatch
    obtain ⟨⟨port,taken⟩,take,rest⟩ := except_bind_success _ _ _ dispatch
    have priorPort := (Raw.Ownership.take_state prior taken checked.input.port.token port take).1
    have member := List.mem_of_find?_eq_some priorPort
    have token := beq_iff_eq.mp (List.find?_some (p := fun (item : Semantics.Raw.Port) => item.token == checked.input.port.token) priorPort)
    have selected : (⟨event.input,checked.input.port⟩ : Binding) ∈ checked.frame.bindings :=
      checked.sameFrame.symm ▸ RuntimeBasisOwnerGeometry.selected_binding checked.input
    have inputMember : checked.input.port ∈ prior.live :=
      checked.frame.complete.mem_iff.mp (List.mem_map.mpr ⟨_,selected,rfl⟩)
    have actual : port = checked.input.port :=
      RuntimeNamedCallerGeometry.full_port_unique checked.frame port checked.input.port member inputMember token
    subst port
    simp only [List.foldlM_nil,List.zip_nil_left,List.flatMap_nil,List.append_nil,List.length_nil,List.length_cons,
      Nat.zero_add,bind,Except.bind,pure,Except.pure] at rest
    obtain ⟨_,guard,rest⟩ := except_bind_success _ _ _ rest
    obtain ⟨reserved,reserve,rest⟩ := except_bind_success _ _ _ rest
    obtain ⟨inserted,insert,returned⟩ := except_bind_success _ _ _ rest
    have constraints := Raw.require_success _ guard
    simp only [Bool.and_eq_true] at constraints
    have kept : inserted.frame = prior.frame := by
      rw [Raw.Ownership.insert_state _ _ _ _ insert,Raw.Ownership.reserve_state _ _ _ reserve,
        (Raw.Ownership.take_state _ _ _ _ take).2]
    have equal := (Except.ok.inj returned).symm
    rw [equal] at result
    have eventList : events = [.protectedComputed prior.frame.length axes checked.input.port.bits 1
        checked.table checked.uses] := result.2.symm
    rw [eventList] at traced
    exact ⟨result.1 ▸ kept,constraints.1.2,constraints.2,traced⟩

theorem certified_geometry {sources caller dependencies program block start count event source interval before}
    (checked : @RuntimeCertifiedComputed.Literal sources caller dependencies program block start count event source interval before) :
    let prior := interval.before.quantum
    let next := interval.after.quantum
    let axes := checked.input.port.wires.map prior.frame.idxOf
    next.frame = prior.frame ∧
    RuntimeLocalEvents.trace prior.reference [checked.operation] = some
      ⟨next.reference,[.computed prior.frame.length axes checked.input.port.bits 1 checked.table checked.useSteps checked.logicalSteps],
        prior.frame.length⟩ := by
  intro prior next axes
  obtain ⟨work,left,read⟩ := interval.intervalRead
  rw [checked.original] at read
  obtain ⟨events,fold⟩ := RuntimeIntervalRawFold.checkOps_pure_raw_fold dependencies block.fuel
    interval.before interval.after [checked.operation] work left read
  change [checked.operation].foldlM (Raw.advance (dependencies.map (·.signature)))
    ⟨prior,[],prior.frame.length⟩ = .ok ⟨next,events,prior.frame.length⟩ at fold
  have traced := Raw.operations_reference _ [checked.operation] ⟨prior,[],prior.frame.length⟩
    ⟨next,events,prior.frame.length⟩ fold
  cases step : Raw.step (dependencies.map (·.signature)) prior checked.operation with
  | error failure =>
    simp only [List.foldlM_cons,Raw.advance,step,bind,Except.bind] at fold
    cases fold
  | ok transition =>
    have result : transition.state = next ∧ transition.events = events := by
      simpa only [List.foldlM_cons,List.foldlM_nil,Raw.advance,step,bind,Except.bind,pure,Except.pure,
        List.nil_append,Except.ok.injEq,Raw.Prepared.mk.injEq,and_true] using fold
    have dispatch := (Raw.step_conditions _ _ _ _ step).2.1
    change Raw.dispatch (dependencies.map (·.signature)) prior
      (.certifiedCompute checked.input.port.token checked.output.token [checked.auxiliary]
        checked.table checked.useSteps checked.logicalSteps) = .ok transition at dispatch
    rw [Raw.dispatch.eq_12] at dispatch
    obtain ⟨⟨port,taken⟩,take,rest⟩ := except_bind_success _ _ _ dispatch
    have priorPort := (Raw.Ownership.take_state prior taken checked.input.port.token port take).1
    have member := List.mem_of_find?_eq_some priorPort
    have token := beq_iff_eq.mp (List.find?_some (p := fun (item : Semantics.Raw.Port) => item.token == checked.input.port.token) priorPort)
    have selected : (⟨event.input,checked.input.port⟩ : Binding) ∈ checked.frame.bindings :=
      checked.sameFrame.symm ▸ RuntimeBasisOwnerGeometry.selected_binding checked.input
    have inputMember : checked.input.port ∈ prior.live :=
      checked.frame.complete.mem_iff.mp (List.mem_map.mpr ⟨_,selected,rfl⟩)
    have actual : port = checked.input.port :=
      RuntimeNamedCallerGeometry.full_port_unique checked.frame port checked.input.port member inputMember token
    subst port
    obtain ⟨_,_,rest⟩ := except_bind_success _ _ _ rest
    obtain ⟨reserved,reserve,rest⟩ := except_bind_success _ _ _ rest
    obtain ⟨inserted,insert,returned⟩ := except_bind_success _ _ _ rest
    have kept : inserted.frame = prior.frame := by
      rw [Raw.Ownership.insert_state _ _ _ _ insert,Raw.Ownership.reserve_state _ _ _ reserve,
        (Raw.Ownership.take_state _ _ _ _ take).2]
    have equal := (Except.ok.inj returned).symm
    rw [equal] at result
    have eventList : events = [.computed prior.frame.length axes checked.input.port.bits 1
        checked.table checked.useSteps checked.logicalSteps] := result.2.symm
    rw [eventList] at traced
    exact ⟨result.1 ▸ kept,traced⟩

#print axioms literal_geometry
#print axioms certified_geometry
end Qleisli.RuntimeComputedGeometry
