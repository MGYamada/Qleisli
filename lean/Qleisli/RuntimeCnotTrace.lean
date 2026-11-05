import Qleisli.RuntimeTraceSpectators
import Qleisli.RuntimeTraceAxes
import QleisliKernel.Raw.Ownership

/-! Exact locality of the same original checked Raw cnot.
Both actual steps supply the original two complete operands and their one-wire
shapes. True control polarity, X tables, spectator ports, frame order and the
single circuit event are preserved. No final action equation, convenient axis
premise, nominal-code availability or new acceptance gate is assumed.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeCnotTrace
open QleisliKernel QleisliKernel.Finite QleisliKernel.Semantics.Finite

private abbrev xStep (control target : Nat) : Step :=
  {Semantics.RawTrace.gate .x target with controls := [⟨control,true⟩]}

private theorem localize_xStep (axes : List Nat) (control target : Nat) :
    Semantics.RawTrace.localize axes (xStep control target) =
      xStep (axes[control]?.getD 0) (axes[target]?.getD 0) := rfl

private theorem cnot_dispatch (dependencies : List Basis) (before : Raw.State)
    (control target controlOut targetOut : Nat) (result : Raw.Transition)
    (read : Raw.dispatch dependencies before (.cnot control target controlOut targetOut) = .ok result) :
    ∃ c t afterControl rest afterControlOut,
      Raw.take before control = .ok (c,afterControl) ∧ Raw.take afterControl target = .ok (t,rest) ∧
      c.bits = 1 ∧ t.bits = 1 ∧ Raw.insert rest controlOut c.wires = .ok afterControlOut ∧
      Raw.insert afterControlOut targetOut t.wires = .ok result.state ∧
      result.events = [.circuit before.frame.length
        [{Raw.gateStep .x (before.frame.idxOf (t.wires[0]?.getD 0)) with
          controls := [⟨before.frame.idxOf (c.wires[0]?.getD 0),true⟩]}]] := by
  simp only [Raw.dispatch] at read
  obtain ⟨⟨c,afterControl⟩,takeControl,h⟩ := except_bind_success _ _ _ read
  obtain ⟨⟨t,rest⟩,takeTarget,h⟩ := except_bind_success _ _ _ h
  obtain ⟨_,oneControl,h⟩ := except_bind_success _ _ _ h
  obtain ⟨_,oneTarget,h⟩ := except_bind_success _ _ _ h
  obtain ⟨afterControlOut,insertControl,h⟩ := except_bind_success _ _ _ h
  obtain ⟨afterTargetOut,insertTarget,h⟩ := except_bind_success _ _ _ h
  have same := Except.ok.inj h
  subst result
  exact ⟨c,t,afterControl,rest,afterControlOut,takeControl,takeTarget,
    beq_iff_eq.mp (Raw.require_success _ oneControl),beq_iff_eq.mp (Raw.require_success _ oneTarget),
    insertControl,insertTarget,rfl⟩

/-- The same original cnot has one exact localized circuit in the actual
caller frame. All operand wires and uniqueness facts come from the two native
step receipts; even empty spectator owners retain their original Port cells. -/
theorem cnot_locality (dependencies : List Basis) (caller selected : Raw.State)
    (spectators : List Semantics.Raw.Port) (control target controlOut targetOut : Nat)
    (callerResult selectedResult : Raw.Transition)
    (embedded : caller.live.Perm (selected.live ++ spectators))
    (callerRead : Raw.step dependencies caller (.cnot control target controlOut targetOut) = .ok callerResult)
    (selectedRead : Raw.step dependencies selected (.cnot control target controlOut targetOut) = .ok selectedResult) :
    ∃ localSteps,
      selectedResult.events = [.circuit selected.frame.length localSteps] ∧
      callerResult.events = [.circuit caller.frame.length
        (localSteps.map (Semantics.RawTrace.localize (selected.frame.map caller.frame.idxOf)))] ∧
      callerResult.state.live.Perm (selectedResult.state.live ++ spectators) ∧
      callerResult.state.frame = caller.frame ∧ selectedResult.state.frame = selected.frame ∧
      Semantics.RawTrace.step caller.reference (.cnot control target controlOut targetOut) =
        some (callerResult.state.reference,callerResult.events) ∧
      Semantics.RawTrace.step selected.reference (.cnot control target controlOut targetOut) =
        some (selectedResult.state.reference,selectedResult.events) := by
  have callerConditions := Raw.step_conditions _ _ _ _ callerRead
  have selectedConditions := Raw.step_conditions _ _ _ _ selectedRead
  have callerValid := Raw.Ownership.valid _ callerConditions.1
  have selectedValid := Raw.Ownership.valid _ selectedConditions.1
  obtain ⟨c,t,afterControl,rest,afterControlOut,takeControl,takeTarget,oneControl,oneTarget,
      insertControl,insertTarget,localEvents⟩ :=
    cnot_dispatch dependencies selected control target controlOut targetOut selectedResult selectedConditions.2.1
  have controlTaken := Raw.Ownership.take_state _ _ _ _ takeControl
  have controlPresent := List.mem_of_find?_eq_some controlTaken.1
  have targetPresent : t ∈ selected.live := by
    have present := List.mem_of_find?_eq_some (Raw.Ownership.take_state _ _ _ _ takeTarget).1
    rw [controlTaken.2] at present
    exact (List.mem_filter.mp present).1
  have controlShape := (selectedValid.ports c controlPresent).1
  have targetShape := (selectedValid.ports t targetPresent).1
  obtain ⟨controlWire,controlWires⟩ := List.length_eq_one_iff.mp (controlShape.symm.trans oneControl)
  obtain ⟨targetWire,targetWires⟩ := List.length_eq_one_iff.mp (targetShape.symm.trans oneTarget)
  have controlCovered : controlWire ∈ selected.frame :=
    selectedValid.covered controlWire (List.mem_flatMap.mpr
      ⟨c,controlPresent,by simp only [controlWires,List.mem_singleton]⟩)
  have targetCovered : targetWire ∈ selected.frame :=
    selectedValid.covered targetWire (List.mem_flatMap.mpr
      ⟨t,targetPresent,by simp only [targetWires,List.mem_singleton]⟩)
  have controlReference := Raw.take_reference _ _ _ _ takeControl
  have targetReference := Raw.take_reference _ _ _ _ takeTarget
  obtain ⟨callerAfterControl,callerTakeControl,controlPerm,controlFrame,selectedControlFrame,controlUnique⟩ :=
    Qleisli.RuntimeTraceSpectators.take_spectators caller.reference selected.reference spectators
      embedded callerValid.owners controlReference
  obtain ⟨callerRest,callerTakeTarget,restPerm,restFrame,selectedRestFrame,_restUnique⟩ :=
    Qleisli.RuntimeTraceSpectators.take_spectators callerAfterControl afterControl.reference spectators
      controlPerm controlUnique targetReference
  have firstInsert := Qleisli.RuntimeTraceSpectators.insert_spectators callerRest rest.reference spectators
    restPerm controlOut c.wires
  have lastInsert := Qleisli.RuntimeTraceSpectators.insert_spectators
    (Semantics.RawTrace.insert callerRest controlOut c.wires)
    (Semantics.RawTrace.insert rest.reference controlOut c.wires) spectators firstInsert.1 targetOut t.wires
  have firstReference := Raw.insert_reference _ _ _ _ insertControl
  have selectedInsert := (Raw.insert_reference _ _ _ _ insertTarget).trans
    (congrArg (fun state => Semantics.RawTrace.insert state targetOut t.wires) firstReference)
  have callerTrace := Raw.step_reference _ _ _ _ callerRead
  have selectedTrace := Raw.step_reference _ _ _ _ selectedRead
  have callerStep : Semantics.RawTrace.step caller.reference (.cnot control target controlOut targetOut) =
      some (Semantics.RawTrace.insert (Semantics.RawTrace.insert callerRest controlOut c.wires) targetOut t.wires,
        [.circuit caller.frame.length [xStep (caller.frame.idxOf controlWire) (caller.frame.idxOf targetWire)]]) := by
    simp only [Semantics.RawTrace.step,callerTakeControl,callerTakeTarget,bind,Option.bind,pure,
      controlWires,targetWires,List.getElem?_cons_zero,Option.getD_some] <;> rfl
  have callerData := Prod.mk.inj (Option.some.inj (callerTrace.symm.trans callerStep))
  let localSteps := [xStep (selected.frame.idxOf controlWire) (selected.frame.idxOf targetWire)]
  have selectedEvents : selectedResult.events = [.circuit selected.frame.length localSteps] := by
    simpa only [localSteps,xStep,controlWires,targetWires,List.getElem?_cons_zero,Option.getD_some,
      Raw.gate_reference] using localEvents
  have mapped : localSteps.map (Semantics.RawTrace.localize (selected.frame.map caller.frame.idxOf)) =
      [xStep (caller.frame.idxOf controlWire) (caller.frame.idxOf targetWire)] := by
    simp only [localSteps,List.map_cons,List.map_nil,localize_xStep,
      Qleisli.RuntimeTraceAxes.wire_axis caller.frame selected.frame controlWire controlCovered,
      Qleisli.RuntimeTraceAxes.wire_axis caller.frame selected.frame targetWire targetCovered]
  refine ⟨localSteps,selectedEvents,?_,?_,?_,?_,callerTrace,selectedTrace⟩
  · rw [mapped]
    exact callerData.2
  · change callerResult.state.reference.live.Perm (selectedResult.state.reference.live ++ spectators)
    rw [callerData.1,selectedInsert]
    exact lastInsert.1
  · change callerResult.state.reference.frame = caller.reference.frame
    rw [callerData.1]
    exact restFrame.trans controlFrame
  · change selectedResult.state.reference.frame = selected.reference.frame
    rw [selectedInsert]
    exact selectedRestFrame.trans selectedControlFrame

#print axioms cnot_locality

end Qleisli.RuntimeCnotTrace
