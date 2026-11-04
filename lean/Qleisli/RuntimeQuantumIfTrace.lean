import Qleisli.RuntimeTraceSpectators
import Qleisli.RuntimeTraceAxes
import QleisliKernel.Raw.Ownership

/-! Exact locality of both original checked Raw quantumIf tapes.
The false arm precedes the true arm in the same single circuit event. Actual
step/dispatch receipts supply the control wire, all target wire membership and
both original tape bounds. Scalar phases and empty tapes remain intact. No
source code, desired event equation, new shape filter or acceptance gate is used.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeQuantumIfTrace
open QleisliKernel QleisliKernel.Finite QleisliKernel.Semantics.Finite

private abbrev arm (control : Nat) (targetAxes : List Nat) (polarity : Bool)
    (written : List Semantics.Raw.UnitaryStep) : List Step :=
  written.map fun original =>
    let action := Semantics.RawTrace.localize targetAxes (Semantics.RawTrace.unitary original)
    {action with controls := action.controls ++ [⟨control,polarity⟩]}

private theorem localize_control (axes : List Nat) (original : Step) (control : Nat) (polarity : Bool) :
    Semantics.RawTrace.localize axes {original with controls := original.controls ++ [⟨control,polarity⟩]} =
      {Semantics.RawTrace.localize axes original with
        controls := (Semantics.RawTrace.localize axes original).controls ++ [⟨axes[control]?.getD 0,polarity⟩]} := by
  rcases original with ⟨controls,action⟩
  simp only [Semantics.RawTrace.localize,List.map_append,List.map_cons,List.map_nil]

private theorem step_bounds (bits : Nat) (written : List Semantics.Raw.UnitaryStep)
    (valid : Raw.circuitStepsValid [] bits (written.map Raw.unitaryStep) = true)
    (original : Semantics.Raw.UnitaryStep) (member : original ∈ written) :
    (∀ control ∈ (Semantics.RawTrace.unitary original).controls, control.index < bits) ∧
      (∀ axis ∈ Finite.targets (Semantics.RawTrace.unitary original).action, axis < bits) := by
  have present : Raw.unitaryStep original ∈ written.map Raw.unitaryStep := List.mem_map_of_mem member
  have checked := (Bool.and_eq_true_iff.mp ((List.all_eq_true.mp valid) _ present)).1
  simp only [Finite.axesValid,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq,Raw.unitary_reference] at checked
  have inside := checked.1.2
  constructor
  · intro control held
    exact inside control.index (List.mem_append.mpr (Or.inl (List.mem_map_of_mem held)))
  · intro axis held
    exact inside axis (List.mem_append.mpr (Or.inr held))

private theorem arm_mapped (callerFrame selectedFrame wires : List Nat) (control : Nat) (polarity : Bool)
    (bits : Nat) (written : List Semantics.Raw.UnitaryStep)
    (shape : bits = wires.length) (covered : ∀ wire ∈ wires, wire ∈ selectedFrame)
    (controlCovered : control ∈ selectedFrame)
    (valid : Raw.circuitStepsValid [] bits (written.map Raw.unitaryStep) = true) :
    (arm (selectedFrame.idxOf control) (wires.map selectedFrame.idxOf) polarity written).map
        (Semantics.RawTrace.localize (selectedFrame.map callerFrame.idxOf)) =
      arm (callerFrame.idxOf control) (wires.map callerFrame.idxOf) polarity written := by
  simp only [arm,List.map_map]
  apply List.map_congr_left
  intro original member
  have bounds := step_bounds bits written valid original member
  have innerLength : (wires.map selectedFrame.idxOf).length = bits := by
    simpa only [List.length_map] using shape.symm
  have composed := Qleisli.RuntimeTraceAxes.localize_comp (selectedFrame.map callerFrame.idxOf)
    (wires.map selectedFrame.idxOf) (Semantics.RawTrace.unitary original)
    (fun value held => by simpa only [innerLength] using bounds.1 value held)
    (fun axis held => by simpa only [innerLength] using bounds.2 axis held)
  have axes := Qleisli.RuntimeTraceAxes.wire_axes callerFrame selectedFrame wires covered
  simp only [Function.comp_def,localize_control,composed,axes,
    Qleisli.RuntimeTraceAxes.wire_axis callerFrame selectedFrame control controlCovered]

private theorem quantumIf_dispatch (dependencies : List Basis) (before : Raw.State)
    (control target controlOut targetOut : Nat) (zero one : List Semantics.Raw.UnitaryStep) (result : Raw.Transition)
    (read : Raw.dispatch dependencies before (.quantumIf control target controlOut targetOut zero one) = .ok result) :
    ∃ c t afterControl rest afterControlOut,
      Raw.take before control = .ok (c,afterControl) ∧ Raw.take afterControl target = .ok (t,rest) ∧
      c.bits = 1 ∧ Raw.circuitStepsValid [] t.bits (zero.map Raw.unitaryStep) = true ∧
      Raw.circuitStepsValid [] t.bits (one.map Raw.unitaryStep) = true ∧
      Raw.insert rest controlOut c.wires = .ok afterControlOut ∧
      Raw.insert afterControlOut targetOut t.wires = .ok result.state ∧
      result.events = [.circuit before.frame.length
        (arm (before.frame.idxOf (c.wires[0]?.getD 0)) (Raw.axes before t.wires) false zero ++
          arm (before.frame.idxOf (c.wires[0]?.getD 0)) (Raw.axes before t.wires) true one)] := by
  simp only [Raw.dispatch] at read
  obtain ⟨⟨c,afterControl⟩,takeControl,h⟩ := except_bind_success _ _ _ read
  obtain ⟨⟨t,rest⟩,takeTarget,h⟩ := except_bind_success _ _ _ h
  obtain ⟨_,oneControl,h⟩ := except_bind_success _ _ _ h
  obtain ⟨_,valid,h⟩ := except_bind_success _ _ _ h
  obtain ⟨afterControlOut,insertControl,h⟩ := except_bind_success _ _ _ h
  obtain ⟨afterTargetOut,insertTarget,h⟩ := except_bind_success _ _ _ h
  have same := Except.ok.inj h
  subst result
  have tapes := Bool.and_eq_true_iff.mp (Raw.require_success _ valid)
  exact ⟨c,t,afterControl,rest,afterControlOut,takeControl,takeTarget,
    beq_iff_eq.mp (Raw.require_success _ oneControl),tapes.1,tapes.2,insertControl,insertTarget,rfl⟩

/-- Both complete written tapes survive as separate local lists of their
original lengths, in false/true order, inside one exact native circuit event.
All coordinate bounds and operand wires are derived from the actual checks. -/
theorem quantumIf_locality (dependencies : List Basis) (caller selected : Raw.State)
    (spectators : List Semantics.Raw.Port) (control target controlOut targetOut : Nat)
    (zero one : List Semantics.Raw.UnitaryStep) (callerResult selectedResult : Raw.Transition)
    (embedded : caller.live.Perm (selected.live ++ spectators))
    (callerRead : Raw.step dependencies caller (.quantumIf control target controlOut targetOut zero one) = .ok callerResult)
    (selectedRead : Raw.step dependencies selected (.quantumIf control target controlOut targetOut zero one) = .ok selectedResult) :
    ∃ zeroLocal oneLocal,
      zeroLocal.length = zero.length ∧ oneLocal.length = one.length ∧
      selectedResult.events = [.circuit selected.frame.length (zeroLocal ++ oneLocal)] ∧
      callerResult.events = [.circuit caller.frame.length
        (zeroLocal.map (Semantics.RawTrace.localize (selected.frame.map caller.frame.idxOf)) ++
          oneLocal.map (Semantics.RawTrace.localize (selected.frame.map caller.frame.idxOf)))] ∧
      callerResult.state.live.Perm (selectedResult.state.live ++ spectators) ∧
      callerResult.state.frame = caller.frame ∧ selectedResult.state.frame = selected.frame ∧
      Semantics.RawTrace.step caller.reference (.quantumIf control target controlOut targetOut zero one) =
        some (callerResult.state.reference,callerResult.events) ∧
      Semantics.RawTrace.step selected.reference (.quantumIf control target controlOut targetOut zero one) =
        some (selectedResult.state.reference,selectedResult.events) := by
  have callerConditions := Raw.step_conditions _ _ _ _ callerRead
  have selectedConditions := Raw.step_conditions _ _ _ _ selectedRead
  have callerValid := Raw.Ownership.valid _ callerConditions.1
  have selectedValid := Raw.Ownership.valid _ selectedConditions.1
  obtain ⟨c,t,afterControl,rest,afterControlOut,takeControl,takeTarget,oneControl,zeroValid,oneValid,
      insertControl,insertTarget,localEvents⟩ :=
    quantumIf_dispatch dependencies selected control target controlOut targetOut zero one selectedResult selectedConditions.2.1
  have controlTaken := Raw.Ownership.take_state _ _ _ _ takeControl
  have controlPresent := List.mem_of_find?_eq_some controlTaken.1
  have targetPresent : t ∈ selected.live := by
    have present := List.mem_of_find?_eq_some (Raw.Ownership.take_state _ _ _ _ takeTarget).1
    rw [controlTaken.2] at present
    exact (List.mem_filter.mp present).1
  have controlShape := (selectedValid.ports c controlPresent).1
  have targetShape := (selectedValid.ports t targetPresent).1
  obtain ⟨controlWire,controlWires⟩ := List.length_eq_one_iff.mp (controlShape.symm.trans oneControl)
  have controlCovered : controlWire ∈ selected.frame := selectedValid.covered controlWire
    (List.mem_flatMap.mpr ⟨c,controlPresent,by simp only [controlWires,List.mem_singleton]⟩)
  have targetCovered : ∀ wire ∈ t.wires, wire ∈ selected.frame := by
    intro wire member
    exact selectedValid.covered wire (List.mem_flatMap.mpr ⟨t,targetPresent,member⟩)
  obtain ⟨callerAfterControl,callerTakeControl,controlPerm,controlFrame,selectedControlFrame,controlUnique⟩ :=
    Qleisli.RuntimeTraceSpectators.take_spectators caller.reference selected.reference spectators
      embedded callerValid.owners (Raw.take_reference _ _ _ _ takeControl)
  obtain ⟨callerRest,callerTakeTarget,restPerm,restFrame,selectedRestFrame,_restUnique⟩ :=
    Qleisli.RuntimeTraceSpectators.take_spectators callerAfterControl afterControl.reference spectators
      controlPerm controlUnique (Raw.take_reference _ _ _ _ takeTarget)
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
  have callerStep : Semantics.RawTrace.step caller.reference
      (.quantumIf control target controlOut targetOut zero one) =
      some (Semantics.RawTrace.insert (Semantics.RawTrace.insert callerRest controlOut c.wires) targetOut t.wires,
        [.circuit caller.frame.length
          (arm (caller.frame.idxOf controlWire) (Raw.axes caller t.wires) false zero ++
            arm (caller.frame.idxOf controlWire) (Raw.axes caller t.wires) true one)]) := by
    simp only [Semantics.RawTrace.step,callerTakeControl,callerTakeTarget,bind,Option.bind,pure,
      controlWires,List.getElem?_cons_zero,Option.getD_some] <;> rfl
  have callerData := Prod.mk.inj (Option.some.inj (callerTrace.symm.trans callerStep))
  let zeroLocal := arm (selected.frame.idxOf controlWire) (Raw.axes selected t.wires) false zero
  let oneLocal := arm (selected.frame.idxOf controlWire) (Raw.axes selected t.wires) true one
  have selectedEvents : selectedResult.events = [.circuit selected.frame.length (zeroLocal ++ oneLocal)] := by
    simpa only [zeroLocal,oneLocal,controlWires,List.getElem?_cons_zero,Option.getD_some] using localEvents
  have zeroMapped := arm_mapped caller.frame selected.frame t.wires controlWire false t.bits zero
    targetShape targetCovered controlCovered zeroValid
  have oneMapped := arm_mapped caller.frame selected.frame t.wires controlWire true t.bits one
    targetShape targetCovered controlCovered oneValid
  refine ⟨zeroLocal,oneLocal,?_,?_,selectedEvents,?_,?_,?_,?_,callerTrace,selectedTrace⟩
  · simp only [zeroLocal,arm,List.length_map]
  · simp only [oneLocal,arm,List.length_map]
  · change callerResult.events = [.circuit caller.frame.length
      ((arm (selected.frame.idxOf controlWire) (t.wires.map selected.frame.idxOf) false zero).map _ ++
        (arm (selected.frame.idxOf controlWire) (t.wires.map selected.frame.idxOf) true one).map _)]
    rw [zeroMapped,oneMapped]
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

#print axioms quantumIf_locality

end Qleisli.RuntimeQuantumIfTrace
