import Qleisli.RuntimeTraceSpectators
import Qleisli.RuntimeTraceAxes
import QleisliKernel.Raw.Ownership

/-! The same original applyUnitary tape in local and complete caller frames.
Actual Raw.step/dispatch receipts supply operand identity, original coordinate
bounds and state validity. The resulting circuit chunk, even when empty, is
localized without changing controls, phase tables or dependency fields. Live
spectator ports and both original frame lists are retained. No event equation,
code availability, replacement program or new acceptance filter is a premise.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeApplyTrace
open QleisliKernel QleisliKernel.Finite QleisliKernel.Semantics.Finite

private theorem apply_dispatch (dependencies : List Basis) (before : Raw.State)
    (input output : Nat) (steps : List Step) (result : Raw.Transition)
    (read : Raw.dispatch dependencies before (.applyUnitary input output steps) = .ok result) :
    ∃ port rest, Raw.take before input = .ok (port,rest) ∧
      Raw.circuitStepsValid dependencies port.bits steps = true ∧
      Raw.insert rest output port.wires = .ok result.state ∧
      result.events = [.circuit before.frame.length (steps.map (Raw.remap (Raw.axes before port.wires)))] := by
  simp only [Raw.dispatch] at read
  obtain ⟨⟨port,rest⟩,taken,h⟩ := except_bind_success _ _ _ read
  obtain ⟨_,valid,h⟩ := except_bind_success _ _ _ h
  obtain ⟨inserted,insertRead,h⟩ := except_bind_success _ _ _ h
  have same := Except.ok.inj h
  subst result
  exact ⟨port,rest,taken,Raw.require_success _ valid,insertRead,rfl⟩

private theorem step_bounds (dependencies : List Basis) (bits : Nat) (steps : List Step)
    (valid : Raw.circuitStepsValid dependencies bits steps = true) (original : Step) (member : original ∈ steps) :
    (∀ control ∈ original.controls, control.index < bits) ∧
      (∀ axis ∈ Finite.targets original.action, axis < bits) := by
  have checked := (Bool.and_eq_true_iff.mp ((List.all_eq_true.mp valid) original member)).1
  simp only [Finite.axesValid,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at checked
  have inside := checked.1.2
  constructor
  · intro control present
    exact inside control.index (List.mem_append.mpr (Or.inl (List.mem_map_of_mem present)))
  · intro axis present
    exact inside axis (List.mem_append.mpr (Or.inr present))

/-- A genuine original applyUnitary step emits exactly one local circuit,
including an empty circuit. Its complete caller counterpart is the same tape
localized through the fixed original frame map. Every bound is derived from
those actual successful Raw checks, not supplied as an additional filter. -/
theorem applyUnitary_locality (dependencies : List Basis) (caller selected : Raw.State)
    (spectators : List Semantics.Raw.Port) (input output : Nat) (steps : List Step)
    (callerResult selectedResult : Raw.Transition)
    (embedded : caller.live.Perm (selected.live ++ spectators))
    (callerRead : Raw.step dependencies caller (.applyUnitary input output steps) = .ok callerResult)
    (selectedRead : Raw.step dependencies selected (.applyUnitary input output steps) = .ok selectedResult) :
    ∃ localSteps,
      selectedResult.events = [.circuit selected.frame.length localSteps] ∧
      callerResult.events = [.circuit caller.frame.length
        (localSteps.map (Semantics.RawTrace.localize (selected.frame.map caller.frame.idxOf)))] ∧
      callerResult.state.live.Perm (selectedResult.state.live ++ spectators) ∧
      callerResult.state.frame = caller.frame ∧ selectedResult.state.frame = selected.frame ∧
      Semantics.RawTrace.step selected.reference (.applyUnitary input output steps) =
        some (selectedResult.state.reference,selectedResult.events) ∧
      Semantics.RawTrace.step caller.reference (.applyUnitary input output steps) =
        some (callerResult.state.reference,callerResult.events) := by
  have callerConditions := Raw.step_conditions _ _ _ _ callerRead
  have selectedConditions := Raw.step_conditions _ _ _ _ selectedRead
  have callerValid := Raw.Ownership.valid _ callerConditions.1
  have selectedValid := Raw.Ownership.valid _ selectedConditions.1
  obtain ⟨port,rest,taken,tapeValid,insertRead,localEvents⟩ :=
    apply_dispatch dependencies selected input output steps selectedResult selectedConditions.2.1
  have found := (Raw.Ownership.take_state _ _ _ _ taken).1
  have present := List.mem_of_find?_eq_some found
  have shape : port.bits = port.wires.length := (selectedValid.ports port present).1
  have covered : ∀ wire ∈ port.wires, wire ∈ selected.frame := by
    intro wire member
    exact selectedValid.covered wire (List.mem_flatMap.mpr ⟨port,present,member⟩)
  have localTake := Raw.take_reference _ _ _ _ taken
  obtain ⟨callerRest,callerTake,remainder,callerFrame,selectedFrame,_remainingUnique⟩ :=
    Qleisli.RuntimeTraceSpectators.take_spectators caller.reference selected.reference spectators
      embedded callerValid.owners localTake
  have inserted := Qleisli.RuntimeTraceSpectators.insert_spectators callerRest rest.reference spectators
    remainder output port.wires
  have selectedInsert := Raw.insert_reference _ _ _ _ insertRead
  have callerTrace := Raw.step_reference _ _ _ _ callerRead
  have selectedTrace := Raw.step_reference _ _ _ _ selectedRead
  have callerStep : Semantics.RawTrace.step caller.reference (.applyUnitary input output steps) =
      some (Semantics.RawTrace.insert callerRest output port.wires,
        [.circuit caller.frame.length (steps.map (Semantics.RawTrace.localize (Raw.axes caller port.wires)))]) := by
    simp only [Semantics.RawTrace.step,callerTake,bind,Option.bind,pure]
    rfl
  have callerData := Prod.mk.inj (Option.some.inj (callerTrace.symm.trans callerStep))
  let localSteps := steps.map (Semantics.RawTrace.localize (Raw.axes selected port.wires))
  have innerLength : (Raw.axes selected port.wires).length = port.bits := by
    simpa only [Raw.axes,List.length_map] using shape.symm
  have axes : (Raw.axes selected port.wires).map
      (fun index => (selected.frame.map caller.frame.idxOf)[index]?.getD 0) = Raw.axes caller port.wires :=
    Qleisli.RuntimeTraceAxes.wire_axes caller.frame selected.frame port.wires covered
  have mapped : localSteps.map (Semantics.RawTrace.localize (selected.frame.map caller.frame.idxOf)) =
      steps.map (Semantics.RawTrace.localize (Raw.axes caller port.wires)) := by
    change (steps.map (Semantics.RawTrace.localize (Raw.axes selected port.wires))).map _ = _
    rw [List.map_map]
    apply List.map_congr_left
    intro original member
    have bounds := step_bounds dependencies port.bits steps tapeValid original member
    have composed := Qleisli.RuntimeTraceAxes.localize_comp (selected.frame.map caller.frame.idxOf)
      (Raw.axes selected port.wires) original
      (fun control present => by simpa only [innerLength] using bounds.1 control present)
      (fun axis present => by simpa only [innerLength] using bounds.2 axis present)
    exact composed.trans (congrArg (fun indices => Semantics.RawTrace.localize indices original) axes)
  refine ⟨localSteps,localEvents,?_,?_,?_,?_,selectedTrace,callerTrace⟩
  · rw [mapped]
    exact callerData.2
  · change callerResult.state.reference.live.Perm (selectedResult.state.reference.live ++ spectators)
    rw [callerData.1,selectedInsert]
    exact inserted.1
  · change callerResult.state.reference.frame = caller.reference.frame
    rw [callerData.1]
    exact callerFrame
  · change selectedResult.state.reference.frame = selected.reference.frame
    rw [selectedInsert]
    exact selectedFrame

#print axioms applyUnitary_locality

end Qleisli.RuntimeApplyTrace
