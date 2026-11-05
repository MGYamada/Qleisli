import Qleisli.RuntimeTraceSpectators
import Qleisli.RuntimeTraceAxes
import QleisliKernel.Raw.Ownership

/-! Actual one-Bit Raw gate locality in the original caller frame.
Both successful original steps supply the same operand Port and its checked
one-wire shape. Their exact gate action, spectator ports and fixed frame lists
are retained. No final event equation, nominal-code premise, replacement tape
or additional acceptance gate is supplied.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeGateTrace
open QleisliKernel QleisliKernel.Finite QleisliKernel.Semantics.Finite

private theorem gate_dispatch (dependencies : List Basis) (before : Raw.State)
    (value : Semantics.Raw.Gate) (input output : Nat) (result : Raw.Transition)
    (read : Raw.dispatch dependencies before (.gate value input output) = .ok result) :
    ∃ port rest, Raw.take before input = .ok (port,rest) ∧ port.bits = 1 ∧
      Raw.insert rest output port.wires = .ok result.state ∧
      result.events = [.circuit before.frame.length
        [Raw.gateStep value (before.frame.idxOf (port.wires[0]?.getD 0))]] := by
  simp only [Raw.dispatch] at read
  obtain ⟨⟨port,rest⟩,taken,h⟩ := except_bind_success _ _ _ read
  obtain ⟨_,one,h⟩ := except_bind_success _ _ _ h
  obtain ⟨inserted,insertRead,h⟩ := except_bind_success _ _ _ h
  have same := Except.ok.inj h
  subst result
  exact ⟨port,rest,taken,beq_iff_eq.mp (Raw.require_success _ one),insertRead,rfl⟩

/-- A single localization changes only the gate's actual axis. -/
theorem localize_gate (axes : List Nat) (value : Semantics.Raw.Gate) (index : Nat) :
    Semantics.RawTrace.localize axes (Semantics.RawTrace.gate value index) =
      Semantics.RawTrace.gate value (axes[index]?.getD 0) := by
  cases value <;> rfl

/-- Every original h/x/z/t gate has the exact localized circuit action under
the two actual checks. Its operand is the same complete Port, and all original
spectators, including zero-width cells, remain in the caller live interface. -/
theorem gate_locality (dependencies : List Basis) (caller selected : Raw.State)
    (spectators : List Semantics.Raw.Port) (value : Semantics.Raw.Gate) (input output : Nat)
    (callerResult selectedResult : Raw.Transition)
    (embedded : caller.live.Perm (selected.live ++ spectators))
    (callerRead : Raw.step dependencies caller (.gate value input output) = .ok callerResult)
    (selectedRead : Raw.step dependencies selected (.gate value input output) = .ok selectedResult) :
    ∃ localSteps,
      selectedResult.events = [.circuit selected.frame.length localSteps] ∧
      callerResult.events = [.circuit caller.frame.length
        (localSteps.map (Semantics.RawTrace.localize (selected.frame.map caller.frame.idxOf)))] ∧
      callerResult.state.live.Perm (selectedResult.state.live ++ spectators) ∧
      callerResult.state.frame = caller.frame ∧ selectedResult.state.frame = selected.frame ∧
      Semantics.RawTrace.step caller.reference (.gate value input output) =
        some (callerResult.state.reference,callerResult.events) ∧
      Semantics.RawTrace.step selected.reference (.gate value input output) =
        some (selectedResult.state.reference,selectedResult.events) := by
  have callerConditions := Raw.step_conditions _ _ _ _ callerRead
  have selectedConditions := Raw.step_conditions _ _ _ _ selectedRead
  have callerValid := Raw.Ownership.valid _ callerConditions.1
  have selectedValid := Raw.Ownership.valid _ selectedConditions.1
  obtain ⟨port,rest,taken,one,insertRead,localEvents⟩ :=
    gate_dispatch dependencies selected value input output selectedResult selectedConditions.2.1
  have present := List.mem_of_find?_eq_some (Raw.Ownership.take_state _ _ _ _ taken).1
  have shape := (selectedValid.ports port present).1
  obtain ⟨wire,wires⟩ := List.length_eq_one_iff.mp (shape.symm.trans one)
  have covered : wire ∈ selected.frame :=
    selectedValid.covered wire (List.mem_flatMap.mpr ⟨port,present,by simp only [wires,List.mem_singleton]⟩)
  have localTake := Raw.take_reference _ _ _ _ taken
  obtain ⟨callerRest,callerTake,remainder,callerFrame,selectedFrame,_remainingUnique⟩ :=
    Qleisli.RuntimeTraceSpectators.take_spectators caller.reference selected.reference spectators
      embedded callerValid.owners localTake
  have inserted := Qleisli.RuntimeTraceSpectators.insert_spectators callerRest rest.reference spectators
    remainder output port.wires
  have selectedInsert := Raw.insert_reference _ _ _ _ insertRead
  have callerTrace := Raw.step_reference _ _ _ _ callerRead
  have selectedTrace := Raw.step_reference _ _ _ _ selectedRead
  have callerStep : Semantics.RawTrace.step caller.reference (.gate value input output) =
      some (Semantics.RawTrace.insert callerRest output port.wires,
        [.circuit caller.frame.length [Semantics.RawTrace.gate value (caller.frame.idxOf wire)]]) := by
    simp only [Semantics.RawTrace.step,callerTake,bind,Option.bind,pure,wires,
      List.getElem?_cons_zero,Option.getD_some] <;> rfl
  have callerData := Prod.mk.inj (Option.some.inj (callerTrace.symm.trans callerStep))
  let localSteps := [Semantics.RawTrace.gate value (selected.frame.idxOf wire)]
  have selectedEvents : selectedResult.events = [.circuit selected.frame.length localSteps] := by
    simpa only [localSteps,wires,List.getElem?_cons_zero,Option.getD_some,Raw.gate_reference] using localEvents
  have mapped : localSteps.map (Semantics.RawTrace.localize (selected.frame.map caller.frame.idxOf)) =
      [Semantics.RawTrace.gate value (caller.frame.idxOf wire)] := by
    simp only [localSteps,List.map_cons,List.map_nil,localize_gate,
      Qleisli.RuntimeTraceAxes.wire_axis caller.frame selected.frame wire covered]
  refine ⟨localSteps,selectedEvents,?_,?_,?_,?_,callerTrace,selectedTrace⟩
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

#print axioms localize_gate
#print axioms gate_locality

end Qleisli.RuntimeGateTrace
