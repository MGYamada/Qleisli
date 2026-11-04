import Qleisli.RuntimeTraceSpectators
import Qleisli.RuntimeTraceAxes
import QleisliKernel.Raw.Ownership

/-! Exact locality of the same original checked Raw toffoli.
All three actual operands and their one-wire shapes come from the original
steps. Both true controls, the exact X action, every spectator Port and both
fixed frame lists survive localization. No desired event equation, supplied
wire correspondence, source-code availability or new gate is assumed.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeToffoliTrace
open QleisliKernel QleisliKernel.Finite QleisliKernel.Semantics.Finite

private abbrev xStep (first second target : Nat) : Step :=
  {Semantics.RawTrace.gate .x target with controls := [⟨first,true⟩,⟨second,true⟩]}

private theorem localize_xStep (axes : List Nat) (first second target : Nat) :
    Semantics.RawTrace.localize axes (xStep first second target) =
      xStep (axes[first]?.getD 0) (axes[second]?.getD 0) (axes[target]?.getD 0) := rfl

private theorem take_mem {before after : Raw.State} {token : Nat} {port value : Semantics.Raw.Port}
    (read : Raw.take before token = .ok (port,after)) (member : value ∈ after.live) : value ∈ before.live := by
  rw [(Raw.Ownership.take_state _ _ _ _ read).2] at member
  exact (List.mem_filter.mp member).1

private theorem toffoli_dispatch (dependencies : List Basis) (before : Raw.State)
    (a b target aOut bOut targetOut : Nat) (result : Raw.Transition)
    (read : Raw.dispatch dependencies before (.toffoli a b target aOut bOut targetOut) = .ok result) :
    ∃ first second third afterA afterB rest afterAOut afterBOut,
      Raw.take before a = .ok (first,afterA) ∧ Raw.take afterA b = .ok (second,afterB) ∧
      Raw.take afterB target = .ok (third,rest) ∧ first.bits = 1 ∧ second.bits = 1 ∧ third.bits = 1 ∧
      Raw.insert rest aOut first.wires = .ok afterAOut ∧
      Raw.insert afterAOut bOut second.wires = .ok afterBOut ∧
      Raw.insert afterBOut targetOut third.wires = .ok result.state ∧
      result.events = [.circuit before.frame.length
        [{Raw.gateStep .x (before.frame.idxOf (third.wires[0]?.getD 0)) with
          controls := [⟨before.frame.idxOf (first.wires[0]?.getD 0),true⟩,
            ⟨before.frame.idxOf (second.wires[0]?.getD 0),true⟩]}]] := by
  simp only [Raw.dispatch] at read
  obtain ⟨⟨first,afterA⟩,takeA,h⟩ := except_bind_success _ _ _ read
  obtain ⟨⟨second,afterB⟩,takeB,h⟩ := except_bind_success _ _ _ h
  obtain ⟨⟨third,rest⟩,takeTarget,h⟩ := except_bind_success _ _ _ h
  obtain ⟨_,oneA,h⟩ := except_bind_success _ _ _ h
  obtain ⟨_,oneB,h⟩ := except_bind_success _ _ _ h
  obtain ⟨_,oneTarget,h⟩ := except_bind_success _ _ _ h
  obtain ⟨afterAOut,insertA,h⟩ := except_bind_success _ _ _ h
  obtain ⟨afterBOut,insertB,h⟩ := except_bind_success _ _ _ h
  obtain ⟨afterTargetOut,insertTarget,h⟩ := except_bind_success _ _ _ h
  have same := Except.ok.inj h
  subst result
  exact ⟨first,second,third,afterA,afterB,rest,afterAOut,afterBOut,takeA,takeB,takeTarget,
    beq_iff_eq.mp (Raw.require_success _ oneA),beq_iff_eq.mp (Raw.require_success _ oneB),
    beq_iff_eq.mp (Raw.require_success _ oneTarget),insertA,insertB,insertTarget,rfl⟩

/-- The two original Raw.step receipts derive the full three-operand caller
localization. Control order and polarity, X tables, the single circuit chunk,
and the unchanged complete spectator list remain exact. -/
theorem toffoli_locality (dependencies : List Basis) (caller selected : Raw.State)
    (spectators : List Semantics.Raw.Port) (a b target aOut bOut targetOut : Nat)
    (callerResult selectedResult : Raw.Transition)
    (embedded : caller.live.Perm (selected.live ++ spectators))
    (callerRead : Raw.step dependencies caller (.toffoli a b target aOut bOut targetOut) = .ok callerResult)
    (selectedRead : Raw.step dependencies selected (.toffoli a b target aOut bOut targetOut) = .ok selectedResult) :
    ∃ localSteps,
      selectedResult.events = [.circuit selected.frame.length localSteps] ∧
      callerResult.events = [.circuit caller.frame.length
        (localSteps.map (Semantics.RawTrace.localize (selected.frame.map caller.frame.idxOf)))] ∧
      callerResult.state.live.Perm (selectedResult.state.live ++ spectators) ∧
      callerResult.state.frame = caller.frame ∧ selectedResult.state.frame = selected.frame ∧
      Semantics.RawTrace.step caller.reference (.toffoli a b target aOut bOut targetOut) =
        some (callerResult.state.reference,callerResult.events) ∧
      Semantics.RawTrace.step selected.reference (.toffoli a b target aOut bOut targetOut) =
        some (selectedResult.state.reference,selectedResult.events) := by
  have callerConditions := Raw.step_conditions _ _ _ _ callerRead
  have selectedConditions := Raw.step_conditions _ _ _ _ selectedRead
  have callerValid := Raw.Ownership.valid _ callerConditions.1
  have selectedValid := Raw.Ownership.valid _ selectedConditions.1
  obtain ⟨first,second,third,afterA,afterB,rest,afterAOut,afterBOut,takeA,takeB,takeTarget,
      oneA,oneB,oneTarget,insertA,insertB,insertTarget,localEvents⟩ :=
    toffoli_dispatch dependencies selected a b target aOut bOut targetOut selectedResult selectedConditions.2.1
  have firstPresent := List.mem_of_find?_eq_some (Raw.Ownership.take_state _ _ _ _ takeA).1
  have secondPresent := take_mem takeA (List.mem_of_find?_eq_some (Raw.Ownership.take_state _ _ _ _ takeB).1)
  have thirdPresent := take_mem takeA (take_mem takeB
    (List.mem_of_find?_eq_some (Raw.Ownership.take_state _ _ _ _ takeTarget).1))
  obtain ⟨wireA,wiresA⟩ := List.length_eq_one_iff.mp ((selectedValid.ports first firstPresent).1.symm.trans oneA)
  obtain ⟨wireB,wiresB⟩ := List.length_eq_one_iff.mp ((selectedValid.ports second secondPresent).1.symm.trans oneB)
  obtain ⟨wireTarget,wiresTarget⟩ := List.length_eq_one_iff.mp
    ((selectedValid.ports third thirdPresent).1.symm.trans oneTarget)
  have coveredA : wireA ∈ selected.frame := selectedValid.covered wireA
    (List.mem_flatMap.mpr ⟨first,firstPresent,by simp only [wiresA,List.mem_singleton]⟩)
  have coveredB : wireB ∈ selected.frame := selectedValid.covered wireB
    (List.mem_flatMap.mpr ⟨second,secondPresent,by simp only [wiresB,List.mem_singleton]⟩)
  have coveredTarget : wireTarget ∈ selected.frame := selectedValid.covered wireTarget
    (List.mem_flatMap.mpr ⟨third,thirdPresent,by simp only [wiresTarget,List.mem_singleton]⟩)
  obtain ⟨callerA,callerTakeA,permA,frameA,selectedFrameA,uniqueA⟩ :=
    Qleisli.RuntimeTraceSpectators.take_spectators caller.reference selected.reference spectators
      embedded callerValid.owners (Raw.take_reference _ _ _ _ takeA)
  obtain ⟨callerB,callerTakeB,permB,frameB,selectedFrameB,uniqueB⟩ :=
    Qleisli.RuntimeTraceSpectators.take_spectators callerA afterA.reference spectators
      permA uniqueA (Raw.take_reference _ _ _ _ takeB)
  obtain ⟨callerRest,callerTakeTarget,permRest,frameRest,selectedFrameRest,_uniqueRest⟩ :=
    Qleisli.RuntimeTraceSpectators.take_spectators callerB afterB.reference spectators
      permB uniqueB (Raw.take_reference _ _ _ _ takeTarget)
  have insertedA := Qleisli.RuntimeTraceSpectators.insert_spectators callerRest rest.reference spectators
    permRest aOut first.wires
  have insertedB := Qleisli.RuntimeTraceSpectators.insert_spectators
    (Semantics.RawTrace.insert callerRest aOut first.wires)
    (Semantics.RawTrace.insert rest.reference aOut first.wires) spectators insertedA.1 bOut second.wires
  have insertedTarget := Qleisli.RuntimeTraceSpectators.insert_spectators
    (Semantics.RawTrace.insert (Semantics.RawTrace.insert callerRest aOut first.wires) bOut second.wires)
    (Semantics.RawTrace.insert (Semantics.RawTrace.insert rest.reference aOut first.wires) bOut second.wires)
    spectators insertedB.1 targetOut third.wires
  have referenceA := Raw.insert_reference _ _ _ _ insertA
  have referenceB := (Raw.insert_reference _ _ _ _ insertB).trans
    (congrArg (fun state => Semantics.RawTrace.insert state bOut second.wires) referenceA)
  have selectedInsert := (Raw.insert_reference _ _ _ _ insertTarget).trans
    (congrArg (fun state => Semantics.RawTrace.insert state targetOut third.wires) referenceB)
  have callerTrace := Raw.step_reference _ _ _ _ callerRead
  have selectedTrace := Raw.step_reference _ _ _ _ selectedRead
  have callerStep : Semantics.RawTrace.step caller.reference (.toffoli a b target aOut bOut targetOut) =
      some (Semantics.RawTrace.insert
        (Semantics.RawTrace.insert (Semantics.RawTrace.insert callerRest aOut first.wires) bOut second.wires)
        targetOut third.wires,
        [.circuit caller.frame.length [xStep (caller.frame.idxOf wireA) (caller.frame.idxOf wireB)
          (caller.frame.idxOf wireTarget)]]) := by
    simp only [Semantics.RawTrace.step,callerTakeA,callerTakeB,callerTakeTarget,bind,Option.bind,pure,
      wiresA,wiresB,wiresTarget,List.getElem?_cons_zero,Option.getD_some] <;> rfl
  have callerData := Prod.mk.inj (Option.some.inj (callerTrace.symm.trans callerStep))
  let localSteps := [xStep (selected.frame.idxOf wireA) (selected.frame.idxOf wireB)
    (selected.frame.idxOf wireTarget)]
  have selectedEvents : selectedResult.events = [.circuit selected.frame.length localSteps] := by
    simpa only [localSteps,xStep,wiresA,wiresB,wiresTarget,List.getElem?_cons_zero,Option.getD_some,
      Raw.gate_reference] using localEvents
  have mapped : localSteps.map (Semantics.RawTrace.localize (selected.frame.map caller.frame.idxOf)) =
      [xStep (caller.frame.idxOf wireA) (caller.frame.idxOf wireB) (caller.frame.idxOf wireTarget)] := by
    simp only [localSteps,List.map_cons,List.map_nil,localize_xStep,
      Qleisli.RuntimeTraceAxes.wire_axis caller.frame selected.frame wireA coveredA,
      Qleisli.RuntimeTraceAxes.wire_axis caller.frame selected.frame wireB coveredB,
      Qleisli.RuntimeTraceAxes.wire_axis caller.frame selected.frame wireTarget coveredTarget]
  refine ⟨localSteps,selectedEvents,?_,?_,?_,?_,callerTrace,selectedTrace⟩
  · rw [mapped]
    exact callerData.2
  · change callerResult.state.reference.live.Perm (selectedResult.state.reference.live ++ spectators)
    rw [callerData.1,selectedInsert]
    exact insertedTarget.1
  · change callerResult.state.reference.frame = caller.reference.frame
    rw [callerData.1]
    exact frameRest.trans (frameB.trans frameA)
  · change selectedResult.state.reference.frame = selected.reference.frame
    rw [selectedInsert]
    exact selectedFrameRest.trans (selectedFrameB.trans selectedFrameA)

#print axioms toffoli_locality

end Qleisli.RuntimeToffoliTrace
