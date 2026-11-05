import Qleisli.RuntimeTraceSpectators
import QleisliKernel.Raw.Ownership

/-! Actual Raw join/split transitions preserve the original spectator ports.
Both executions read the same original operation. Successful Raw checks supply
complete operand identity and freshness; literal traces retain exact wire
concatenation/take/drop, both fixed frames and their empty event lists. This is
Raw port locality, not typed refinement of an opaque source owner or a new gate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeStructuralTrace
open QleisliKernel QleisliKernel.Finite QleisliKernel.Semantics.Finite

private theorem join_dispatch (dependencies : List Basis) (before : Raw.State)
    (left right output : Nat) (result : Raw.Transition)
    (read : Raw.dispatch dependencies before (.join left right output) = .ok result) :
    ∃ first second afterFirst rest,
      Raw.take before left = .ok (first,afterFirst) ∧ Raw.take afterFirst right = .ok (second,rest) ∧
      Raw.insert rest output (first.wires ++ second.wires) = .ok result.state ∧ result.events = [] := by
  simp only [Raw.dispatch] at read
  obtain ⟨⟨first,afterFirst⟩,takeFirst,h⟩ := except_bind_success _ _ _ read
  obtain ⟨⟨second,rest⟩,takeSecond,h⟩ := except_bind_success _ _ _ h
  obtain ⟨inserted,insertRead,h⟩ := except_bind_success _ _ _ h
  have same := Except.ok.inj h
  subst result
  exact ⟨first,second,afterFirst,rest,takeFirst,takeSecond,insertRead,rfl⟩

private theorem split_dispatch (dependencies : List Basis) (before : Raw.State)
    (input left right leftBits : Nat) (result : Raw.Transition)
    (read : Raw.dispatch dependencies before (.split input left right leftBits) = .ok result) :
    ∃ port rest afterLeft, Raw.take before input = .ok (port,rest) ∧
      Raw.insert rest left (port.wires.take leftBits) = .ok afterLeft ∧
      Raw.insert afterLeft right (port.wires.drop leftBits) = .ok result.state ∧ result.events = [] := by
  simp only [Raw.dispatch] at read
  obtain ⟨⟨port,rest⟩,taken,h⟩ := except_bind_success _ _ _ read
  obtain ⟨_,_,h⟩ := except_bind_success _ _ _ h
  obtain ⟨afterLeft,leftRead,h⟩ := except_bind_success _ _ _ h
  obtain ⟨afterRight,rightRead,h⟩ := except_bind_success _ _ _ h
  have same := Except.ok.inj h
  subst result
  exact ⟨port,rest,afterLeft,taken,leftRead,rightRead,rfl⟩

/-- A genuine join consumes the same two complete original Ports locally and
in the caller, emits no events and leaves every original spectator intact. -/
theorem join_locality (dependencies : List Basis) (caller selected : Raw.State)
    (spectators : List Semantics.Raw.Port) (left right output : Nat) (callerResult selectedResult : Raw.Transition)
    (embedded : caller.live.Perm (selected.live ++ spectators))
    (callerRead : Raw.step dependencies caller (.join left right output) = .ok callerResult)
    (selectedRead : Raw.step dependencies selected (.join left right output) = .ok selectedResult) :
    callerResult.events = [] ∧ selectedResult.events = [] ∧
      callerResult.state.live.Perm (selectedResult.state.live ++ spectators) ∧
      callerResult.state.frame = caller.frame ∧ selectedResult.state.frame = selected.frame ∧
      Semantics.RawTrace.step caller.reference (.join left right output) = some (callerResult.state.reference,[]) ∧
      Semantics.RawTrace.step selected.reference (.join left right output) = some (selectedResult.state.reference,[]) := by
  have callerConditions := Raw.step_conditions _ _ _ _ callerRead
  have selectedConditions := Raw.step_conditions _ _ _ _ selectedRead
  have callerValid := Raw.Ownership.valid _ callerConditions.1
  obtain ⟨first,second,afterFirst,rest,takeFirst,takeSecond,insertRead,selectedEvents⟩ :=
    join_dispatch dependencies selected left right output selectedResult selectedConditions.2.1
  have firstReference := Raw.take_reference _ _ _ _ takeFirst
  have secondReference := Raw.take_reference _ _ _ _ takeSecond
  obtain ⟨callerFirst,callerTakeFirst,firstPerm,firstFrame,selectedFirstFrame,firstUnique⟩ :=
    Qleisli.RuntimeTraceSpectators.take_spectators caller.reference selected.reference spectators
      embedded callerValid.owners firstReference
  obtain ⟨callerRest,callerTakeSecond,restPerm,restFrame,selectedRestFrame,_restUnique⟩ :=
    Qleisli.RuntimeTraceSpectators.take_spectators callerFirst afterFirst.reference spectators
      firstPerm firstUnique secondReference
  have inserted := Qleisli.RuntimeTraceSpectators.insert_spectators callerRest rest.reference spectators
    restPerm output (first.wires ++ second.wires)
  have selectedInsert := Raw.insert_reference _ _ _ _ insertRead
  have callerTrace := Raw.step_reference _ _ _ _ callerRead
  have selectedTrace := Raw.step_reference _ _ _ _ selectedRead
  have callerStep : Semantics.RawTrace.step caller.reference (.join left right output) =
      some (Semantics.RawTrace.insert callerRest output (first.wires ++ second.wires),[]) := by
    simp only [Semantics.RawTrace.step,callerTakeFirst,callerTakeSecond,bind,Option.bind,pure]
  have callerData := Prod.mk.inj (Option.some.inj (callerTrace.symm.trans callerStep))
  refine ⟨callerData.2,selectedEvents,?_,?_,?_,?_,?_⟩
  · change callerResult.state.reference.live.Perm (selectedResult.state.reference.live ++ spectators)
    rw [callerData.1,selectedInsert]
    exact inserted.1
  · change callerResult.state.reference.frame = caller.reference.frame
    rw [callerData.1]
    exact restFrame.trans firstFrame
  · change selectedResult.state.reference.frame = selected.reference.frame
    rw [selectedInsert]
    exact selectedRestFrame.trans selectedFirstFrame
  · simpa only [callerData.2] using callerTrace
  · simpa only [selectedEvents] using selectedTrace

/-- A genuine split uses the same original Port's ordered take/drop wires on
both sides. Separate empty outputs remain distinct cells. No source-owner split
permission or final spectator correspondence is assumed. -/
theorem split_locality (dependencies : List Basis) (caller selected : Raw.State)
    (spectators : List Semantics.Raw.Port) (input left right leftBits : Nat) (callerResult selectedResult : Raw.Transition)
    (embedded : caller.live.Perm (selected.live ++ spectators))
    (callerRead : Raw.step dependencies caller (.split input left right leftBits) = .ok callerResult)
    (selectedRead : Raw.step dependencies selected (.split input left right leftBits) = .ok selectedResult) :
    callerResult.events = [] ∧ selectedResult.events = [] ∧
      callerResult.state.live.Perm (selectedResult.state.live ++ spectators) ∧
      callerResult.state.frame = caller.frame ∧ selectedResult.state.frame = selected.frame ∧
      Semantics.RawTrace.step caller.reference (.split input left right leftBits) = some (callerResult.state.reference,[]) ∧
      Semantics.RawTrace.step selected.reference (.split input left right leftBits) = some (selectedResult.state.reference,[]) := by
  have callerConditions := Raw.step_conditions _ _ _ _ callerRead
  have selectedConditions := Raw.step_conditions _ _ _ _ selectedRead
  have callerValid := Raw.Ownership.valid _ callerConditions.1
  obtain ⟨port,rest,afterLeft,taken,leftRead,rightRead,selectedEvents⟩ :=
    split_dispatch dependencies selected input left right leftBits selectedResult selectedConditions.2.1
  have takenReference := Raw.take_reference _ _ _ _ taken
  obtain ⟨callerRest,callerTake,restPerm,restFrame,selectedRestFrame,_restUnique⟩ :=
    Qleisli.RuntimeTraceSpectators.take_spectators caller.reference selected.reference spectators
      embedded callerValid.owners takenReference
  have leftInsert := Qleisli.RuntimeTraceSpectators.insert_spectators callerRest rest.reference spectators
    restPerm left (port.wires.take leftBits)
  have rightInsert := Qleisli.RuntimeTraceSpectators.insert_spectators
    (Semantics.RawTrace.insert callerRest left (port.wires.take leftBits))
    (Semantics.RawTrace.insert rest.reference left (port.wires.take leftBits)) spectators
    leftInsert.1 right (port.wires.drop leftBits)
  have firstReference := Raw.insert_reference _ _ _ _ leftRead
  have selectedInsert := (Raw.insert_reference _ _ _ _ rightRead).trans
    (congrArg (fun state => Semantics.RawTrace.insert state right (port.wires.drop leftBits)) firstReference)
  have callerTrace := Raw.step_reference _ _ _ _ callerRead
  have selectedTrace := Raw.step_reference _ _ _ _ selectedRead
  have callerStep : Semantics.RawTrace.step caller.reference (.split input left right leftBits) =
      some (Semantics.RawTrace.insert
        (Semantics.RawTrace.insert callerRest left (port.wires.take leftBits)) right (port.wires.drop leftBits),[]) := by
    simp only [Semantics.RawTrace.step,callerTake,bind,Option.bind,pure]
  have callerData := Prod.mk.inj (Option.some.inj (callerTrace.symm.trans callerStep))
  refine ⟨callerData.2,selectedEvents,?_,?_,?_,?_,?_⟩
  · change callerResult.state.reference.live.Perm (selectedResult.state.reference.live ++ spectators)
    rw [callerData.1,selectedInsert]
    exact rightInsert.1
  · change callerResult.state.reference.frame = caller.reference.frame
    rw [callerData.1]
    exact restFrame
  · change selectedResult.state.reference.frame = selected.reference.frame
    rw [selectedInsert]
    exact selectedRestFrame
  · simpa only [callerData.2] using callerTrace
  · simpa only [selectedEvents] using selectedTrace

#print axioms join_locality
#print axioms split_locality

end Qleisli.RuntimeStructuralTrace
