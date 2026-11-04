import Qleisli.RuntimeTraceBounds
import Qleisli.RuntimeApplyTrace
import Qleisli.RuntimeStructuralTrace
import Qleisli.RuntimeGateTrace
import Qleisli.RuntimeCnotTrace
import Qleisli.RuntimeToffoliTrace
import Qleisli.RuntimeQuantumIfTrace
import QleisliKernel.Raw.Sector
import QleisliKernel.Semantics.RawOwnerFlow

/-! Exact locality of one original Raw step in a retained sector fragment.
The same actual local/caller step receipts determine the circuit events and
post-interface. The actual owner-flow step and actual sector EventPiece relation
exclude constructors that cannot occur in this circuit fragment. No caller
event equation, final spectator relation, axis bound, allowlist or new acceptance
filter is supplied. Whole-operation-list localization remains separate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeStepLocality
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Semantics.Finite

private theorem pieces_flatten (bits : Nat) (chunks pieces : List (List Step))
    (related : Exact.ListRel (Raw.Sector.EventPiece bits) (RuntimeLocalEvents.localEvents bits chunks) pieces) :
    chunks.flatten = pieces.flatten := by
  induction chunks generalizing pieces with
  | nil =>
    cases pieces with
    | nil => rfl
    | cons first rest => exact False.elim related
  | cons first rest ih =>
    cases pieces with
    | nil => exact False.elim related
    | cons piece pieces =>
      rcases related.1 with same | ⟨same,_⟩
      · have samePiece : first = piece := by
          simpa only [Semantics.Raw.Event.circuit.injEq,true_and] using same
        simp only [List.flatten_cons,samePiece,ih pieces related.2]
      · cases same

private theorem assemble {dependencies : List Basis} {caller selected : Raw.State}
    {spectators : List Semantics.Raw.Port} {op : Semantics.Raw.Op}
    {callerResult selectedResult : Raw.Transition} {pieces chunks : List (List Step)}
    (callerRead : Raw.step dependencies caller op = .ok callerResult)
    (selectedRead : Raw.step dependencies selected op = .ok selectedResult)
    (related : Exact.ListRel (Raw.Sector.EventPiece selected.frame.length) selectedResult.events pieces)
    (localEvents : selectedResult.events = RuntimeLocalEvents.localEvents selected.frame.length chunks)
    (callerEvents : callerResult.events = RuntimeLocalEvents.circuitEvents caller.frame.length
      (selected.frame.map caller.frame.idxOf) chunks)
    (bounded : RuntimeLocalEvents.bounds selected.frame.length chunks = true)
    (remaining : callerResult.state.live.Perm (selectedResult.state.live ++ spectators))
    (callerFrame : callerResult.state.frame = caller.frame)
    (selectedFrame : selectedResult.state.frame = selected.frame) :
    ∃ chunks,
      selectedResult.events = RuntimeLocalEvents.localEvents selected.frame.length chunks ∧
      callerResult.events = RuntimeLocalEvents.circuitEvents caller.frame.length
        (selected.frame.map caller.frame.idxOf) chunks ∧
      chunks.flatten = pieces.flatten ∧ RuntimeLocalEvents.bounds selected.frame.length chunks = true ∧
      callerResult.state.live.Perm (selectedResult.state.live ++ spectators) ∧
      callerResult.state.frame = caller.frame ∧ selectedResult.state.frame = selected.frame ∧
      Semantics.RawTrace.step caller.reference op = some (callerResult.state.reference,callerResult.events) ∧
      Semantics.RawTrace.step selected.reference op = some (selectedResult.state.reference,selectedResult.events) := by
  have localPieces : Exact.ListRel (Raw.Sector.EventPiece selected.frame.length)
      (RuntimeLocalEvents.localEvents selected.frame.length chunks) pieces := by
    rw [← localEvents]
    exact related
  exact ⟨chunks,localEvents,callerEvents,pieces_flatten _ _ _ localPieces,bounded,remaining,
    callerFrame,selectedFrame,Raw.step_reference _ _ _ _ callerRead,Raw.step_reference _ _ _ _ selectedRead⟩

private theorem impossible_piece (bits : Nat) (event : Semantics.Raw.Event) (pieces : List (List Step))
    (excluded : ∀ steps, ¬ Raw.Sector.EventPiece bits event steps)
    (related : Exact.ListRel (Raw.Sector.EventPiece bits) [event] pieces) : False := by
  cases pieces with
  | nil => exact related
  | cons first rest => exact excluded first related.1

/-- One SAME original operation, its TWO actual checked Raw steps, actual
logical owner transport and exact local sector pieces determine both traces.
Every real circuit contributes its own chunk, even an empty tape; structural
steps contribute none. All final fields and bounds are conclusions. -/
theorem step_locality (dependencies : List Basis) (caller selected : Raw.State)
    (spectators : List Semantics.Raw.Port) (op : Semantics.Raw.Op)
    (callerResult selectedResult : Raw.Transition)
    (ownerBefore ownerAfter : Semantics.RawOwnerFlow.Frame) (pieces : List (List Step))
    (embedded : caller.live.Perm (selected.live ++ spectators))
    (callerRead : Raw.step dependencies caller op = .ok callerResult)
    (selectedRead : Raw.step dependencies selected op = .ok selectedResult)
    (ownerRead : Semantics.RawOwnerFlow.step ownerBefore op = some ownerAfter)
    (related : Exact.ListRel (Raw.Sector.EventPiece selected.frame.length) selectedResult.events pieces) :
    ∃ chunks,
      selectedResult.events = RuntimeLocalEvents.localEvents selected.frame.length chunks ∧
      callerResult.events = RuntimeLocalEvents.circuitEvents caller.frame.length
        (selected.frame.map caller.frame.idxOf) chunks ∧
      chunks.flatten = pieces.flatten ∧ RuntimeLocalEvents.bounds selected.frame.length chunks = true ∧
      callerResult.state.live.Perm (selectedResult.state.live ++ spectators) ∧
      callerResult.state.frame = caller.frame ∧ selectedResult.state.frame = selected.frame ∧
      Semantics.RawTrace.step caller.reference op = some (callerResult.state.reference,callerResult.events) ∧
      Semantics.RawTrace.step selected.reference op = some (selectedResult.state.reference,selectedResult.events) := by
  cases op with
  | init0 output wire =>
    change none = some ownerAfter at ownerRead
    cases ownerRead
  | packUnit output =>
    change none = some ownerAfter at ownerRead
    cases ownerRead
  | unpackUnit input =>
    change none = some ownerAfter at ownerRead
    cases ownerRead
  | gate value input output =>
    obtain ⟨localSteps,localEvents,callerEvents,remaining,callerFrame,selectedFrame,_,_⟩ :=
      Qleisli.RuntimeGateTrace.gate_locality dependencies caller selected spectators value input output
        callerResult selectedResult embedded callerRead selectedRead
    exact assemble (chunks := [localSteps]) callerRead selectedRead related localEvents callerEvents
      (Qleisli.RuntimeTraceBounds.gate_bounds dependencies selected value input output selectedResult localSteps
        selectedRead localEvents) remaining callerFrame selectedFrame
  | cnot control target controlOut targetOut =>
    obtain ⟨localSteps,localEvents,callerEvents,remaining,callerFrame,selectedFrame,_,_⟩ :=
      Qleisli.RuntimeCnotTrace.cnot_locality dependencies caller selected spectators control target controlOut targetOut
        callerResult selectedResult embedded callerRead selectedRead
    exact assemble (chunks := [localSteps]) callerRead selectedRead related localEvents callerEvents
      (Qleisli.RuntimeTraceBounds.cnot_bounds dependencies selected control target controlOut targetOut
        selectedResult localSteps selectedRead localEvents) remaining callerFrame selectedFrame
  | toffoli a b target aOut bOut targetOut =>
    obtain ⟨localSteps,localEvents,callerEvents,remaining,callerFrame,selectedFrame,_,_⟩ :=
      Qleisli.RuntimeToffoliTrace.toffoli_locality dependencies caller selected spectators a b target aOut bOut targetOut
        callerResult selectedResult embedded callerRead selectedRead
    exact assemble (chunks := [localSteps]) callerRead selectedRead related localEvents callerEvents
      (Qleisli.RuntimeTraceBounds.toffoli_bounds dependencies selected a b target aOut bOut targetOut
        selectedResult localSteps selectedRead localEvents) remaining callerFrame selectedFrame
  | applyUnitary input output written =>
    obtain ⟨localSteps,localEvents,callerEvents,remaining,callerFrame,selectedFrame,_,_⟩ :=
      Qleisli.RuntimeApplyTrace.applyUnitary_locality dependencies caller selected spectators input output written
        callerResult selectedResult embedded callerRead selectedRead
    exact assemble (chunks := [localSteps]) callerRead selectedRead related localEvents callerEvents
      (Qleisli.RuntimeTraceBounds.apply_bounds dependencies selected input output written selectedResult localSteps
        selectedRead localEvents) remaining callerFrame selectedFrame
  | quantumIf control target controlOut targetOut zero one =>
    obtain ⟨zeroLocal,oneLocal,_,_,localEvents,callerEvents,remaining,callerFrame,selectedFrame,_,_⟩ :=
      Qleisli.RuntimeQuantumIfTrace.quantumIf_locality dependencies caller selected spectators control target controlOut targetOut
        zero one callerResult selectedResult embedded callerRead selectedRead
    exact assemble (chunks := [zeroLocal ++ oneLocal]) callerRead selectedRead related localEvents
      (by simpa only [RuntimeLocalEvents.circuitEvents,List.map_cons,List.map_nil,List.map_append] using callerEvents)
      (Qleisli.RuntimeTraceBounds.quantumIf_bounds dependencies selected control target controlOut targetOut zero one
        selectedResult (zeroLocal ++ oneLocal) selectedRead localEvents) remaining callerFrame selectedFrame
  | join left right output =>
    obtain ⟨callerEvents,localEvents,remaining,callerFrame,selectedFrame,_,_⟩ :=
      Qleisli.RuntimeStructuralTrace.join_locality dependencies caller selected spectators left right output
        callerResult selectedResult embedded callerRead selectedRead
    exact assemble (chunks := []) callerRead selectedRead related localEvents callerEvents rfl
      remaining callerFrame selectedFrame
  | split input left right leftBits =>
    obtain ⟨callerEvents,localEvents,remaining,callerFrame,selectedFrame,_,_⟩ :=
      Qleisli.RuntimeStructuralTrace.split_locality dependencies caller selected spectators input left right leftBits
        callerResult selectedResult embedded callerRead selectedRead
    exact assemble (chunks := []) callerRead selectedRead related localEvents callerEvents rfl
      remaining callerFrame selectedFrame
  | liftBasis input output wires table =>
    have trace := Raw.step_reference _ _ _ _ selectedRead
    simp only [Semantics.RawTrace.step] at trace
    obtain ⟨⟨port,next⟩,_,finished⟩ := Option.bind_eq_some_iff.mp trace
    have events := (Prod.mk.inj (Option.some.inj finished)).2
    rw [← events] at related
    exact False.elim (impossible_piece _ _ _ (by
      intro steps piece
      rcases piece with same | ⟨same,_⟩ <;> cases same) related)
  | certifiedCompute input output ancilla function physical logical =>
    have trace := Raw.step_reference _ _ _ _ selectedRead
    simp only [Semantics.RawTrace.step] at trace
    obtain ⟨⟨port,next⟩,_,finished⟩ := Option.bind_eq_some_iff.mp trace
    have events := (Prod.mk.inj (Option.some.inj finished)).2
    rw [← events] at related
    exact False.elim (impossible_piece _ _ _ (by
      intro steps piece
      rcases piece with same | ⟨same,_⟩ <;> cases same) related)
  | computeUseUncompute input output targets ancilla function uses =>
    have trace := Raw.step_reference _ _ _ _ selectedRead
    simp only [Semantics.RawTrace.step] at trace
    obtain ⟨⟨source,next⟩,_,rest⟩ := Option.bind_eq_some_iff.mp trace
    obtain ⟨⟨ports,after⟩,_,finished⟩ := Option.bind_eq_some_iff.mp rest
    have events := (Prod.mk.inj (Option.some.inj finished)).2
    rw [← events] at related
    exact False.elim (impossible_piece _ _ _ (by
      intro steps piece
      rcases piece with same | ⟨same,_⟩ <;> cases same) related)

#print axioms step_locality

end Qleisli.RuntimeStepLocality
