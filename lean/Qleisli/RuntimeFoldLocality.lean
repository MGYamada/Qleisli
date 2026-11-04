import Qleisli.RuntimeStepLocality

/-! Whole original-operation-list locality from two actual Raw fold receipts.
The private histories retain only the native step receipts and exact event
appends extracted from those folds. They are not public premises. The actual
owner fold and local sector pieces derive every per-step locality fact. Literal
chunk appends retain all circuit boundaries, including empty circuit chunks.
Original-reader adapters, synthetic finish events and source forest codes remain
separate. This module changes no checker or acceptance condition.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeFoldLocality
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite QleisliKernel.Semantics.Finite

private inductive History (dependencies : List Basis) :
    Raw.State → List Semantics.Raw.Op → Raw.State → List Semantics.Raw.Event → Prop
  | nil (state) : History dependencies state [] state []
  | cons (before op transition operations after events)
      (checked : Raw.step dependencies before op = .ok transition)
      (rest : History dependencies transition.state operations after events) :
      History dependencies before (op :: operations) after (transition.events ++ events)

private theorem fold_history (dependencies : List Basis) (operations : List Semantics.Raw.Op)
    (initial result : Raw.Prepared)
    (read : operations.foldlM (Raw.advance dependencies) initial = .ok result) :
    ∃ events, History dependencies initial.state operations result.state events ∧
      result.events = initial.events ++ events ∧ result.inputBits = initial.inputBits := by
  induction operations generalizing initial with
  | nil =>
    have same := Except.ok.inj read
    subst result
    exact ⟨[],.nil _,by simp only [List.append_nil],rfl⟩
  | cons operation operations ih =>
    simp only [List.foldlM_cons] at read
    obtain ⟨next,advanced,rest⟩ := except_bind_success _ _ _ read
    obtain ⟨transition,checked,finished⟩ := except_bind_success _ _ _ advanced
    have same := Except.ok.inj finished
    subst next
    obtain ⟨events,history,appended,bits⟩ := ih _ rest
    refine ⟨transition.events ++ events,.cons _ _ _ _ _ _ checked history,?_,bits⟩
    simpa only [List.append_assoc] using appended

private theorem relation_split {α β : Type} (relation : α → β → Prop)
    (first rest : List α) (values : List β)
    (related : Exact.ListRel relation (first ++ rest) values) :
    ∃ firstValues restValues, values = firstValues ++ restValues ∧
      Exact.ListRel relation first firstValues ∧ Exact.ListRel relation rest restValues := by
  induction first generalizing values with
  | nil => exact ⟨[],values,rfl,trivial,related⟩
  | cons head tail ih =>
    cases values with
    | nil => exact False.elim related
    | cons value values =>
      obtain ⟨front,back,same,firstRelated,restRelated⟩ := ih values related.2
      exact ⟨value :: front,back,congrArg (List.cons value) same,⟨related.1,firstRelated⟩,restRelated⟩

private theorem history_locality (dependencies : List Basis) (operations : List Semantics.Raw.Op)
    (caller selected callerAfter selectedAfter : Raw.State)
    (callerEvents selectedEvents : List Semantics.Raw.Event)
    (spectators : List Semantics.Raw.Port)
    (ownerBefore ownerAfter : Semantics.RawOwnerFlow.Frame) (pieces : List (List Step))
    (embedded : caller.live.Perm (selected.live ++ spectators))
    (callerHistory : History dependencies caller operations callerAfter callerEvents)
    (selectedHistory : History dependencies selected operations selectedAfter selectedEvents)
    (ownerFold : operations.foldlM Semantics.RawOwnerFlow.step ownerBefore = some ownerAfter)
    (related : Exact.ListRel (Raw.Sector.EventPiece selected.frame.length) selectedEvents pieces) :
    ∃ chunks,
      selectedEvents = RuntimeLocalEvents.localEvents selected.frame.length chunks ∧
      callerEvents = RuntimeLocalEvents.circuitEvents caller.frame.length
        (selected.frame.map caller.frame.idxOf) chunks ∧
      chunks.flatten = pieces.flatten ∧ RuntimeLocalEvents.bounds selected.frame.length chunks = true ∧
      callerAfter.live.Perm (selectedAfter.live ++ spectators) ∧
      callerAfter.frame = caller.frame ∧ selectedAfter.frame = selected.frame := by
  induction operations generalizing caller selected callerEvents selectedEvents ownerBefore pieces with
  | nil =>
    cases callerHistory with
    | nil =>
      cases selectedHistory with
      | nil =>
        cases pieces with
        | nil => exact ⟨[],rfl,rfl,rfl,rfl,embedded,rfl,rfl⟩
        | cons first rest => exact False.elim related
  | cons operation operations ih =>
    cases callerHistory with
    | cons _ _ callerStep _ _ callerTail callerRead callerRest =>
      cases selectedHistory with
      | cons _ _ selectedStep _ _ selectedTail selectedRead selectedRest =>
        simp only [List.foldlM_cons] at ownerFold
        obtain ⟨ownerMiddle,ownerRead,ownerRest⟩ := Option.bind_eq_some_iff.mp ownerFold
        obtain ⟨firstPieces,restPieces,piecesAppend,firstRelated,restRelated⟩ :=
          relation_split (Raw.Sector.EventPiece selected.frame.length) selectedStep.events selectedTail pieces related
        obtain ⟨firstChunks,firstLocal,firstCaller,firstFlatten,firstBounds,middlePerm,
            callerFrame,selectedFrame,_,_⟩ :=
          Qleisli.RuntimeStepLocality.step_locality dependencies caller selected spectators operation callerStep selectedStep
            ownerBefore ownerMiddle firstPieces embedded callerRead selectedRead ownerRead firstRelated
        have remainingPieces : Exact.ListRel (Raw.Sector.EventPiece selectedStep.state.frame.length)
            selectedTail restPieces := by
          rw [selectedFrame]
          exact restRelated
        obtain ⟨restChunks,restLocal,restCaller,restFlatten,restBounds,remaining,
            callerFinalFrame,selectedFinalFrame⟩ :=
          ih callerStep.state selectedStep.state callerTail selectedTail ownerMiddle restPieces
            middlePerm callerRest selectedRest ownerRest remainingPieces
        have restLocalOriginal : selectedTail = RuntimeLocalEvents.localEvents selected.frame.length restChunks := by
          simpa only [selectedFrame] using restLocal
        have restCallerOriginal : callerTail = RuntimeLocalEvents.circuitEvents caller.frame.length
            (selected.frame.map caller.frame.idxOf) restChunks := by
          simpa only [callerFrame,selectedFrame] using restCaller
        have restBoundsOriginal : RuntimeLocalEvents.bounds selected.frame.length restChunks = true := by
          simpa only [selectedFrame] using restBounds
        refine ⟨firstChunks ++ restChunks,?_,?_,?_,?_,remaining,
          callerFinalFrame.trans callerFrame,selectedFinalFrame.trans selectedFrame⟩
        · rw [firstLocal,restLocalOriginal]
          simp only [RuntimeLocalEvents.localEvents,List.map_append]
        · rw [firstCaller,restCallerOriginal]
          simp only [RuntimeLocalEvents.circuitEvents,List.map_append]
        · simp only [List.flatten_append,firstFlatten,restFlatten,piecesAppend]
        · change (firstChunks ++ restChunks).all _ = true
          rw [List.all_append]
          exact Bool.and_eq_true_iff.mpr ⟨firstBounds,restBoundsOriginal⟩

/-- TWO actual folds over the SAME original operations determine complete
local/caller circuit traces. Each native step, owner transition and piece split
is derived internally; no successful locality chain or final invariant is an
input. Chunks are appended literally and retain every real empty circuit. -/
theorem folds_locality (dependencies : List Basis) (operations : List Semantics.Raw.Op)
    (caller selected : Raw.State) (callerResult selectedResult : Raw.Prepared)
    (spectators : List Semantics.Raw.Port)
    (ownerBefore ownerAfter : Semantics.RawOwnerFlow.Frame) (pieces : List (List Step))
    (embedded : caller.live.Perm (selected.live ++ spectators))
    (callerFold : operations.foldlM (Raw.advance dependencies)
      ⟨caller,[],caller.frame.length⟩ = .ok callerResult)
    (selectedFold : operations.foldlM (Raw.advance dependencies)
      ⟨selected,[],selected.frame.length⟩ = .ok selectedResult)
    (ownerFold : operations.foldlM Semantics.RawOwnerFlow.step ownerBefore = some ownerAfter)
    (related : Exact.ListRel (Raw.Sector.EventPiece selected.frame.length) selectedResult.events pieces) :
    ∃ chunks,
      selectedResult.events = RuntimeLocalEvents.localEvents selected.frame.length chunks ∧
      callerResult.events = RuntimeLocalEvents.circuitEvents caller.frame.length
        (selected.frame.map caller.frame.idxOf) chunks ∧
      chunks.flatten = pieces.flatten ∧ RuntimeLocalEvents.bounds selected.frame.length chunks = true ∧
      callerResult.state.live.Perm (selectedResult.state.live ++ spectators) ∧
      callerResult.state.frame = caller.frame ∧ selectedResult.state.frame = selected.frame ∧
      callerResult.inputBits = caller.frame.length ∧ selectedResult.inputBits = selected.frame.length ∧
      RuntimeLocalEvents.trace caller.reference operations = some callerResult.reference ∧
      RuntimeLocalEvents.trace selected.reference operations = some selectedResult.reference := by
  obtain ⟨callerEvents,callerHistory,callerAppended,callerBits⟩ :=
    fold_history dependencies operations ⟨caller,[],caller.frame.length⟩ callerResult callerFold
  obtain ⟨selectedEvents,selectedHistory,selectedAppended,selectedBits⟩ :=
    fold_history dependencies operations ⟨selected,[],selected.frame.length⟩ selectedResult selectedFold
  have callerEmitted : callerResult.events = callerEvents := by
    simpa only [List.nil_append] using callerAppended
  have selectedEmitted : selectedResult.events = selectedEvents := by
    simpa only [List.nil_append] using selectedAppended
  have selectedPieces : Exact.ListRel (Raw.Sector.EventPiece selected.frame.length) selectedEvents pieces := by
    rw [← selectedEmitted]
    exact related
  obtain ⟨chunks,localEvents,callerEventsEquation,flatten,bounded,remaining,callerFrame,selectedFrame⟩ :=
    history_locality dependencies operations caller selected callerResult.state selectedResult.state callerEvents selectedEvents
      spectators ownerBefore ownerAfter pieces embedded callerHistory selectedHistory ownerFold selectedPieces
  refine ⟨chunks,selectedEmitted.trans localEvents,callerEmitted.trans callerEventsEquation,flatten,bounded,
    remaining,callerFrame,selectedFrame,callerBits,selectedBits,?_,?_⟩
  · exact Raw.operations_reference dependencies operations ⟨caller,[],caller.frame.length⟩ callerResult callerFold
  · exact Raw.operations_reference dependencies operations ⟨selected,[],selected.frame.length⟩ selectedResult selectedFold

#print axioms folds_locality

end Qleisli.RuntimeFoldLocality
