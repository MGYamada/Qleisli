import Qleisli.RuntimeNamedThreePackedOutput
import Qleisli.RuntimeObservingPrefix
import Qleisli.RawFiniteRows
import Qleisli.Semantics.ObservingAction

/-! Identify the original named-call interval in the independent observing
reader and retain each inherited outcome through the pure Raw action.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeNamedThreePackedInstrument
open QleisliKernel QleisliKernel.Qirf
open Qleisli.RuntimeForestProduct
open Qleisli.RuntimeNamedThreePackedOutput
open Qleisli.Semantics.ObservingAction (History)
open RuntimeForestCode (Frame)

noncomputable def pureHistory (dependencies : List Semantics.Finite.Dependency)
    (events : List Semantics.Raw.Event) (initial : History) : History :=
  {initial with operator := fun row col =>
    Qleisli.Semantics.RawAction.events dependencies events (fun input => initial.operator input col) row}

/-- Finite-row agreement of an inherited operator with the source input
encoding suffices for the original pure interval's operator on each column. -/
theorem pureHistory_operator_congr {before after events}
    (bounded : RawFiniteRows.BoundedEvents before events after)
    (dependencies : List Semantics.Finite.Dependency) (history : History)
    (input : Nat → Nat → ℂ)
    (represented : ∀ col, RawFiniteRows.OnRows before
      (fun row => history.operator row col) (fun row => input row col)) :
    ∀ col, RawFiniteRows.OnRows after
      (fun row => (pureHistory dependencies events history).operator row col)
      (Qleisli.Semantics.RawAction.events dependencies events (fun row => input row col)) := by
  intro col
  exact bounded.congr dependencies _ _ (represented col)

/-- Advance all inherited histories by one event, in the interpreter's order. -/
noncomputable def advance (dependencies : List Semantics.Finite.Dependency)
    (recurse : List Semantics.Observation.Event → History → Option (List History))
    (histories : List History) (event : Semantics.Observation.Event) : Option (List History) := do
  let groups ← histories.mapM (Qleisli.Semantics.ObservingAction.step dependencies recurse event)
  return groups.flatten

theorem run_append_event (dependencies : List Semantics.Finite.Dependency) (fuel : Nat)
    (prior : List Semantics.Observation.Event) (event : Semantics.Observation.Event)
    (initial : History) :
    Qleisli.Semantics.ObservingAction.run dependencies (fuel+1) (prior++[event]) initial =
      (do
        let histories ← Qleisli.Semantics.ObservingAction.run dependencies (fuel+1) prior initial
        advance dependencies (Qleisli.Semantics.ObservingAction.run dependencies fuel) histories event) := by
  let step := advance dependencies (Qleisli.Semantics.ObservingAction.run dependencies fuel)
  change (prior++[event]).foldlM step [initial] = (do
    let histories ← prior.foldlM step [initial]
    step histories event)
  simp only [List.foldlM_append,List.foldlM_cons,List.foldlM_nil,bind_pure]

private theorem advance_pure (dependencies : List Semantics.Finite.Dependency)
    (recurse : List Semantics.Observation.Event → History → Option (List History))
    (event : Semantics.Raw.Event) (histories : List History) :
    advance dependencies recurse histories (.pure event) =
      some (histories.map (pureHistory dependencies [event])) := by
  have groups :
      histories.mapM (Qleisli.Semantics.ObservingAction.step dependencies recurse (.pure event)) =
        some (histories.map (fun history => [pureHistory dependencies [event] history])) := by
    induction histories with
    | nil => rfl
    | cons history rest ih =>
      rw [List.mapM_cons,ih,List.map_cons]
      rfl
  rw [advance,groups]
  change some ((histories.map (fun history => [pureHistory dependencies [event] history])).flatten) = _
  clear groups
  congr 1
  induction histories with
  | nil => rfl
  | cons history rest ih =>
    simp only [List.map_cons,List.flatten_cons,List.cons_append,List.nil_append,ih]

private theorem fold_pure (dependencies : List Semantics.Finite.Dependency)
    (recurse : List Semantics.Observation.Event → History → Option (List History))
    (events : List Semantics.Raw.Event) (histories : List History) :
    (events.map Semantics.Observation.Event.pure).foldlM (advance dependencies recurse) histories =
      some (histories.map (pureHistory dependencies events)) := by
  induction events generalizing histories with
  | nil =>
    have identity : pureHistory dependencies [] = id := by
      funext history
      cases history
      rfl
    simp [identity]
  | cons event events ih =>
    rw [List.map_cons,List.foldlM_cons,advance_pure]
    change (events.map Semantics.Observation.Event.pure).foldlM (advance dependencies recurse)
        (histories.map (pureHistory dependencies [event])) =
      some (histories.map (pureHistory dependencies (event::events)))
    rw [ih,List.map_map]
    rfl

/-- Keep every history and the stored outcome order through the pure slice.
Arbitrary surrounding events use the original recursive observing step. -/
theorem run_surround_pure (dependencies : List Semantics.Finite.Dependency) (fuel : Nat)
    (earlier suffix : List Semantics.Observation.Event)
    (events : List Semantics.Raw.Event) (initial : History) :
    let advanceHistory := advance dependencies (Qleisli.Semantics.ObservingAction.run dependencies fuel)
    Qleisli.Semantics.ObservingAction.run dependencies (fuel+1)
        ((earlier ++ events.map Semantics.Observation.Event.pure) ++ suffix) initial =
      (do
        let histories ← Qleisli.Semantics.ObservingAction.run dependencies (fuel+1) earlier initial
        suffix.foldlM advanceHistory (histories.map (pureHistory dependencies events))) := by
  intro advanceHistory
  change (((earlier ++ events.map Semantics.Observation.Event.pure) ++ suffix).foldlM
    advanceHistory [initial]) = (do
      let histories ← earlier.foldlM advanceHistory [initial]
      suffix.foldlM advanceHistory (histories.map (pureHistory dependencies events)))
  rw [List.foldlM_append,List.foldlM_append]
  cases before : earlier.foldlM advanceHistory [initial] with
  | none => rfl
  | some histories =>
    change (do
      let updated ← (events.map Semantics.Observation.Event.pure).foldlM advanceHistory histories
      suffix.foldlM advanceHistory updated) = _
    rw [fold_pure]
    rfl

/-- The actual observing fold preserves all stored classical and hidden
outcomes when it executes a pure slice. Every column can be arbitrary. -/
theorem run_pure (dependencies : List Semantics.Finite.Dependency)
    (fuel : Nat) (events : List Semantics.Raw.Event) (initial : History) :
    Qleisli.Semantics.ObservingAction.run dependencies (fuel+1)
        (events.map Semantics.Observation.Event.pure) initial =
      some [pureHistory dependencies events initial] := by
  exact fold_pure dependencies (Qleisli.Semantics.ObservingAction.run dependencies fuel) events [initial]

/-- One proof identifies the actual reader result, the complete observing
fold from any inherited history, and the original three-call logical action
on its encoded input. The event list is shared with the source equation. -/
theorem original_three_observing {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime)
    (view : RuntimeNamedThreeOccurrence.Three body.checked.result.steps)
    (coverage : RuntimeNamedSelectionOn.Coverage view.centerSelection
      (RuntimeNamedThreeOccurrence.actual_body_middle body view)) :
    let held := RuntimeNamedThreeOccurrence.actual_body_middle body view
    let pre := RuntimeNamedOccurrenceAction.span view.prePrimitive
    let center := RuntimeNamedSelectionOn.middle view.centerSelection held coverage
    let post := RuntimeNamedOccurrenceAction.span view.postPrimitive
    let source := QleisliKernel.SourceTypes.SourceRuntimeScope.Subject.whole prepared.source.body
    let initial := RuntimeBodyOperations.initialHistory prepared body.checked.native runtime body.checked.inputs
    let state := body.checked.native.whole.state
    let finish := Semantics.Raw.Event.reorder state.quantum.frame.length
      (RuntimeForestCode.forestAxes state.quantum.frame body.checked.owners.bindings)
    pre.start = 0 → center.start = pre.start+pre.count → post.start = center.start+center.count →
    pre.count+center.count+post.count = body.root.program.operations.length →
    ∃ a b c : List Semantics.Raw.Event,
      Semantics.Observation.read body.root.program = some body.checked.native.whole.prepared ∧
      body.checked.native.whole.prepared.events =
        (a++b++c++[finish]).map Semantics.Observation.Event.pure ∧
      (∀ history : History, Qleisli.Semantics.ObservingAction.run body.root.dependencies 65
        body.checked.native.whole.prepared.events history =
          some [pureHistory body.root.dependencies (a++b++c++[finish]) history]) ∧
      ∃ checked : RuntimeOwnerMap.Checked source.initialRoles body.checked.native.block.entry,
        RuntimeInterval.Computed
          (RuntimePureBody.reordered source.initialRoles body.checked.native.block.entry initial.bindings) checked ∧
        ∃ result : Frame body.checked.owners,
          PackedComposition view.prePrimitive view.centerSelection view.postPrimitive held checked result a b c finish := by
  intro held pre center post source initial state finish starts next last covers
  obtain ⟨a,b,c,events,checked,entry,result,action⟩ :=
    original_three_packed body view coverage starts next last covers
  refine ⟨a,b,c,body.checked.native.originalRoot.reader,events,?_,checked,entry,result,action⟩
  intro history
  rw [events]
  exact run_pure body.root.dependencies 64 _ history

#print axioms original_three_observing

/-- Locate the original adjacent interval and evaluate it on each history
emitted by the original prefix. The suffix uses the same interpreter and can
include the final permutation of the enclosing body. -/
theorem interval_histories
    {deps program block s a b c pre choose post preEvents chooseEvents postEvents}
    (result : @RuntimeAdjacentSlices.Three deps program block s a b c pre choose post
      preEvents chooseEvents postEvents)
    (fuel : Nat) (depth : block.fuel = fuel+1) (final : Semantics.RawTrace.Interface)
    (events : List Semantics.Observation.Event)
    (original : Semantics.Observation.readOps (fuel+1) block.entry.quantum.reference
      block.operations = some (final,events)) :
    ∃ earlier later,
      Semantics.Observation.readOps (fuel+1) block.entry.quantum.reference
        (block.operations.take s) = some (pre.interval.before.quantum.reference,earlier) ∧
      Semantics.Observation.readOps (fuel+1) post.interval.after.quantum.reference
        (block.operations.drop (s+(a+b+c))) = some (final,later) ∧
      events = earlier ++ (preEvents++chooseEvents++postEvents).map Semantics.Observation.Event.pure ++ later ∧
      ∀ (tail : List Semantics.Observation.Event) (history : History),
        Qleisli.Semantics.ObservingAction.run deps (fuel+1) (events++tail) history =
          (do
            let inherited ← Qleisli.Semantics.ObservingAction.run deps (fuel+1) earlier history
            (later++tail).foldlM
              (advance deps (Qleisli.Semantics.ObservingAction.run deps fuel))
              (inherited.map (pureHistory deps (preEvents++chooseEvents++postEvents)))) := by
  obtain ⟨work,left,checked⟩ := pre.interval.prefixRead
  rw [depth] at checked
  obtain ⟨earlier,entered⟩ := RuntimeObservingPrefix.checkOps_reference deps (fuel+1)
    block.entry pre.interval.before (block.operations.take s) work left checked
  obtain ⟨later,read,slices⟩ := result.observing_interval fuel block.entry.quantum.reference
    final earlier events entered original
  refine ⟨earlier,later,entered,read,slices,?_⟩
  intro tail history
  rw [slices,List.append_assoc (earlier ++ _) later tail]
  exact run_surround_pure deps fuel earlier (later++tail) _ history

#print axioms interval_histories

/-- An interval in the actual observing root uses the original reader,
prefix check, enclosing continuation, and final output permutation. -/
theorem root_interval_histories {deps program}
    (root : RuntimeInterval.Prepared deps program)
    {s a b c pre choose post preEvents chooseEvents postEvents}
    (result : @RuntimeAdjacentSlices.Three deps program root.block s a b c pre choose post
      preEvents chooseEvents postEvents) :
    ∃ earlier later,
      Semantics.Observation.readOps 65 root.block.entry.quantum.reference
        (root.block.operations.take s) = some (pre.interval.before.quantum.reference,earlier) ∧
      root.whole.prepared.events =
        earlier ++ (preEvents++chooseEvents++postEvents).map Semantics.Observation.Event.pure ++ later ∧
      (s+(a+b+c) = root.block.operations.length →
        root.whole.prepared.state = post.interval.after.quantum.reference ∧
        later = [.pure (readerFinish program root.whole.prepared.state)]) ∧
      ∀ history : History,
        Qleisli.Semantics.ObservingAction.run deps 65 root.whole.prepared.events history =
          (do
            let inherited ← Qleisli.Semantics.ObservingAction.run deps 65 earlier history
            later.foldlM (advance deps (Qleisli.Semantics.ObservingAction.run deps 64))
              (inherited.map (pureHistory deps (preEvents++chooseEvents++postEvents)))) := by
  have actual := root.originalRoot.reader
  unfold Semantics.Observation.read at actual
  cases read : Semantics.Observation.readOps 65 (Semantics.RawTrace.initial program.inputs) program.operations with
  | none => simp only [read,bind,Option.bind] at actual; cases actual
  | some pair =>
    obtain ⟨state,events⟩ := pair
    simp only [read,bind,Option.bind,pure] at actual
    let finish := Semantics.Observation.Event.pure (readerFinish program state)
    have finalState : root.whole.prepared.state = state :=
      congrArg Semantics.Observation.Prepared.state (Option.some.inj actual).symm
    have returned : events++[finish] = root.whole.prepared.events :=
      congrArg Semantics.Observation.Prepared.events (Option.some.inj actual)
    have original : Semantics.Observation.readOps 65 root.entry.quantum.reference
        root.block.operations = some (state,events) := by
      change Semantics.Observation.readOps 65 root.entry.quantum.reference program.operations = _
      rw [(RuntimeNamedFrameAxes.initialized root.inputRead).1]
      exact read
    obtain ⟨earlier,later,entered,rest,slices,histories⟩ :=
      interval_histories result 64 rfl state events original
    refine ⟨earlier,later++[finish],entered,?_,?_,?_⟩
    · rw [← returned,slices,List.append_assoc (earlier ++ _) later]
    · intro ends
      rw [ends,List.drop_length] at rest
      change some (post.interval.after.quantum.reference,[]) = some (state,later) at rest
      have final := Option.some.inj rest
      refine ⟨finalState.trans (congrArg Prod.fst final).symm,?_⟩
      have noSuffix : later = [] := (congrArg Prod.snd final).symm
      rw [noSuffix,List.nil_append]
      exact congrArg (fun state => [Semantics.Observation.Event.pure (readerFinish program state)]) finalState.symm
    · intro history
      rw [← returned]
      exact histories [finish] history

#print axioms root_interval_histories

/-- The actual source interval has the same call actions as the pure event
slice inside the original observing root. The inherited operator columns
can be compared with the explicit source equation in their checked input
frame. The original continuation, including the final reorder, follows. -/
theorem original_adjacent_observing {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime)
    (view : RuntimeNamedThreeOccurrence.Adjacent body.checked.result.steps)
    (coverage : RuntimeNamedSelectionOn.Coverage view.centerSelection
      (RuntimeNamedThreeOccurrence.actual_adjacent_middle body view)) :
    let held := RuntimeNamedThreeOccurrence.actual_adjacent_middle body view
    let pre := RuntimeNamedOccurrenceAction.span view.prePrimitive
    let center := RuntimeNamedSelectionOn.middle view.centerSelection held coverage
    let post := RuntimeNamedOccurrenceAction.span view.postPrimitive
    center.start = pre.start+pre.count → post.start = center.start+center.count →
    ∃ a b c : List Semantics.Raw.Event, ∃ earlier later : List Semantics.Observation.Event,
      Semantics.Observation.readOps 65 body.checked.native.block.entry.quantum.reference
        (body.checked.native.block.operations.take pre.start) =
          some (pre.slice.interval.before.quantum.reference,earlier) ∧
      body.checked.native.whole.prepared.events =
        earlier ++ (a++b++c).map Semantics.Observation.Event.pure ++ later ∧
      (post.start+post.count = body.checked.native.block.operations.length →
        body.checked.native.whole.prepared.state = post.slice.interval.after.quantum.reference ∧
        later = [.pure (readerFinish body.root.program body.checked.native.whole.prepared.state)]) ∧
      RawFiniteRows.BoundedEvents pre.slice.interval.before.quantum.frame.length
        (a++b++c) post.slice.interval.after.quantum.frame.length ∧
      RuntimeNamedThreeFrameChain.Composed view.prePrimitive view.centerSelection view.postPrimitive held a b c ∧
      ∀ history : History,
        Qleisli.Semantics.ObservingAction.run body.root.dependencies 65
          body.checked.native.whole.prepared.events history =
          (do
            let inherited ← Qleisli.Semantics.ObservingAction.run body.root.dependencies 65 earlier history
            later.foldlM
              (advance body.root.dependencies (Qleisli.Semantics.ObservingAction.run body.root.dependencies 64))
              (inherited.map (pureHistory body.root.dependencies (a++b++c)))) := by
  intro held pre center post next last
  change center.start = pre.start+pre.count at next
  change post.start = center.start+center.count at last
  have calls := RuntimeNamedSourceFlow.original_adjacent_calls body view
  cases firstRead : pre with
  | mk firstStart firstCount firstSlice =>
    cases middleRead : center with
    | mk middleStart middleCount middleSlice =>
      cases lastRead : post with
      | mk lastStart lastCount lastSlice =>
        simp only [firstRead,middleRead,lastRead] at next last
        change middleStart = firstStart+firstCount at next
        change lastStart = middleStart+middleCount at last
        subst middleStart
        subst lastStart
        obtain ⟨a,b,c,chain⟩ := RuntimeAdjacentSlices.three firstSlice middleSlice lastSlice
        have preOn := RuntimeNamedOccurrenceAction.on_span view.prePrimitive a (by
          change RuntimeAdjacentSlices.Fold _ pre.slice.ops pre.slice.interval.before.quantum
            pre.slice.interval.after.quantum a
          rw [firstRead]
          exact chain.preFold)
        have centerOn := RuntimeNamedSelectionOn.on_middle view.centerSelection held coverage b (by
          change RuntimeLocalEvents.trace center.slice.interval.before.quantum.reference center.slice.ops =
            some ⟨center.slice.interval.after.quantum.reference,b,center.slice.interval.before.quantum.frame.length⟩
          rw [middleRead]
          exact chain.chooseFold.trace)
        have postOn := RuntimeNamedOccurrenceAction.on_span view.postPrimitive c (by
          change RuntimeAdjacentSlices.Fold _ post.slice.ops post.slice.interval.before.quantum
            post.slice.interval.after.quantum c
          rw [lastRead]
          exact chain.postFold)
        have firstRaw : pre.slice.interval.after = center.slice.interval.before := by
          rw [firstRead,middleRead]
          exact chain.toChoose
        have secondRaw : center.slice.interval.after = post.slice.interval.before := by
          rw [middleRead,lastRead]
          exact chain.toPost
        obtain ⟨earlier,later,entered,events,terminal,histories⟩ :=
          root_interval_histories body.checked.native chain
        have finalRead : firstStart+firstCount+middleCount+lastCount =
            body.checked.native.block.operations.length →
            body.checked.native.whole.prepared.state = lastSlice.interval.after.quantum.reference ∧
            later = [.pure (readerFinish body.root.program body.checked.native.whole.prepared.state)] := by
          intro ends
          exact terminal (by simpa only [Nat.add_assoc] using ends)
        have finite :
            RawFiniteRows.BoundedEvents firstSlice.interval.before.quantum.frame.length
              (a++b++c) lastSlice.interval.after.quantum.frame.length := by
          have firstBounds := RawFiniteRows.checked_slice firstSlice a chain.preFold.trace
          have middleBounds := RawFiniteRows.checked_slice middleSlice b chain.chooseFold.trace
          have lastBounds := RawFiniteRows.checked_slice lastSlice c chain.postFold.trace
          rw [← chain.toChoose] at middleBounds
          rw [← chain.toPost] at lastBounds
          exact (firstBounds.append middleBounds).append lastBounds
        exact ⟨a,b,c,earlier,later,entered,events,finalRead,finite,
          RuntimeNamedThreeFrameChain.compose_sites (fuel := 126)
            view.prePrimitive view.centerSelection view.postPrimitive held coverage
            calls.2.2.1 calls.2.2.2.1 calls.2.2.2.2 a b c preOn centerOn postOn
            calls.1 calls.2.1 firstRaw secondRaw,
          histories⟩

#print axioms original_adjacent_observing

end Qleisli.RuntimeNamedThreePackedInstrument
