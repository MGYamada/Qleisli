import Qleisli.RuntimeNamedThreePackedOutput
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

private noncomputable def advance (dependencies : List Semantics.Finite.Dependency)
    (recurse : List Semantics.Observation.Event → History → Option (List History))
    (histories : List History) (event : Semantics.Observation.Event) : Option (List History) := do
  let groups ← histories.mapM (Qleisli.Semantics.ObservingAction.step dependencies recurse event)
  return groups.flatten

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
    (fuel : Nat) (initial final : Semantics.RawTrace.Interface)
    (earlier events : List Semantics.Observation.Event)
    (entered : Semantics.Observation.readOps (fuel+1) initial (block.operations.take s) =
      some (pre.interval.before.quantum.reference,earlier))
    (original : Semantics.Observation.readOps (fuel+1) initial block.operations = some (final,events)) :
    ∃ later,
      Semantics.Observation.readOps (fuel+1) post.interval.after.quantum.reference
        (block.operations.drop (s+(a+b+c))) = some (final,later) ∧
      ∀ (tail : List Semantics.Observation.Event) (history : History),
        Qleisli.Semantics.ObservingAction.run deps (fuel+1) (events++tail) history =
          (do
            let inherited ← Qleisli.Semantics.ObservingAction.run deps (fuel+1) earlier history
            (later++tail).foldlM
              (advance deps (Qleisli.Semantics.ObservingAction.run deps fuel))
              (inherited.map (pureHistory deps (preEvents++chooseEvents++postEvents)))) := by
  obtain ⟨later,read,slices⟩ := result.observing_interval fuel initial final earlier events entered original
  refine ⟨later,read,?_⟩
  intro tail history
  rw [slices,List.append_assoc (earlier ++ _) later tail]
  exact run_surround_pure deps fuel earlier (later++tail) _ history

#print axioms interval_histories

end Qleisli.RuntimeNamedThreePackedInstrument
