import ProtectedProgram
import Qleisli.RuntimeAdjacentRootAction
import Qleisli.RuntimeNamedThreePackedInstrument

/-! Compose checked clean-workspace actions inside the original observing Raw
program. The independent reader retains prior outcomes, the literal suffix and
the actual final output order. The proof uses the existing QPTL cleanup laws
with checked Raw premises.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.Raw.ProtectedObserving
open QleisliKernel Qirf QleisliKernel.Finite QleisliKernel.Semantics
open QleisliKernel.Raw.Observation (State checkOps checkStep)
open Qleisli.Raw.ProtectedProgram (events_action logicalEvents)
open Qleisli.RuntimeNamedThreePackedInstrument (advance pureHistory run_surround_pure)
open Qleisli.RuntimeNamedThreePackedOutput (readerFinish)
open Qleisli.Semantics.ObservingAction (History run)

private theorem checkedMembers (dependencies : List Semantics.Finite.Dependency)
    (events : List Semantics.Raw.Event) (work left : Nat)
    (ok : (events.foldlM (fun _ event => Raw.Pure.eventCheck dependencies event) ()).run work =
      (.ok (),left)) :
    ∀ event ∈ events, RuntimeInterval.Computed (Raw.Pure.eventCheck dependencies event) () := by
  induction events generalizing work with
  | nil => simp
  | cons event rest ih =>
    simp only [List.foldlM_cons] at ok
    obtain ⟨returned,middle,checked,tail⟩ := bind_success _ _ _ _ _ ok
    cases returned
    intro chosen present
    rcases List.mem_cons.mp present with rfl | present
    · exact ⟨work,middle,checked⟩
    · exact ih middle tail chosen present

/-- Unpack the actual executable step, which checked every pure event
emitted by the literal Raw instruction. -/
private theorem checkedPureStep (dependencies : List Semantics.Finite.Dependency) (fuel : Nat)
    (before after : State) (operation : Semantics.Raw.Op) (work left : Nat)
    (ok : (checkStep dependencies (checkOps dependencies fuel) before (.pure operation)).run work =
      (.ok after,left)) :
    ∃ events : List Semantics.Raw.Event,
      Observation.readOps (fuel+1) before.quantum.reference [.pure operation] =
        some (after.quantum.reference,events.map Observation.Event.pure) ∧
      ∀ event ∈ events, RuntimeInterval.Computed (Raw.Pure.eventCheck dependencies event) () := by
  obtain ⟨_,_,_,rest⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,_,_,rest⟩ := bind_success _ _ _ _ _ rest
  obtain ⟨result,_,body,rest⟩ := bind_success _ _ _ _ _ rest
  obtain ⟨_,_,_,rest⟩ := bind_success _ _ _ _ _ rest
  have exit := (pure_success _ _ _ _ rest).1
  subst after
  obtain ⟨_,_,_,rest⟩ := bind_success _ _ _ _ _ body
  obtain ⟨transition,_,original,rest⟩ := bind_success _ _ _ _ _ rest
  obtain ⟨returned,_,checked,rest⟩ := bind_success _ _ _ _ _ rest
  cases returned
  have same := (pure_success _ _ _ _ rest).1
  subst result
  refine ⟨transition.events,?_,checkedMembers _ _ _ _ checked⟩
  have read := Raw.step_reference _ _ _ _ (lift_success _ _ _ _ original).1
  rw [Raw.ObservationAgreement.read_succ]
  simp [Raw.ObservationAgreement.layer,Raw.ObservationAgreement.readStep,read]

private theorem singletonStep (dependencies : List Semantics.Finite.Dependency)
    (fuel : Nat) (before after : State) (operation : Observation.Op)
    (checked : RuntimeInterval.Computed (checkOps dependencies (fuel+1) before [operation]) after) :
    RuntimeInterval.Computed (checkStep dependencies (checkOps dependencies fuel) before operation) after := by
  obtain ⟨work,left,ok⟩ := checked
  obtain ⟨result,middle,walked,rest⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,_,_,rest⟩ := bind_success _ _ _ _ _ rest
  have same := (pure_success _ _ _ _ rest).1
  subst after
  exact ⟨work,middle,by simpa only [List.foldlM_cons,List.foldlM_nil,bind_pure] using walked⟩

/-- Replace each inherited operator column by the already proved logical
action, keeping all recorded and hidden outcomes. -/
noncomputable def logicalHistory (dependencies : List Semantics.Finite.Dependency)
    (events : List Semantics.Raw.Event) (history : History) : History :=
  {history with operator := fun row col =>
    logicalEvents dependencies events (fun input => history.operator input col) row}

private theorem runWithCheckedCleanup (dependencies : List Semantics.Finite.Dependency) (fuel : Nat)
    (earlier later : List Observation.Event) (events : List Semantics.Raw.Event)
    (history : History)
    (checked : ∀ event ∈ events, RuntimeInterval.Computed (Raw.Pure.eventCheck dependencies event) ()) :
    run dependencies (fuel+1) (earlier ++ events.map Observation.Event.pure ++ later) history =
      (do
        let inherited ← run dependencies (fuel+1) earlier history
        later.foldlM (advance dependencies (run dependencies fuel))
          (inherited.map (logicalHistory dependencies events))) := by
  rw [run_surround_pure]
  have exactHistory : pureHistory dependencies events = logicalHistory dependencies events := by
    funext initial
    simp only [pureHistory,logicalHistory,events_action dependencies events checked]
  rw [exactHistory]

/-- An actual checked pure operation in an accepted observing root can be
evaluated by its exact logical actions. The original prefix supplies every
inherited operator column; the original suffix and return permutation then
consume the same updated histories. -/
theorem original_interval {dependencies program}
    (root : RuntimeInterval.Prepared dependencies program) {start : Nat}
    (interval : RuntimeInterval.Checked root.block start 1) {operation : Semantics.Raw.Op}
    (literal : (program.operations.drop start).take 1 = [.pure operation]) :
    ∃ (earlier : List Observation.Event) (events : List Semantics.Raw.Event) (later : List Observation.Event),
      root.whole.prepared.events = earlier ++ events.map Observation.Event.pure ++ later ∧
      ∀ history : History,
        run dependencies 65 root.whole.prepared.events history =
          (do
            let inherited ← run dependencies 65 earlier history
            later.foldlM (advance dependencies (run dependencies 64))
              (inherited.map (logicalHistory dependencies events))) := by
  obtain ⟨beforeWork,beforeLeft,prefixChecked⟩ := interval.prefixRead
  obtain ⟨earlier,beforeRead⟩ := Qleisli.RuntimeObservingPrefix.checkOps_reference
    dependencies 65 root.entry interval.before (program.operations.take start) beforeWork beforeLeft prefixChecked
  rw [(RuntimeNamedFrameAxes.initialized root.inputRead).1] at beforeRead
  have sliceChecked : RuntimeInterval.Computed
      (checkOps dependencies 65 interval.before [.pure operation]) interval.after := by
    simpa only [RuntimeInterval.Prepared.block,literal] using interval.intervalRead
  obtain ⟨work,left,stepChecked⟩ := singletonStep dependencies 64 interval.before interval.after
    (.pure operation) sliceChecked
  obtain ⟨events,stepRead,checked⟩ :=
    checkedPureStep dependencies 64 interval.before interval.after operation work left stepChecked
  let tail := program.operations.drop (start+1)
  have split : program.operations = (program.operations.take start ++ [.pure operation]) ++ tail := by
    unfold tail
    rw [List.append_assoc,← literal,← List.drop_drop,List.take_append_drop,List.take_append_drop]
  have appendRead (state : Semantics.RawTrace.Interface) (first rest : List Observation.Op) :
      Observation.readOps 65 state (first ++ rest) = (do
        let (middle,firstEvents) ← Observation.readOps 65 state first
        let (last,restEvents) ← Observation.readOps 65 middle rest
        return (last,firstEvents ++ restEvents)) :=
    Qleisli.RuntimeAdjacentSlices.readOps_append 64 state first rest
  change Observation.readOps 65 (Semantics.RawTrace.initial program.inputs)
    (program.operations.take start) = _ at beforeRead
  change Observation.readOps 65 interval.before.quantum.reference [.pure operation] = _ at stepRead
  have original := root.originalRoot.reader
  unfold Observation.read at original
  cases wholeRead : Observation.readOps 65 (Semantics.RawTrace.initial program.inputs) program.operations with
  | none => simp [wholeRead] at original
  | some result =>
    obtain ⟨state,allEvents⟩ := result
    simp only [wholeRead,bind,Option.bind,pure] at original
    rw [split,appendRead,appendRead,beforeRead] at wholeRead
    simp only [bind,Option.bind,pure,stepRead] at wholeRead
    cases suffixRead : Observation.readOps 65 interval.after.quantum.reference tail with
    | none => simp [suffixRead] at wholeRead
    | some result =>
      obtain ⟨last,later⟩ := result
      rw [suffixRead] at wholeRead
      obtain ⟨sameState,sameEvents⟩ := Prod.mk.inj (Option.some.inj wholeRead)
      subst state
      subst allEvents
      let finish := Observation.Event.pure (readerFinish program last)
      have returned : ((earlier ++ events.map Observation.Event.pure) ++ later) ++ [finish] =
          root.whole.prepared.events := congrArg Observation.Prepared.events (Option.some.inj original)
      have trace : root.whole.prepared.events =
          earlier ++ events.map Observation.Event.pure ++ (later ++ [finish]) := by
        rw [← returned,List.append_assoc (earlier ++ _) later]
      exact ⟨earlier,events,later ++ [finish],trace,fun history => by
        rw [trace]
        exact runWithCheckedCleanup dependencies 64 earlier (later ++ [finish]) events history checked⟩

#print axioms original_interval

end Qleisli.Raw.ProtectedObserving
