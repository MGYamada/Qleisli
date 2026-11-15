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

/-- Only the observing reader's administrative pure events can be retained
without a separate pure check. A branch requires independently checked arms. -/
def RetainedEvent : Observation.Event → Prop
  | .pure (.init0 _) => True
  | .pure (.reorder _ _) => True
  | .pure _ | .branch .. => False
  | _ => True

private theorem retainedOfRead {fuel state next operation events}
    (read : Raw.ObservationAgreement.readStep (Observation.readOps fuel) state operation =
      some (next,events)) (observation : ∀ raw, operation ≠ .pure raw)
    (noBranch : ∀ condition left right quantum classical,
      operation ≠ .branch condition left right quantum classical) :
    ∀ event ∈ events, RetainedEvent event := by
  cases operation with
  | pure raw => exact (observation raw rfl).elim
  | constant _ _ | not _ _ | xor _ _ _ | and _ _ _ =>
    have listed : _ = events := congrArg Prod.snd (Option.some.inj read)
    rw [← listed]
    simp [RetainedEvent]
  | measure _ _ | discard _ | reset _ _ _ =>
    obtain ⟨⟨_,_⟩,_,finish⟩ := Option.bind_eq_some_iff.mp read
    have listed : _ = events := congrArg Prod.snd (Option.some.inj finish)
    rw [← listed]
    simp [RetainedEvent]
  | branch condition left right quantum classical =>
    exact (noBranch condition left right quantum classical rfl).elim

/-- A checked observing event. Both branch arms retain their checked subtrees. -/
inductive LogicalStep (dependencies : List Semantics.Finite.Dependency) where
  | pure (event : Semantics.Raw.Event)
      (checked : RuntimeInterval.Computed (Raw.Pure.eventCheck dependencies event) ())
  | retained (event : Observation.Event) (administrative : RetainedEvent event)
  | branch (condition : Nat) (left right : List (LogicalStep dependencies))
      (phis : List Observation.ClassicalPhi)

def LogicalStep.original {dependencies} (step : LogicalStep dependencies) : Observation.Event :=
  match step with
  | .pure event _ => .pure event
  | .retained event _ => event
  | .branch condition left right phis =>
    .branch condition (left.attach.map fun next => next.val.original)
      (right.attach.map fun next => next.val.original) phis
termination_by sizeOf step
decreasing_by
  all_goals
    have smaller := List.sizeOf_lt_of_mem next.property
    simp_wf
    omega

private theorem LogicalStep.original_branch {dependencies} (condition : Nat)
    (left right : List (LogicalStep dependencies)) (phis : List Observation.ClassicalPhi) :
    (LogicalStep.branch condition left right phis).original =
      .branch condition (left.map LogicalStep.original) (right.map LogicalStep.original) phis := by
  rw [LogicalStep.original]
  simp

noncomputable def LogicalStep.apply {dependencies} (fuel : Nat) (histories : List History)
    (step : LogicalStep dependencies) : Option (List History) :=
  match step with
  | .pure event _ => some (histories.map (logicalHistory dependencies [event]))
  | .retained event _ => advance dependencies (run dependencies fuel) histories event
  | .branch condition left right phis =>
    match fuel with
    | 0 => advance dependencies (run dependencies 0) histories step.original
    | depth+1 => do
      let groups ← histories.mapM fun history => do
        let choice ← Qleisli.Semantics.RawInstrument.value history.values condition
        let next ← (if choice then left else right).foldlM (LogicalStep.apply depth) [history]
        next.mapM (Qleisli.Semantics.ObservingAction.merge choice phis)
      return groups.flatten
termination_by fuel

private theorem advanceLogicalPure {dependencies} (fuel : Nat)
    (histories : List History) (event : Semantics.Raw.Event)
    (checked : RuntimeInterval.Computed (Raw.Pure.eventCheck dependencies event) ()) :
    advance dependencies (run dependencies fuel) histories (.pure event) =
      some (histories.map (logicalHistory dependencies [event])) := by
  have checks : ∀ other ∈ [event], RuntimeInterval.Computed (Raw.Pure.eventCheck dependencies other) () := by
    intro other mem
    rw [List.mem_singleton.mp mem]
    exact checked
  have same : pureHistory dependencies [event] = logicalHistory dependencies [event] := by
    funext initial
    simp only [pureHistory,logicalHistory,events_action dependencies [event] checks]
  rw [Qleisli.RuntimeNamedThreePackedInstrument.advance_pure, same]

private theorem LogicalStep.apply_original {dependencies} (fuel : Nat) :
    ∀ (histories : List History) (step : LogicalStep dependencies),
      advance dependencies (run dependencies fuel) histories step.original = step.apply fuel histories := by
  induction fuel with
  | zero =>
    intro histories step
    cases step with
    | pure event proof => simpa only [LogicalStep.original,LogicalStep.apply] using advanceLogicalPure 0 histories event proof
    | retained event _ => simp only [LogicalStep.original,LogicalStep.apply]
    | branch _ _ _ _ => simp only [LogicalStep.apply]
  | succ fuel ih =>
    intro histories step
    cases step with
    | pure event proof => simpa only [LogicalStep.original,LogicalStep.apply] using advanceLogicalPure (fuel+1) histories event proof
    | retained event _ => simp only [LogicalStep.original,LogicalStep.apply]
    | branch condition left right phis =>
      have armRun (steps : List (LogicalStep dependencies)) (initial : History) :
          run dependencies (fuel+1) (steps.map LogicalStep.original) initial =
            steps.foldlM (LogicalStep.apply fuel) [initial] := by
        change (steps.map LogicalStep.original).foldlM (advance dependencies (run dependencies fuel)) [initial] = _
        rw [List.foldlM_map]
        congr 1
        funext h s
        exact ih h s
      have one (history : History) :
          Qleisli.Semantics.ObservingAction.step dependencies (run dependencies (fuel+1))
            (.branch condition (left.map LogicalStep.original) (right.map LogicalStep.original) phis) history =
          (do
            let choice ← Qleisli.Semantics.RawInstrument.value history.values condition
            let next ← (if choice then left else right).foldlM (LogicalStep.apply fuel) [history]
            next.mapM (Qleisli.Semantics.ObservingAction.merge choice phis)) := by
        simp only [Qleisli.Semantics.ObservingAction.step]
        cases found : Qleisli.Semantics.RawInstrument.value history.values condition with
        | none => rfl
        | some choice => cases choice <;> simp [armRun]
      simp only [LogicalStep.original_branch,LogicalStep.apply,advance]
      rw [funext one]

private def ReadsChecked (dependencies : List Semantics.Finite.Dependency) (fuel : Nat) : Prop :=
    ∀ (before after : State) (operations : List Observation.Op) (work left : Nat),
      (checkOps dependencies (fuel+1) before operations).run work = (.ok after,left) →
      ∃ steps : List (LogicalStep dependencies),
        Observation.readOps (fuel+1) before.quantum.reference operations =
          some (after.quantum.reference,steps.map LogicalStep.original)

private theorem readSingleton {fuel state next operation events}
    (read : Raw.ObservationAgreement.readStep (Observation.readOps fuel) state operation =
      some (next,events)) : Observation.readOps (fuel+1) state [operation] = some (next,events) := by
  rw [Raw.ObservationAgreement.read_succ]
  simp only [Raw.ObservationAgreement.layer,List.foldlM_cons,List.foldlM_nil]
  rw [read]
  rfl

private theorem literalBranch {dependencies fuel before after work left}
    (recurse : ∀ child, fuel = child+1 → ReadsChecked dependencies child)
    (condition : Nat) (thenOps elseOps : List Observation.Op) (quantum : List Observation.QuantumPhi)
    (classical : List Observation.ClassicalPhi)
    (ok : (checkStep dependencies (checkOps dependencies fuel) before
      (.branch condition thenOps elseOps quantum classical)).run work = (.ok after,left)) :
    ∃ steps : List (LogicalStep dependencies),
      Observation.readOps (fuel+1) before.quantum.reference [.branch condition thenOps elseOps quantum classical] =
        some (after.quantum.reference,steps.map LogicalStep.original) := by
  obtain ⟨_,_,_,checked⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,_,_,checked⟩ := bind_success _ _ _ _ _ checked
  obtain ⟨_,_,body,_⟩ := bind_success _ _ _ _ _ checked
  obtain ⟨_,_,_,body⟩ := bind_success _ _ _ _ _ body
  obtain ⟨_,thenWork,_,body⟩ := bind_success _ _ _ _ _ body
  obtain ⟨thenState,thenLeft,thenChecked,body⟩ := bind_success _ _ _ _ _ body
  obtain ⟨elseState,elseLeft,elseChecked,_⟩ := bind_success _ _ _ _ _ body
  cases fuel with
  | zero => cases thenChecked
  | succ depth =>
    obtain ⟨first,firstRead⟩ := recurse depth rfl _ _ thenOps thenWork thenLeft thenChecked
    obtain ⟨second,secondRead⟩ := recurse depth rfl _ _ elseOps thenLeft elseLeft elseChecked
    change Observation.readOps (depth+1) before.quantum.reference thenOps =
      some (thenState.quantum.reference,first.map LogicalStep.original) at firstRead
    change Observation.readOps (depth+1) before.quantum.reference elseOps =
      some (elseState.quantum.reference,second.map LogicalStep.original) at secondRead
    let finish (arm : Semantics.RawTrace.Interface) (choice : Bool) : Semantics.Raw.Event :=
      .reorder arm.frame.length (Semantics.RawTrace.axes arm (Observation.phiWires arm quantum choice))
    let steps : List (LogicalStep dependencies) :=
      [.branch condition (first ++ [.retained (.pure (finish thenState.quantum.reference true)) trivial])
        (second ++ [.retained (.pure (finish elseState.quantum.reference false)) trivial]) classical]
    have actual : Raw.ObservationAgreement.readStep (Observation.readOps (depth+1)) before.quantum.reference
        (.branch condition thenOps elseOps quantum classical) =
      some (Observation.phiInterface quantum,steps.map LogicalStep.original) := by
      simp [Raw.ObservationAgreement.readStep,firstRead,secondRead,steps,LogicalStep.original_branch,LogicalStep.original,finish]
    obtain ⟨_,events,read,_⟩ := Qleisli.RuntimeObservingPrefix.checkStep_reference_with_writes
      dependencies (depth+1) before after _ work left ok
    have same := (Prod.mk.inj (Option.some.inj (read.symm.trans actual))).1
    exact ⟨steps,readSingleton (same ▸ actual)⟩

private theorem literalStep {dependencies fuel before after operation work left}
    (recurse : ∀ child, fuel = child+1 → ReadsChecked dependencies child)
    (ok : (checkStep dependencies (checkOps dependencies fuel) before operation).run work =
      (.ok after,left)) :
    ∃ steps : List (LogicalStep dependencies),
      Observation.readOps (fuel+1) before.quantum.reference [operation] =
        some (after.quantum.reference,steps.map LogicalStep.original) := by
  cases operation
  case pure operation =>
    obtain ⟨events,read,checked⟩ := checkedPureStep dependencies fuel before after operation work left ok
    let steps : List (LogicalStep dependencies) := events.attach.map fun event =>
      .pure event.val (checked event.val event.property)
    refine ⟨steps,?_⟩
    have same : steps.map LogicalStep.original = events.map Observation.Event.pure := by
      simp [steps,List.map_map,Function.comp_def,LogicalStep.original]
    rw [same]
    exact read
  case branch condition thenOps elseOps quantum classical =>
    exact literalBranch recurse condition thenOps elseOps quantum classical ok
  all_goals
    obtain ⟨_,events,read,_⟩ := Qleisli.RuntimeObservingPrefix.checkStep_reference_with_writes
      dependencies fuel before after _ work left ok
    have administrative := retainedOfRead read (by intro raw equal; cases equal)
      (by intro condition left right quantum classical equal; cases equal)
    let steps : List (LogicalStep dependencies) := events.attach.map fun event =>
      .retained event.val (administrative event.val event.property)
    refine ⟨steps,?_⟩
    have same : steps.map LogicalStep.original = events := by
      simp [steps,List.map_map,Function.comp_def,LogicalStep.original]
    rw [same]
    exact readSingleton read

private theorem literalFold {dependencies fuel}
    (recurse : ∀ child, fuel = child+1 → ReadsChecked dependencies child) (operations : List Observation.Op)
    (before after : State) (work left : Nat)
    (ok : (operations.foldlM (checkStep dependencies (checkOps dependencies fuel)) before).run work =
      (.ok after,left)) :
    ∃ steps : List (LogicalStep dependencies),
      Observation.readOps (fuel+1) before.quantum.reference operations =
        some (after.quantum.reference,steps.map LogicalStep.original) := by
  induction operations generalizing before work with
  | nil =>
    have same := (pure_success _ _ _ _ ok).1
    subst after
    exact ⟨[],rfl⟩
  | cons operation rest ih =>
    simp only [List.foldlM_cons] at ok
    obtain ⟨middle,next,first,later⟩ := bind_success _ _ _ _ _ ok
    obtain ⟨firstSteps,prefixRead⟩ := literalStep recurse first
    obtain ⟨suffix,suffixRead⟩ := ih middle next later
    refine ⟨firstSteps ++ suffix,?_⟩
    change Observation.readOps (fuel+1) before.quantum.reference ([operation] ++ rest) = _
    rw [Qleisli.RuntimeAdjacentSlices.readOps_append,prefixRead]
    simp only [bind,Option.bind,pure,suffixRead,List.map_append]

private theorem literalOps {dependencies} (fuel : Nat) : ReadsChecked dependencies fuel := by
  induction fuel with
  | zero =>
    intro before after operations work left ok
    obtain ⟨result,afterFold,folded,finished⟩ := bind_success _ _ _ _ _ ok
    obtain ⟨_,_,_,finished⟩ := bind_success _ _ _ _ _ finished
    have same := (pure_success _ _ _ _ finished).1
    subst after
    exact literalFold (fun child impossible => by cases impossible) operations before result work afterFold folded
  | succ fuel ih =>
    intro before after operations work left ok
    obtain ⟨result,afterFold,folded,finished⟩ := bind_success _ _ _ _ _ ok
    obtain ⟨_,_,_,finished⟩ := bind_success _ _ _ _ _ finished
    have same := (pure_success _ _ _ _ finished).1
    subst after
    exact literalFold (fun child equal => Nat.succ.inj equal ▸ ih) operations before result work afterFold folded

private theorem literalRun {dependencies} (fuel : Nat) (steps : List (LogicalStep dependencies))
    (initial : History) :
    run dependencies (fuel+1) (steps.map LogicalStep.original) initial =
      steps.foldlM (LogicalStep.apply fuel) [initial] := by
  change (steps.map LogicalStep.original).foldlM (advance dependencies (run dependencies fuel)) [initial] = _
  rw [List.foldlM_map]
  congr 1
  funext histories step
  exact LogicalStep.apply_original fuel histories step

/-- Run the entire independently accepted observing root using its checked
logical pure events through both checked branches, with original outcomes and output order. -/
theorem original_program {dependencies program} (root : RuntimeInterval.Prepared dependencies program) :
    ∃ steps : List (LogicalStep dependencies),
      root.whole.prepared.events = steps.map LogicalStep.original ∧
      ∀ initial : History, run dependencies 65 root.whole.prepared.events initial =
        steps.foldlM (LogicalStep.apply 64) [initial] := by
  obtain ⟨work,left,accepted⟩ := root.verified
  obtain ⟨_,initialWork,_,accepted⟩ := bind_success _ _ _ _ _ accepted
  obtain ⟨quantum,afterQuantum,quantumRead,accepted⟩ := bind_success _ _ _ _ _ accepted
  obtain ⟨entry,before,entryRead,accepted⟩ := bind_success _ _ _ _ _ accepted
  obtain ⟨after,middle,checked,accepted⟩ := bind_success _ _ _ _ _ accepted
  obtain ⟨steps,read⟩ := literalOps 64 _ _ _ _ _ checked
  have entryReference : entry.quantum.reference = Semantics.RawTrace.initial program.inputs := by
    have initialized : RuntimeInterval.Computed (PureInterval.initial program) entry := by
      refine ⟨initialWork,before,?_⟩
      unfold PureInterval.initial
      rw [bind_run,quantumRead]
      exact entryRead
    exact (RuntimeNamedFrameAxes.initialized initialized).1
  rw [entryReference] at read
  let finish := readerFinish program after.quantum.reference
  have trace := root.originalRoot.reader
  unfold Observation.read at trace
  dsimp only at trace
  change Observation.readOps 65 (Semantics.RawTrace.initial program.inputs) program.operations = _ at read
  rw [read] at trace
  change some _ = some root.whole.prepared at trace
  have events := congrArg Observation.Prepared.events (Option.some.inj trace)
  let complete := steps ++ [.retained (.pure finish) trivial]
  have same : root.whole.prepared.events = complete.map LogicalStep.original := by
    rw [← events,List.map_append]
    simp only [List.map_cons,List.map_nil,LogicalStep.original]
    rfl
  exact ⟨complete,same,fun initial => by rw [same]; exact literalRun 64 complete initial⟩

#print axioms original_program

end Qleisli.Raw.ProtectedObserving
