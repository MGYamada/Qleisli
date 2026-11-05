import Qleisli.RuntimeNamedThreePackedInstrument
import Qleisli.RuntimeOriginalObservation

/-! The original destructive observation and the immediately following named
call share their entire Raw state and source owner map. Its retained output
frame supplies the exact input encoding for every emitted history.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeNamedObservationEntry
open QleisliKernel QleisliKernel.Qirf
open QleisliKernel.Qirf.RuntimeForestCode (Frame OwnerCode forestAxes)
open Qleisli.Semantics.ObservingAction (History)
open Qleisli.RuntimeNamedThreePackedInstrument (advance pureHistory)
open Qleisli.RuntimeNamedThreeFrameChain (checkedAt frameAt ComposedAt originalBindings PostFrame EncodedOperator encodePost)
open Qleisli.RuntimeNamedSourceFlow (entryState)
open Qleisli.RuntimeForestProduct (referenceAction)
open Qleisli.RuntimeNamedThreePackedOutput (FinishCaller packedCallerReturn)

def Entry {sources caller dependencies program functionName event block position previous step}
    (observed : @RuntimeObservationAction.Checked sources caller dependencies program functionName
      event block position previous)
    (pre : @RuntimeNamedPrimitiveOccurrence.Occurrence dependencies program block step) : Prop :=
  match pre with
  | .named (scope := scope) (before := before) _ _ =>
    ∃ same : observed.interval.after = scope.interval.before,
      (checkedAt same observed.after).bindings = before.bindings

private theorem entry {sources caller dependencies program functionName event block position previous step}
    (observed : @RuntimeObservationAction.Checked sources caller dependencies program functionName
      event block position previous)
    (pre : @RuntimeNamedPrimitiveOccurrence.Occurrence dependencies program block step)
    (source : (entryState step).map (·.bindings) = some observed.after.bindings)
    (next : (RuntimeNamedOccurrenceAction.span pre).start = position.start+position.count) :
    Entry observed pre := by
  cases pre with
  | @named start count inputs sources caller before childHistory childRetired ordinary first size inputToken outputToken role kind
      event scope body read boundary finalOrdinary primitive original bound =>
    change some before.bindings = some observed.after.bindings at source
    change start = position.start+position.count at next
    subst start
    have same := RuntimeAdjacentSlices.adjacent observed.interval scope.interval
    exact ⟨same,(RuntimeNamedThreeFrameChain.checkedAt_bindings same observed.after).trans
      (Option.some.inj source).symm⟩

/-- A stored source observation immediately preceding the adjacent calls
provides the actual entry map and native state of the first call. -/
theorem original_entry {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime)
    (view : RuntimeNamedThreeOccurrence.Adjacent body.checked.result.steps)
    {rootOwner rootName caller functionName path event position before ssa}
    (observed : @RuntimeOrdinaryBody.Observation artifact.sources rootOwner rootName caller functionName
      body.root.dependencies body.root.program path event body.checked.native.block position before ssa)
    (earlier : List (RuntimePureBody.Step body.root.dependencies body.root.program body.checked.native.block))
    (prefixShape : view.earlier = earlier ++ [.observation observed])
    (next : (RuntimeNamedOccurrenceAction.span view.prePrimitive).start = position.start+position.count) :
    Entry observed.checked view.prePrimitive := by
  have join := RuntimeNamedSourceFlow.original_observation_join body view observed earlier prefixShape
  exact entry observed.checked view.prePrimitive (congrArg (Option.map (·.bindings)) join.symm) next

#print axioms original_entry

/-- Run the original erasure on a represented history and account for every
visible and hidden outcome. The continuation describes the use of each
unnormalized projected operator. -/
def OutcomeHistories {sources caller dependencies program functionName event block position previous}
    (observed : @RuntimeObservationAction.Checked sources caller dependencies program functionName
      event block position previous) (input : Frame observed.before) (consumed : OwnerCode observed.input)
    (continues : (Nat → Nat → ℂ) → History → Prop) : Prop :=
  let raw := observed.interval.before.quantum.reference
  let axes := observed.input.port.wires.map raw.frame.idxOf
  let erasure := Semantics.Observation.Event.erase raw.frame.length axes observed.measured
  ∀ (recurse : List Semantics.Observation.Event → History → Option (List History))
    (joint : Nat → Nat → ℂ) (history : History),
    (∀ col, RawFiniteRows.OnRows raw.frame.length (fun row => history.operator row col)
      (fun row => referenceAction input joint row col)) →
    ∃ branch : Nat → History,
      Qleisli.Semantics.ObservingAction.step dependencies recurse erasure history =
        some ((List.range (2^axes.length)).map branch) ∧
      ∀ outcome, outcome < 2^axes.length →
        (branch outcome).values = (match observed.measured with
          | none => history.values
          | some id => history.values++[(id,outcome == 1)]) ∧
        (branch outcome).hidden = history.hidden++[outcome] ∧
        continues (RuntimeOriginalObservation.outcomeJoint consumed outcome joint) (branch outcome)

theorem OutcomeHistories.imp {sources caller dependencies program functionName event block position previous}
    {observed : @RuntimeObservationAction.Checked sources caller dependencies program functionName
      event block position previous} {input : Frame observed.before} {consumed : OwnerCode observed.input}
    {continues next : (Nat → Nat → ℂ) → History → Prop}
    (histories : OutcomeHistories observed input consumed continues)
    (implies : ∀ projected branch, continues projected branch → next projected branch) :
    OutcomeHistories observed input consumed next := by
  intro recurse joint history represented
  obtain ⟨branch,read,law⟩ := histories recurse joint history represented
  refine ⟨branch,read,?_⟩
  intro outcome bounded
  obtain ⟨visible,hidden,acts⟩ := law outcome bounded
  exact ⟨visible,hidden,implies _ _ acts⟩

/-- Every original erasure outcome supplies the checked first call's frame. -/
def SuppliedHistories {sources caller dependencies program functionName event block position previous step}
    (observed : @RuntimeObservationAction.Checked sources caller dependencies program functionName
      event block position previous)
    (pre : @RuntimeNamedPrimitiveOccurrence.Occurrence dependencies program block step)
    (input : Frame observed.before) : Prop :=
  let entry := (RuntimeNamedOccurrenceAction.span pre).slice.interval.before
  ∃ same : observed.interval.after = entry,
  ∃ consumed : OwnerCode observed.input, ∃ output : Frame observed.after,
    (checkedAt same observed.after).bindings = originalBindings pre ∧
    OutcomeHistories observed input consumed (fun projected branch =>
      ∀ col, RawFiniteRows.OnRows entry.quantum.frame.length
        (fun row => branch.operator row col)
        (fun row => referenceAction (frameAt same output) projected row col))

private theorem supply {sources caller dependencies program functionName event block position previous step}
    (observed : @RuntimeObservationAction.Checked sources caller dependencies program functionName
      event block position previous)
    (pre : @RuntimeNamedPrimitiveOccurrence.Occurrence dependencies program block step)
    (joined : Entry observed pre) (input : Frame observed.before) :
    SuppliedHistories observed pre input := by
  cases pre
  obtain ⟨same,bindings⟩ := joined
  obtain ⟨_read,_value,consumed,output,law⟩ :=
    RuntimeOriginalObservation.original_observation_histories observed input
  refine ⟨same,consumed,output,bindings,?_⟩
  intro recurse joint history represented
  obtain ⟨branch,emitted,branches⟩ := law recurse joint history
    (fun row bounded col => represented col row bounded)
  refine ⟨branch,emitted,?_⟩
  intro outcome outcomeBound
  obtain ⟨visible,hidden,encoded⟩ := branches outcome outcomeBound
  refine ⟨visible,hidden,?_⟩
  intro col row rowBound
  dsimp only
  rw [RuntimeNamedThreeFrameChain.frameAt_action]
  have bound := (congrArg (fun state => row < 2^state.quantum.frame.length) same).mpr rowBound
  exact encoded row bound col

theorem original_supplies_histories {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime)
    (view : RuntimeNamedThreeOccurrence.Adjacent body.checked.result.steps)
    {rootOwner rootName caller functionName path event position before ssa}
    (observed : @RuntimeOrdinaryBody.Observation artifact.sources rootOwner rootName caller functionName
      body.root.dependencies body.root.program path event body.checked.native.block position before ssa)
    (earlier : List (RuntimePureBody.Step body.root.dependencies body.root.program body.checked.native.block))
    (prefixShape : view.earlier = earlier ++ [.observation observed])
    (next : (RuntimeNamedOccurrenceAction.span view.prePrimitive).start = position.start+position.count)
    (input : Frame observed.checked.before) :
    SuppliedHistories observed.checked view.prePrimitive input :=
  supply observed.checked view.prePrimitive
    (original_entry body view observed earlier prefixShape next) input

#print axioms original_supplies_histories

/-- Instantiate the typed three-call equation on all outcomes of this
original erasure, with the original pre-call map and frame. -/
def ObservedCompositionWith {sources caller dependencies program functionName event block position previous
    preStep centerStep postStep rootItem rootCount}
    {witness : @RuntimeSelectionSteps.Witness dependencies rootItem rootCount}
    (observed : @RuntimeObservationAction.Checked sources caller dependencies program functionName
      event block position previous)
    (pre : @RuntimeNamedPrimitiveOccurrence.Occurrence dependencies program block preStep)
    (center : @RuntimeNamedThreeOccurrence.Middle dependencies program block centerStep)
    (post : @RuntimeNamedPrimitiveOccurrence.Occurrence dependencies program block postStep)
    (held : RuntimeNamedThreeOccurrence.RetainedData witness center)
    (input : Frame observed.before)
    (continues : PostFrame post → EncodedOperator → (Nat → Nat → ℂ) → History → Prop) : Prop :=
  ∃ same : observed.interval.after = (RuntimeNamedOccurrenceAction.span pre).slice.interval.before,
  ∃ consumed : OwnerCode observed.input, ∃ retained : Frame observed.after,
    (checkedAt same observed.after).bindings = originalBindings pre ∧
    ComposedAt pre center post held (frameAt same retained) (fun caller logical =>
      OutcomeHistories observed input consumed (continues caller logical))

/-- The original three pure calls act on each unnormalized projected state
in the actual post-call frame and preserve its outcome records. -/
def ObservedComposition {sources caller dependencies program functionName event block position previous
    preStep centerStep postStep rootItem rootCount}
    {witness : @RuntimeSelectionSteps.Witness dependencies rootItem rootCount}
    (observed : @RuntimeObservationAction.Checked sources caller dependencies program functionName
      event block position previous)
    (pre : @RuntimeNamedPrimitiveOccurrence.Occurrence dependencies program block preStep)
    (center : @RuntimeNamedThreeOccurrence.Middle dependencies program block centerStep)
    (post : @RuntimeNamedPrimitiveOccurrence.Occurrence dependencies program block postStep)
    (held : RuntimeNamedThreeOccurrence.RetainedData witness center)
    (input : Frame observed.before) (events : List Semantics.Raw.Event) : Prop :=
  ObservedCompositionWith observed pre center post held input (fun caller logical projected branch =>
    let after := pureHistory dependencies events branch
    after.values = branch.values ∧ after.hidden = branch.hidden ∧
    ∀ col, RawFiniteRows.OnRows (RuntimeNamedOccurrenceAction.span post).slice.interval.after.quantum.frame.length
      (fun row => after.operator row col) (fun row => encodePost post caller (logical projected) row col))

private theorem compose_observation {sources caller dependencies program functionName event block position previous
    preStep centerStep postStep rootItem rootCount}
    {witness : @RuntimeSelectionSteps.Witness dependencies rootItem rootCount}
    (observed : @RuntimeObservationAction.Checked sources caller dependencies program functionName
      event block position previous)
    (pre : @RuntimeNamedPrimitiveOccurrence.Occurrence dependencies program block preStep)
    (center : @RuntimeNamedThreeOccurrence.Middle dependencies program block centerStep)
    (post : @RuntimeNamedPrimitiveOccurrence.Occurrence dependencies program block postStep)
    (held : RuntimeNamedThreeOccurrence.RetainedData witness center)
    (input : Frame observed.before) (a b c : List Semantics.Raw.Event)
    (supplied : SuppliedHistories observed pre input)
    (bounds : RawFiniteRows.BoundedEvents (RuntimeNamedOccurrenceAction.span pre).slice.interval.before.quantum.frame.length
      (a++b++c) (RuntimeNamedOccurrenceAction.span post).slice.interval.after.quantum.frame.length)
    (chain : RuntimeNamedThreeFrameChain.Composed pre center post held a b c) :
    ObservedComposition observed pre center post held input (a++b++c) := by
  obtain ⟨same,consumed,retained,bindings,histories⟩ := supplied
  refine ⟨same,consumed,retained,bindings,(chain _ (frameAt same retained) bindings).imp ?_⟩
  intro caller logical acts
  apply histories.imp
  intro projected branch represented
  refine ⟨rfl,rfl,?_⟩
  intro col row bounded
  have transported := Qleisli.RuntimeNamedThreePackedInstrument.pureHistory_operator_congr bounds
    dependencies branch (referenceAction (frameAt same retained) projected) represented col row bounded
  exact transported.trans (acts projected row col)

/-- Compare the actual returned history with the packed source result after
applying the original return order to the post-call logical state. -/
def PackedOutcomeAction {dependencies program block postStep roles state checked}
    (post : @RuntimeNamedPrimitiveOccurrence.Occurrence dependencies program block postStep)
    (output : @Frame roles state checked) (events : List Semantics.Raw.Event) (finish : Semantics.Raw.Event)
    (caller : PostFrame post) (logical : EncodedOperator) (projected : Nat → Nat → ℂ) (branch : History) : Prop :=
  let after := pureHistory dependencies (events++[finish]) branch
  after.values = branch.values ∧ after.hidden = branch.hidden ∧
  ∀ col, RawFiniteRows.OnRows state.quantum.frame.length
    (fun row => after.operator row col) (fun row => packedCallerReturn post output caller (logical projected) row col)

private theorem packed_outcomes {sources caller dependencies program functionName event block position previous
    preStep centerStep postStep rootItem rootCount roles state checked}
    {witness : @RuntimeSelectionSteps.Witness dependencies rootItem rootCount}
    (observed : @RuntimeObservationAction.Checked sources caller dependencies program functionName
      event block position previous)
    (pre : @RuntimeNamedPrimitiveOccurrence.Occurrence dependencies program block preStep)
    (center : @RuntimeNamedThreeOccurrence.Middle dependencies program block centerStep)
    (post : @RuntimeNamedPrimitiveOccurrence.Occurrence dependencies program block postStep)
    (held : RuntimeNamedThreeOccurrence.RetainedData witness center)
    (input : Frame observed.before) (events : List Semantics.Raw.Event)
    (composition : ObservedComposition observed pre center post held input events)
    (output : @Frame roles state checked) (axes : List Nat)
    (physical : state.quantum.frame = (RuntimeNamedOccurrenceAction.span post).slice.interval.after.quantum.frame)
    (finish : FinishCaller post output (.reorder state.quantum.frame.length axes)) :
    ObservedCompositionWith observed pre center post held input
      (PackedOutcomeAction post output events (.reorder state.quantum.frame.length axes)) := by
  obtain ⟨same,consumed,retained,bindings,law⟩ := composition
  refine ⟨same,consumed,retained,bindings,law.imp ?_⟩
  intro caller logical each
  apply each.imp
  intro projected branch encoded
  obtain ⟨_values,_hidden,encoded⟩ := encoded
  refine ⟨rfl,rfl,?_⟩
  intro col row bounded
  have columns : RawFiniteRows.OnRows state.quantum.frame.length
      (fun row => (pureHistory dependencies events branch).operator row col)
      (fun row => encodePost post caller (logical projected) row col) := by
    rw [congrArg List.length physical]
    exact encoded col
  have matched := (RawFiniteRows.BoundedEvent.reorder state.quantum.frame.length axes).congr
    dependencies _ _ columns row bounded
  change Qleisli.Semantics.RawAction.events dependencies (events++[.reorder state.quantum.frame.length axes])
    (fun physical => branch.operator physical col) row = _
  simp only [Qleisli.Semantics.RawAction.events,List.foldl_append,List.foldl_cons,List.foldl_nil]
  exact matched.trans (finish caller (logical projected) row bounded col)

/-- The original prefix at the first call ends in the checked erasure. -/
theorem prefix_erasure {sources caller dependencies program functionName event block position previous start count}
    (observed : @RuntimeObservationAction.Checked sources caller dependencies program functionName
      event block position previous)
    (pre : RuntimeInterval.Checked block start count)
    (next : start = position.start+position.count)
    (events : List Semantics.Observation.Event)
    (read : Semantics.Observation.readOps block.fuel block.entry.quantum.reference
      (block.operations.take start) = some (pre.before.quantum.reference,events)) :
    let state := observed.interval.before.quantum.reference
    let axes := observed.input.port.wires.map state.frame.idxOf
    ∃ prefixEvents,
      Semantics.Observation.readOps block.fuel block.entry.quantum.reference
        (block.operations.take position.start) = some (state,prefixEvents) ∧
      events = prefixEvents ++ [.erase state.frame.length axes observed.measured] := by
  subst start
  obtain ⟨work,left,checked⟩ := observed.interval.prefixRead
  obtain ⟨prefixEvents,prefixRead⟩ := RuntimeObservingPrefix.checkOps_reference dependencies
    block.fuel block.entry observed.interval.before (block.operations.take position.start) work left checked
  have erasure := (RuntimeOriginalObservation.original_erasure observed).1
  have positive : ∃ fuel, block.fuel = fuel+1 := by
    cases depth : block.fuel with
    | zero => rw [depth] at checked; cases checked
    | succ fuel => exact ⟨fuel,rfl⟩
  obtain ⟨fuel,depth⟩ := positive
  rw [RuntimeAdjacentSlices.prefixSplit,depth,RuntimeAdjacentSlices.readOps_append] at read
  rw [depth] at prefixRead erasure
  rw [prefixRead] at read
  simp only [bind,Option.bind] at read
  rw [erasure] at read
  exact ⟨prefixEvents,by rw [depth]; exact prefixRead,congrArg Prod.snd (Option.some.inj read).symm⟩

#print axioms prefix_erasure
/-- The original source erasure directly precedes the pure call chain in the
original observing program. Every incoming history takes the actual erasure
step, then every emitted history takes the original three-call action and
the original continuation. -/
theorem original_erasure_then_adjacent {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime)
    (view : RuntimeNamedThreeOccurrence.Adjacent body.checked.result.steps)
    {rootOwner rootName caller functionName path event position before ssa}
    (observed : @RuntimeOrdinaryBody.Observation artifact.sources rootOwner rootName caller functionName
      body.root.dependencies body.root.program path event body.checked.native.block position before ssa)
    (earlier : List (RuntimePureBody.Step body.root.dependencies body.root.program body.checked.native.block))
    (prefixShape : view.earlier = earlier ++ [.observation observed])
    (input : Frame observed.checked.before)
    (coverage : RuntimeNamedSelectionOn.Coverage view.centerSelection
      (RuntimeNamedThreeOccurrence.actual_adjacent_middle body view)) :
    let held := RuntimeNamedThreeOccurrence.actual_adjacent_middle body view
    let pre := RuntimeNamedOccurrenceAction.span view.prePrimitive
    let center := RuntimeNamedSelectionOn.middle view.centerSelection held coverage
    let post := RuntimeNamedOccurrenceAction.span view.postPrimitive
    let state := observed.checked.interval.before.quantum.reference
    let axes := observed.checked.input.port.wires.map state.frame.idxOf
    let erasure := Semantics.Observation.Event.erase state.frame.length axes observed.checked.measured
    pre.start = position.start+position.count →
    center.start = pre.start+pre.count → post.start = center.start+center.count →
    ∃ a b c : List Semantics.Raw.Event, ∃ priorEvents suffix : List Semantics.Observation.Event,
      Semantics.Observation.readOps 65 body.checked.native.block.entry.quantum.reference
        (body.checked.native.block.operations.take position.start) = some (state,priorEvents) ∧
      body.checked.native.whole.prepared.events =
        (priorEvents++[erasure]) ++ (a++b++c).map Semantics.Observation.Event.pure ++ suffix ∧
      ObservedComposition observed.checked view.prePrimitive view.centerSelection view.postPrimitive
        held input (a++b++c) ∧
      (view.later = [] → post.start+post.count = body.checked.native.block.operations.length →
        let state := body.checked.native.whole.state
        let finish := Semantics.Raw.Event.reorder state.quantum.frame.length
          (forestAxes state.quantum.frame body.checked.owners.bindings)
        ∃ output : Frame body.checked.owners, suffix = [.pure finish] ∧
          ObservedCompositionWith observed.checked view.prePrimitive view.centerSelection view.postPrimitive
            held input (PackedOutcomeAction view.postPrimitive output (a++b++c) finish) ∧
          ∀ history : History,
            Qleisli.Semantics.ObservingAction.run body.root.dependencies 65
              body.checked.native.whole.prepared.events history =
              (do
                let inherited ← Qleisli.Semantics.ObservingAction.run body.root.dependencies 65 priorEvents history
                let erased ← advance body.root.dependencies
                  (Qleisli.Semantics.ObservingAction.run body.root.dependencies 64) inherited erasure
                return erased.map (pureHistory body.root.dependencies (a++b++c++[finish])))) ∧
      ∀ history : History,
        Qleisli.Semantics.ObservingAction.run body.root.dependencies 65
          body.checked.native.whole.prepared.events history =
          (do
            let inherited ← Qleisli.Semantics.ObservingAction.run body.root.dependencies 65 priorEvents history
            let erased ← advance body.root.dependencies
              (Qleisli.Semantics.ObservingAction.run body.root.dependencies 64) inherited erasure
            suffix.foldlM
              (advance body.root.dependencies (Qleisli.Semantics.ObservingAction.run body.root.dependencies 64))
              (erased.map (pureHistory body.root.dependencies (a++b++c)))) := by
  intro held pre center post state axes erasure next toCenter toPost
  obtain ⟨a,b,c,prior,suffix,read,events,terminal,bounds,composed,historyLaw⟩ :=
    RuntimeNamedThreePackedInstrument.original_adjacent_observing body view coverage toCenter toPost
  obtain ⟨priorEvents,entered,actual⟩ := prefix_erasure observed.checked pre.slice.interval next prior read
  change prior = priorEvents++[erasure] at actual
  subst prior
  have supplied := original_supplies_histories body view observed earlier prefixShape next input
  have observation := compose_observation observed.checked view.prePrimitive view.centerSelection view.postPrimitive
    held input a b c supplied bounds composed
  refine ⟨a,b,c,priorEvents,suffix,entered,events,observation,?_,?_⟩
  · intro last ends state finish
    obtain ⟨finalState,suffixRead⟩ := terminal ends
    obtain ⟨finishRead,physical,output,action⟩ :=
      Qleisli.RuntimeNamedThreePackedOutput.original_adjacent_post_finish body view last ends finalState
    have finished : suffix = [.pure finish] :=
      suffixRead.trans (congrArg (fun event => [Semantics.Observation.Event.pure event]) finishRead)
    refine ⟨output,finished,
      packed_outcomes observed.checked view.prePrimitive view.centerSelection view.postPrimitive held input
        (a++b++c) observation output _ physical action,?_⟩
    intro history
    have original : body.checked.native.whole.prepared.events =
        ((priorEvents++[erasure]) ++ (a++b++c++[finish]).map Semantics.Observation.Event.pure) ++ [] := by
      simp only [events,finished,List.append_nil,List.map_append,List.map_cons,List.map_nil,List.append_assoc]
    rw [original,RuntimeNamedThreePackedInstrument.run_surround_pure body.root.dependencies 64,
      RuntimeNamedThreePackedInstrument.run_append_event body.root.dependencies 64]
    cases Qleisli.Semantics.ObservingAction.run body.root.dependencies 65 priorEvents history <;> rfl
  · intro history
    rw [historyLaw,RuntimeNamedThreePackedInstrument.run_append_event body.root.dependencies 64]
    cases Qleisli.Semantics.ObservingAction.run body.root.dependencies 65 priorEvents history <;> rfl

#print axioms original_erasure_then_adjacent
end Qleisli.RuntimeNamedObservationEntry
