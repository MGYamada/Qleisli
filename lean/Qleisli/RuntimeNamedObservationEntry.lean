import Qleisli.RuntimeNamedThreePackedInstrument
import Qleisli.RuntimeOriginalObservation

/-! The original destructive observation and the immediately following named
call share their entire Raw state and source owner map. Its retained output
frame supplies the exact input encoding for every emitted history.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeNamedObservationEntry
open QleisliKernel QleisliKernel.Qirf
open QleisliKernel.Qirf.RuntimeForestCode (Frame OwnerCode)
open Qleisli.Semantics.ObservingAction (History)
open Qleisli.RuntimeNamedThreeFrameChain (checkedAt frameAt)
open Qleisli.RuntimeNamedSourceFlow (entryState)
open Qleisli.RuntimeForestProduct (referenceAction)

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



/-- Every actual erasure result is encoded in the entry frame of the same
original named call. There is no premise about amplitudes outside the
observation's finite input domain. -/
def SuppliedHistories {sources caller dependencies program functionName event block position previous step}
    (observed : @RuntimeObservationAction.Checked sources caller dependencies program functionName
      event block position previous)
    (pre : @RuntimeNamedPrimitiveOccurrence.Occurrence dependencies program block step)
    (input : Frame observed.before) : Prop :=
  match pre with
  | .named (scope := scope) (before := before) _ _ =>
    let raw := observed.interval.before.quantum.reference
    let axes := observed.input.port.wires.map raw.frame.idxOf
    let event := Semantics.Observation.Event.erase raw.frame.length axes observed.measured
    ∃ same : observed.interval.after = scope.interval.before,
    ∃ consumed : OwnerCode observed.input, ∃ output : Frame observed.after,
      (checkedAt same observed.after).bindings = before.bindings ∧
      ∀ (recurse : List Semantics.Observation.Event → History → Option (List History))
        (joint : Nat → Nat → ℂ) (history : History),
        (∀ col, RawFiniteRows.OnRows raw.frame.length (fun row => history.operator row col)
          (fun row => referenceAction input joint row col)) →
        ∃ branch : Nat → History,
          Qleisli.Semantics.ObservingAction.step dependencies recurse event history =
            some ((List.range (2^axes.length)).map branch) ∧
          ∀ outcome, outcome < 2^axes.length → ∀ col,
            RawFiniteRows.OnRows scope.interval.before.quantum.frame.length
              (fun row => (branch outcome).operator row col)
              (fun row => referenceAction (frameAt same output)
                (RuntimeOriginalObservation.outcomeJoint consumed outcome joint) row col)

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
  intro outcome outcomeBound col row rowBound
  dsimp only
  rw [RuntimeNamedThreeFrameChain.frameAt_action]
  rw [← same] at rowBound
  exact (branches outcome outcomeBound).2.2 row rowBound col

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

end Qleisli.RuntimeNamedObservationEntry
