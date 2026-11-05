import Qleisli.RuntimeAdjacentRootAction
import Qleisli.RuntimeNamedSelectionOn
import Qleisli.RuntimeNamedOccurrenceAction
import Qleisli.RawInstrumentComposition
import Qleisli.RuntimeNamedCodeTransport

/-! Recover the literal parent slices from the three source calls. The middle
slice comes from the selection retained by this traversal of this body.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeNamedThreeRoot
open QleisliKernel QleisliKernel.Qirf
open RuntimeAdjacentSlices (Span Fold Event)
open RuntimeNamedOccurrenceAction (span)
open RuntimeNamedSelectionOn (middle)

/-- The full original observing root has one final reorder after the three
actual slices. Both joins identify the complete native state, including history. -/
structure Whole {deps program} (root : RuntimeInterval.Prepared deps program)
    (pre center post : Span root.block) (a b c : List Event) : Prop where
  toCenter : pre.slice.interval.after = center.slice.interval.before
  toPost : center.slice.interval.after = post.slice.interval.before
  preFold : Fold (deps.map (·.signature)) pre.slice.ops pre.slice.interval.before.quantum pre.slice.interval.after.quantum a
  centerFold : Fold (deps.map (·.signature)) center.slice.ops center.slice.interval.before.quantum center.slice.interval.after.quantum b
  postFold : Fold (deps.map (·.signature)) post.slice.ops post.slice.interval.before.quantum post.slice.interval.after.quantum c
  centerTrace : RuntimeLocalEvents.trace center.slice.interval.before.quantum.reference center.slice.ops =
    some ⟨center.slice.interval.after.quantum.reference,b,center.slice.interval.before.quantum.frame.length⟩
  finalState : root.whole.prepared.state = post.slice.interval.after.quantum.reference
  finalEvents : root.whole.prepared.events = (a ++ b ++ c).map Semantics.Observation.Event.pure ++
      [.pure (.reorder post.slice.interval.after.quantum.frame.length
        (Semantics.RawTrace.axes post.slice.interval.after.quantum.reference
          (program.outputs.flatMap fun token => ((post.slice.interval.after.quantum.live.find?
            (fun port => port.token == token)).map (·.wires)).getD [])))]

private def finalEvent {deps program} (root : RuntimeInterval.Prepared deps program)
    (post : Span root.block) : Semantics.Observation.Event :=
  .pure (.reorder post.slice.interval.after.quantum.frame.length
    (Semantics.RawTrace.axes post.slice.interval.after.quantum.reference
      (program.outputs.flatMap fun token => ((post.slice.interval.after.quantum.live.find?
        (fun port => port.token == token)).map (·.wires)).getD [])))

/-- Factor the actual original observing root's independent instrument
meaning into the three retained slices and its one real final permutation.
The complete intermediate history families are existentially retained. This
does not identify the slices' different source codes or discharge their
remaining whole-source encoding correspondence. -/
theorem Whole.instrument_decomposition {deps program} {root : RuntimeInterval.Prepared deps program}
    {pre center post : Span root.block} {a b c : List Event}
    (whole : Whole root pre center post a b c) (classical : List Bool)
    (histories : List Qleisli.Semantics.RawInstrument.History) :
    Qleisli.Semantics.RawInstrument.ProgramMeaning deps program classical histories ↔
      ∃ initial first second third,
        Qleisli.Semantics.Raw.IdentityMeaning root.whole.prepared.inputBits initial ∧
        Qleisli.Semantics.RawInstrument.Run deps (a.map Semantics.Observation.Event.pure)
          [⟨program.classicalInputs.zip classical,[],initial⟩] first ∧
        Qleisli.Semantics.RawInstrument.Run deps (b.map Semantics.Observation.Event.pure) first second ∧
        Qleisli.Semantics.RawInstrument.Run deps (c.map Semantics.Observation.Event.pure) second third ∧
        Qleisli.Semantics.RawInstrument.Run deps [finalEvent root post] third histories := by
  have events : root.whole.prepared.events =
      ((a.map Semantics.Observation.Event.pure ++ b.map Semantics.Observation.Event.pure) ++
        c.map Semantics.Observation.Event.pure) ++ [finalEvent root post] := by
    simpa only [List.map_append,finalEvent] using whole.finalEvents
  constructor
  · rintro ⟨prepared,initial,original,identity,ran⟩
    have same : prepared = root.whole.prepared := Option.some.inj (original.symm.trans root.originalRoot.reader)
    subst prepared
    rw [events] at ran
    obtain ⟨third,front,last⟩ := (Qleisli.Semantics.RawInstrument.Run.append_iff _ _ _ _).mp ran
    obtain ⟨second,front,post⟩ := (Qleisli.Semantics.RawInstrument.Run.append_iff _ _ _ _).mp front
    obtain ⟨first,pre,center⟩ := (Qleisli.Semantics.RawInstrument.Run.append_iff _ _ _ _).mp front
    exact ⟨initial,first,second,third,identity,pre,center,post,last⟩
  · rintro ⟨initial,first,second,third,identity,pre,center,post,last⟩
    refine ⟨root.whole.prepared,initial,root.originalRoot.reader,identity,?_⟩
    rw [events]
    exact ((pre.append center).append post).append last

private theorem whole {deps program} (p : RuntimeInterval.Prepared deps program)
    (pre center post : Span p.block) (starts : pre.start = 0)
    (next : center.start = pre.start+pre.count) (last : post.start = center.start+center.count)
    (covers : pre.count+center.count+post.count = program.operations.length) :
    ∃ a b c, Whole p pre center post a b c := by
  rcases pre with ⟨s,a,pre⟩
  rcases center with ⟨t,b,center⟩
  rcases post with ⟨u,c,post⟩
  change s = 0 at starts
  change t = s+a at next
  change u = t+b at last
  subst s
  subst t
  subst u
  obtain ⟨ev₁,ev₂,ev₃,checked⟩ := RuntimeAdjacentSlices.three pre center post
  exact ⟨ev₁,ev₂,ev₃,checked.toChoose,checked.toPost,checked.preFold,checked.chooseFold,checked.postFold,checked.chooseFold.trace,
    (checked.retainedRoot p covers).1,(checked.retainedRoot p covers).2⟩

/-- The three equations refer to the very event lists of the original root
and its final output permutation. Each equation retains its own input code. -/
theorem original_body {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime)
    (view : RuntimeNamedThreeOccurrence.Three body.checked.result.steps)
    (coverage : RuntimeNamedSelectionOn.Coverage view.centerSelection (RuntimeNamedThreeOccurrence.actual_body_middle body view)) :
    let held := RuntimeNamedThreeOccurrence.actual_body_middle body view
    let pre := span view.prePrimitive
    let center := middle view.centerSelection held coverage
    let post := span view.postPrimitive
    pre.start = 0 → center.start = pre.start+pre.count → post.start = center.start+center.count →
    pre.count+center.count+post.count = body.root.program.operations.length →
    ∃ a b c, Whole body.checked.native pre center post a b c ∧
      RuntimeNamedOccurrenceAction.On view.prePrimitive a ∧
      RuntimeNamedSelectionOn.On b view.centerSelection held ∧ RuntimeNamedOccurrenceAction.On view.postPrimitive c := by
  intro held pre center post starts next last covers
  obtain ⟨a,b,c,root⟩ := whole body.checked.native pre center post starts next last covers
  exact ⟨a,b,c,root,RuntimeNamedOccurrenceAction.on_span view.prePrimitive a root.preFold,
    RuntimeNamedSelectionOn.on_middle view.centerSelection held coverage b root.centerTrace,
    RuntimeNamedOccurrenceAction.on_span view.postPrimitive c root.postFold⟩

/-- The same complete original traversal supplies the code/axis return law
for every named call in its retained step list. This does not assert equality
of unrelated intermediate source encodings or compose their logical actions. -/
theorem original_return_codes {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime)
    (step : RuntimePureBody.Step body.root.dependencies body.root.program body.checked.native.block)
    (_original : step ∈ body.checked.result.steps) : RuntimeNamedCodeTransport.StepReturnCodes step :=
  RuntimeNamedCodeTransport.step_return_codes step

#print axioms original_body
#print axioms Whole.instrument_decomposition
#print axioms original_return_codes
end Qleisli.RuntimeNamedThreeRoot
