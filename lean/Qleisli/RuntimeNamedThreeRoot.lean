import Qleisli.RuntimeAdjacentRootAction
import Qleisli.RuntimeNamedSelectionOn
import Qleisli.RuntimeNamedOccurrenceAction

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

#print axioms original_body
end Qleisli.RuntimeNamedThreeRoot
