import Qleisli.RuntimeNamedBodyFlow
import QleisliKernel.Qirf.RuntimeNamedThreeOccurrence

/-! The actual pre/choose/post calls share their complete source states.
The source entry and final return reads come from this same original body.
These administrative joins do not yet compose the calls' logical actions.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeNamedSourceFlow
open QleisliKernel QleisliKernel.Qirf

private theorem primitive_entry {dependencies program block step}
    (held : @RuntimeNamedPrimitiveOccurrence.Occurrence dependencies program block step) :
    ∃ state, entryState step = some state := by
  cases held
  exact ⟨_,rfl⟩

private theorem primitive_exit {dependencies program block step}
    (held : @RuntimeNamedPrimitiveOccurrence.Occurrence dependencies program block step) :
    ∃ state, exitState step = some state := by
  cases held
  exact ⟨_,rfl⟩

private theorem middle_entry {dependencies program block step}
    (held : @RuntimeNamedThreeOccurrence.Middle dependencies program block step) :
    ∃ state, entryState step = some state := by
  cases held
  exact ⟨_,rfl⟩

private theorem middle_exit {dependencies program block step}
    (held : @RuntimeNamedThreeOccurrence.Middle dependencies program block step) :
    ∃ state, exitState step = some state := by
  cases held
  exact ⟨_,rfl⟩

private theorem primitive_child {artifact root execution}
    (next : RuntimePureBody.BlockRunner artifact root execution) {program block step}
    (held : @RuntimeNamedPrimitiveOccurrence.Occurrence root.dependencies program block step)
    (checked : RuntimeNamedChildRuns.CheckedStep next step) :
    RuntimeNamedChildRuns.ChildRun artifact root execution next step := by
  cases held
  exact checked

private theorem middle_child {artifact root execution}
    (next : RuntimePureBody.BlockRunner artifact root execution) {program block step}
    (held : @RuntimeNamedThreeOccurrence.Middle root.dependencies program block step)
    (checked : RuntimeNamedChildRuns.CheckedStep next step) :
    RuntimeNamedChildRuns.ChildRun artifact root execution next step := by
  cases held
  exact checked

/-- Both joins concern the full actual owner maps, bases, ports and issuance
histories. Neither matching widths nor a caller-provided code equation is used.
The first call is anchored to the real source entry read and the last call to
the real final return read, including any original owner reorder. -/
theorem original_three {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime)
    (view : RuntimeNamedThreeOccurrence.Three body.checked.result.steps) :
    let source := SourceTypes.SourceRuntimeScope.Subject.whole prepared.source.body
    let initialHistory := RuntimeBodyOperations.initialHistory prepared body.checked.native runtime body.checked.inputs
    ∃ initial : RuntimeOwnerMap.Checked source.initialRoles body.checked.native.block.entry,
      RuntimeInterval.Computed
        (RuntimePureBody.reordered source.initialRoles body.checked.native.block.entry initialHistory.bindings) initial ∧
      entryState view.pre = some {initialHistory with bindings := initial.bindings} ∧
      exitState view.pre = entryState view.center ∧
      exitState view.center = entryState view.post ∧
      ∃ last, exitState view.post = some last ∧
        Returned body.checked.native.block source.outputRoles last body.checked.result.history := by
  obtain ⟨initial,initialRead,last,flow,returned⟩ := original_body body
  rw [view.original] at flow
  cases flow with
  | cons first rest =>
    cases rest with
    | cons center rest =>
      cases rest with
      | cons final rest =>
        cases rest
        exact ⟨initial,initialRead,first.entry (primitive_entry view.prePrimitive),
          (first.exit (primitive_exit view.prePrimitive)).trans
            (center.entry (middle_entry view.centerSelection)).symm,
          (center.exit (middle_exit view.centerSelection)).trans
            (final.entry (primitive_entry view.postPrimitive)).symm,
          last,final.exit (primitive_exit view.postPrimitive),returned⟩

/-- Each of the three stored children comes from the actual recursive reader
on its original callee. The retained computation includes the real argument
binding read, visible ordinary SSA, callee block, source plan and result steps.
This does not yet compose their logical actions or observing histories. -/
theorem original_child_runs {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime)
    (view : RuntimeNamedThreeOccurrence.Three body.checked.result.steps) :
    let execution := RuntimePureBody.ExecutionMode.planned
      (RuntimeBodyOperations.preparation artifact prepared.source.catalogue)
      (RuntimeBodyOperations.stagedConsumption artifact prepared.source.catalogue body.root)
    let next := RuntimePureBody.runBlockCore artifact body.root execution 127
    RuntimeNamedChildRuns.ChildRun artifact body.root execution next view.pre ∧
      RuntimeNamedChildRuns.ChildRun artifact body.root execution next view.center ∧
      RuntimeNamedChildRuns.ChildRun artifact body.root execution next view.post := by
  obtain ⟨_initial,_input,_last,flow,_returned⟩ := RuntimeNamedChildRuns.original_body body
  exact ⟨primitive_child _ view.prePrimitive (flow.calls view.pre
      ((congrArg (fun steps => view.pre ∈ steps) view.original).mpr (by simp))),
    middle_child _ view.centerSelection (flow.calls view.center
      ((congrArg (fun steps => view.center ∈ steps) view.original).mpr (by simp))),
    primitive_child _ view.postPrimitive (flow.calls view.post
      ((congrArg (fun steps => view.post ∈ steps) view.original).mpr (by simp)))⟩

/-- The real adjacent source steps and all three recursive child reads also
remain available inside a longer original source body. -/
theorem original_adjacent_calls {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime)
    (view : RuntimeNamedThreeOccurrence.Adjacent body.checked.result.steps) :
    let execution := RuntimePureBody.ExecutionMode.planned
      (RuntimeBodyOperations.preparation artifact prepared.source.catalogue)
      (RuntimeBodyOperations.stagedConsumption artifact prepared.source.catalogue body.root)
    let next := RuntimePureBody.runBlockCore artifact body.root execution 127
    exitState view.pre = entryState view.center ∧
      exitState view.center = entryState view.post ∧
      RuntimeNamedChildRuns.ChildRun artifact body.root execution next view.pre ∧
      RuntimeNamedChildRuns.ChildRun artifact body.root execution next view.center ∧
      RuntimeNamedChildRuns.ChildRun artifact body.root execution next view.post := by
  obtain ⟨_initial,_input,_last,flow,_returned⟩ := RuntimeNamedChildRuns.original_body body
  have source := flow.source
  rw [view.original] at source
  obtain ⟨_entry,tail⟩ := source.suffix
  cases tail with
  | cons pre tail =>
    cases tail with
    | cons center tail =>
      cases tail with
      | cons post _ =>
        exact ⟨(pre.exit (primitive_exit view.prePrimitive)).trans
            (center.entry (middle_entry view.centerSelection)).symm,
          (center.exit (middle_exit view.centerSelection)).trans
            (post.entry (primitive_entry view.postPrimitive)).symm,
          primitive_child _ view.prePrimitive (flow.calls view.pre
            ((congrArg (fun steps => view.pre ∈ steps) view.original).mpr (by simp))),
          middle_child _ view.centerSelection (flow.calls view.center
            ((congrArg (fun steps => view.center ∈ steps) view.original).mpr (by simp))),
          primitive_child _ view.postPrimitive (flow.calls view.post
            ((congrArg (fun steps => view.post ∈ steps) view.original).mpr (by simp)))⟩

/-- The same original source traversal supplies the exact join from a
preceding destructive observation to the first adjacent named call. -/
theorem original_observation_join {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime)
    (view : RuntimeNamedThreeOccurrence.Adjacent body.checked.result.steps)
    {rootOwner rootName caller functionName path event position before ssa}
    (observed : @RuntimeOrdinaryBody.Observation artifact.sources rootOwner rootName caller functionName
      body.root.dependencies body.root.program path event body.checked.native.block position before ssa)
    (earlier : List (RuntimePureBody.Step body.root.dependencies body.root.program body.checked.native.block))
    (prefixShape : view.earlier = earlier ++ [.observation observed]) :
    some observed.after = entryState view.pre := by
  obtain ⟨_initial,_read,_last,flow,_returned⟩ := RuntimeNamedChildRuns.original_body body
  have source := flow.source
  have split : body.checked.result.steps =
      earlier ++ .observation observed :: view.pre :: view.center :: view.post :: view.later := by
    calc
      _ = view.earlier ++ view.pre :: view.center :: view.post :: view.later := view.original
      _ = (earlier ++ [.observation observed]) ++ view.pre :: view.center :: view.post :: view.later :=
        congrArg (fun preceding => preceding ++ view.pre :: view.center :: view.post :: view.later) prefixShape
      _ = _ := by simp only [List.append_assoc,List.cons_append,List.nil_append]
  rw [split] at source
  obtain ⟨_state,tail⟩ := source.suffix
  obtain ⟨entry,read⟩ := primitive_entry view.prePrimitive
  exact (congrArg some (tail.adjacent (rfl : exitState (.observation observed) = some observed.after) read)).trans
    read.symm

#print axioms original_observation_join
#print axioms original_adjacent_calls
#print axioms original_three
#print axioms original_child_runs
end Qleisli.RuntimeNamedSourceFlow
