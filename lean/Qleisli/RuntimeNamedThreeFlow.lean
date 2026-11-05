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

#print axioms original_three
end Qleisli.RuntimeNamedSourceFlow
