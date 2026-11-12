import Qleisli.RuntimeNamedSelectionInputs
import Qleisli.RuntimeSelectionFrameEvidence
import QleisliKernel.Qirf.RuntimeOwnerCodeReindex

/-! Derive the actual selection frames from the complete caller's owner codes.
No successful readFrame invocation or remaining-work claim is asserted.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeNamedSelectionFrames
open QleisliKernel QleisliKernel.Qirf
open RuntimeOwnerMap (Map Binding)
open RuntimeForestCode RuntimeOwnerCodeReindex

/-- Full ordered carriers, rather than widths, identify the same per-owner
read. Source aliases may differ while the complete port and basis stay fixed. -/
theorem carrier_codes {left right : Map} (same : carrierOwners right = carrierOwners left)
    (codes : OwnerCodes left) : Nonempty (OwnerCodes right) := by
  induction codes generalizing right with
  | nil =>
    cases right with
    | nil => exact ⟨.nil⟩
    | cons current tail => simp [carrierOwners] at same
  | @cons original rest first remaining ih =>
    cases right with
    | nil => simp [carrierOwners] at same
    | cons current tail =>
      have parts := List.cons.inj same
      have head : (⟨current.port,current.owner.basis⟩ : Semantics.CarrierInterface.Owner) =
          ⟨original.port,original.owner.basis⟩ := parts.1
      have actual : RuntimeInterval.Computed
          (Carrier.readOwner ⟨current.port,current.owner.basis⟩) first.layout := by
        rw [head]
        exact first.original
      obtain ⟨tailCodes⟩ := ih parts.2
      exact ⟨.cons ⟨first.layout,actual⟩ tailCodes⟩

def NodeFrames {dependencies program block}
    (node : @RuntimePureBody.Node dependencies program block) : Prop :=
  match node with
  | .selection (codes := codes) .. =>
    Nonempty (Frame codes.owners.before) ∧ Nonempty (Frame codes.owners.transport.after)
  | _ => True

theorem node_frames {dependencies program block bindings}
    (available : Nonempty (OwnerCodes bindings))
    (node : @RuntimePureBody.Node dependencies program block)
    (input : RuntimeNamedSelectionInputs.NodeInput (carrierOwners bindings) node) :
    NodeFrames node := by
  cases node with
  | primitive _ _ => trivial
  | structural _ => trivial
  | basis => trivial
  | named _ _ _ _ _ _ => trivial
  | operation _ _ _ _ _ _ _ _ _ _ => trivial
  | rectangularOperation _ => trivial
  | transform => trivial
  | selection frame selectorBits targetBits retained restricted inputCode outputCode labels expected logical equations codes layouts =>
    obtain ⟨original⟩ := available
    have actual := carrier_codes input original
    exact ⟨RuntimeForestFrameEvidence.of_ownerCodes codes.owners.before actual,
      RuntimeSelectionFrameEvidence.frame_after frame codes.owners restricted actual⟩

def OccurrenceFrames {dependencies program block step}
    (held : @RuntimeNamedThreeOccurrence.Middle dependencies program block step) : Prop :=
  match held with
  | .named (before := before) (scope := scope) node _ =>
    ∀ {roles} (checked : RuntimeOwnerMap.Checked roles scope.interval.before) (_frame : Frame checked),
      checked.bindings = before.bindings → NodeFrames node

/-- The actual child input is derived from the same real named call. Parent
owner receipts select its original ordered arguments before carrier transport;
the after Frame follows the same original selection's recorded owner flow. -/
theorem actual_occurrence_frames {artifact root execution fuel program block step}
    (held : @RuntimeNamedThreeOccurrence.Middle root.dependencies program block step)
    (call : RuntimeNamedChildRuns.ChildRun artifact root execution
      (RuntimePureBody.runBlockCore artifact root execution (fuel+1)) step) :
    OccurrenceFrames held := by
  have input := RuntimeNamedSelectionInputs.actual_occurrence_source held call
  cases held with
  | @named start count inputs sources caller before childHistory childRetired ordinary event scope body read boundary finalOrdinary node selected =>
    intro roles checked frame same
    have subset := (RuntimeSelectionPartition.order_values before.bindings event.inputOwners
      boundary.input.ordered boundary.input.orderRead).1
    have retained : boundary.input.ordered ⊆ checked.bindings := by
      rw [same]
      exact subset
    obtain ⟨codes,_found⟩ := reindex_exists frame.owners boundary.input.ordered retained
    exact node_frames ⟨codes⟩ node input.1

/-- The real middle child retains both mathematical Frames once its actual
complete caller input Frame is available. No budgeted read is fabricated. -/
theorem original_middle_frames {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime)
    (view : RuntimeNamedThreeOccurrence.Three body.checked.result.steps) :
    OccurrenceFrames view.centerSelection :=
  actual_occurrence_frames view.centerSelection
    (RuntimeNamedSourceFlow.original_child_runs body view).2.1

#print axioms carrier_codes
#print axioms node_frames
#print axioms actual_occurrence_frames
#print axioms original_middle_frames
end Qleisli.RuntimeNamedSelectionFrames
