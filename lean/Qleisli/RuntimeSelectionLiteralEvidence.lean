import Qleisli.RuntimeSelectionTraceEvidence
import Qleisli.RuntimeForestFrameEvidence
import Qleisli.RuntimeOwnerTransitionFrameEvidence

/-! A mathematical Literal for the same actual source selection and sector.
Shared trace evidence supplies all event/localization fields without forest
codes. Original BEFORE owner-code availability and the recorded source-owner
transition supply exactly the two remaining frame fields. Nonempty asserts no
readSource invocation, remaining-work bound, accepted handle or general
arbitrary-body BEFORE availability theorem.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeSelectionLiteralEvidence
open QleisliKernel QleisliKernel.Qirf

/-- The actual source lookup, same retained sector and original BEFORE owner
receipts suffice to construct this Literal mathematically. All its final code,
event, frame, reader and bound fields are derived; no lowering shape or final
availability/locality premise is supplied. This is not a budgeted read claim. -/
theorem literal_of_ownerCodes
    {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles)
    {selectorBits targetBits : Nat} {retained : Raw.Sector.Retained}
    (restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits selectorBits] [.bits targetBits]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained)
    (available : Nonempty (RuntimeForestCode.OwnerCodes source.before.bindings)) :
    Nonempty (RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
      source.before source.transport.after) := by
  obtain ⟨trace⟩ := Qleisli.RuntimeSelectionTraceEvidence.trace_of_source frame source
    (selectorBits := selectorBits) (targetBits := targetBits) (retained := retained) restricted
  obtain ⟨inputCode⟩ := Qleisli.RuntimeForestFrameEvidence.of_ownerCodes source.before available
  obtain ⟨outputCode⟩ := Qleisli.RuntimeOwnerTransitionFrameEvidence.frame_after
    frame.interval source.before source.transport available
  exact ⟨{
    selection := trace.selection
    selectedRoles := trace.selectedRoles
    selectedPorts := trace.selectedPorts
    inputCode := inputCode
    outputCode := outputCode
    traceResult := trace.traceResult
    executed := trace.executed
    afterState := trace.afterState
    chunks := trace.chunks
    localRead := trace.localRead
    localSteps := trace.localSteps
    bounded := trace.bounded
    literal := trace.literal
  }⟩

#print axioms literal_of_ownerCodes

end Qleisli.RuntimeSelectionLiteralEvidence
