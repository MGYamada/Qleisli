import Qleisli.RuntimeSparseOperationAction
import Qleisli.RawProtectedMatrixAction

/-! The graph operation's original checked interval and reconstructed local
matrix supply the same full caller history, including its inherited SSA.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeOriginalGraphAction
open QleisliKernel QleisliKernel.Qirf
open QleisliKernel.Semantics.Exact (Matrix)
open Qleisli.Semantics.Exact (action)
open Qleisli.RuntimeLiteralBody (SourceHistory SemanticHistoryAgreesWithInherited cast_represents)
open Qleisli.RuntimeSparseOperationAction
open Qleisli.RuntimeCallHistory (project)
open RuntimeCallTraceFrames (WireOrder)
open RuntimeOwnerMap (Binding)

private theorem fragment_action {dependencies program block arity start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block arity start count inputs outputs roles)
    {physical : Matrix}
    (read : RuntimeInterval.Computed (Raw.ProtectedEvaluation.reconstruct dependencies
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) physical)
    (rows : physical.rows = 2^frame.pureBody.state.frame.length)
    {entry : Raw.State} {childEvents}
    (entryRef : entry.reference = ⟨frame.selected,WireOrder frame.selected⟩)
    (trace : RuntimeLocalEvents.trace entry.reference frame.operations =
      some ⟨frame.pureBody.state.reference,childEvents,entry.frame.length⟩)
    {Reference : Type} (joint : Nat → Reference → ℂ) (row : Nat) (reference : Reference)
    (bound : row < 2^frame.pureBody.state.frame.length) :
    Qleisli.Semantics.RawAction.events dependencies childEvents (fun col => joint col reference) row =
      action physical joint (project frame.pureBody.state.reference (WireOrder frame.returned) row) reference := by
  obtain ⟨_,permutation⟩ := Qleisli.RuntimeCallHistory.fragment_finish frame entryRef trace
  have width := permutation.length_eq.trans List.length_range
  have packedBound : project frame.pureBody.state.reference (WireOrder frame.returned) row < physical.rows := by
    simpa only [project,width,rows] using Qleisli.RuntimeForestProduct.gather_bound row
      (Semantics.RawTrace.axes frame.pureBody.state.reference (WireOrder frame.returned))
  obtain ⟨original,readTrace,evaluated⟩ := Qleisli.RuntimeCallHistory.fragment_prefix_action
    frame entryRef trace (fun col => joint col reference) row bound
  obtain ⟨work,left,reconstructed⟩ := read
  exact evaluated.symm.trans
    (Qleisli.Raw.ReconstructedAction.program_action dependencies _ physical work left reconstructed original
      readTrace joint _ reference packedBound).symm

/-- The actual source-ordered graph application supplies the finite operator,
owner state, inherited SSA and hidden history in a single literal result. -/
theorem original_graph_history {dependencies program block arity start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block arity start count inputs outputs roles)
    {inputCode outputCode physical logical : Matrix}
    (inputRead : RuntimeInterval.Computed
      (Carrier.ownerCode ((frame.selected.zip roles).map fun (port,role) => ⟨port,role.basis⟩)) inputCode)
    (outputRead : RuntimeInterval.Computed
      (Carrier.ownerCode ((frame.returned.zip roles).map fun (port,role) => ⟨port,role.basis⟩)) outputCode)
    (physicalRead : RuntimeInterval.Computed (Raw.ProtectedEvaluation.reconstruct dependencies
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) physical)
    (checked : QleisliKernel.CodeSpace.Map inputCode outputCode physical)
    (equation : checked.logical = logical)
    {before after : RuntimeStructuralAction.SourceState} {ordinary : RuntimeOrdinaryBody.State}
    (ownerOrder : Qleisli.RuntimeNamedSourceFlow.OperationOwnerOrder frame before after)
    (rootInputs : List Nat) (inherited : Option (Nat → Prop))
    {source : SourceHistory} {actual : Qleisli.Semantics.ObservingAction.History}
    (agrees : SemanticHistoryAgreesWithInherited inherited rootInputs frame.interval.before before ordinary source actual)
    {events results}
    (read : Semantics.Observation.readOps block.fuel frame.interval.before.quantum.reference
      ((block.operations.drop start).take count) = some (frame.interval.after.quantum.reference,events))
    (executed : Qleisli.Semantics.ObservingAction.run dependencies block.fuel events actual = some results) :
    ∃ selected returned spectators,
      List.Forall₂ (SemanticHistoryAgreesWithInherited inherited rootInputs frame.interval.after after ordinary)
        [{source with owners := after, operator :=
          applySourceBlock before.bindings after.bindings selected returned spectators logical source.operator}] results := by
  have originalAgreement := agrees
  obtain ⟨_,_,_,_,_,incoming,initial,input,represented⟩ := agrees
  have retained := ownerOrder
  obtain ⟨_,_,originalInterval,_,transport,_,final,_⟩ := retained
  let sameExit := Qleisli.RuntimeIntervalStates.same_after originalInterval frame.interval
  let outgoing := Qleisli.RuntimeNamedThreeFrameChain.checkedAt sameExit transport.after
  have outgoingOrder : outgoing.bindings = after.bindings :=
    (Qleisli.RuntimeNamedThreeFrameChain.checkedAt_bindings sameExit transport.after).trans final
  obtain ⟨selected,returned,spectators,_,_,selectedPorts,returnedPorts,beforeOrder,_,rows,_,lifted⟩ :=
    original_operation_code_lift frame ownerOrder incoming outgoing initial outgoingOrder (initial.symm ▸ input)
      inputRead outputRead physicalRead checked equation
  have live := incoming.complete.symm.trans (beforeOrder.symm.map Binding.port)
  rw [List.map_append,← selectedPorts] at live
  obtain ⟨entry,parentEvents,childEvents,entryRef,parentTrace,childTrace,exitWires,_,bounded,paired⟩ :=
    Qleisli.RuntimeCallHistory.pure_interval_events frame (spectators.map Binding.port) live
  have entryWires : entry.reference.frame = WireOrder (selected.map Binding.port) := by
    rw [entryRef,selectedPorts]
  rw [returnedPorts] at exitWires
  have localMatrix {Reference : Type} (joint : Nat → Reference → ℂ) row reference
      (bound : row < 2^frame.pureBody.state.frame.length) :
      Qleisli.Semantics.RawAction.events dependencies childEvents (fun col => joint col reference) row =
        action physical joint (project frame.pureBody.state.reference (WireOrder (returned.map Binding.port)) row) reference := by
    simpa only [returnedPorts] using fragment_action frame physicalRead rows entryRef childTrace joint row reference bound
  obtain ⟨output,representedAfter⟩ := operation_events_lift incoming outgoing (initial.symm ▸ input)
    lifted entryWires exitWires bounded paired localMatrix source.operator actual
    (cast_represents initial.symm input represented)
  let node : RuntimePureBody.Node dependencies program block :=
    .operation frame inputCode outputCode physical logical inputRead outputRead physicalRead checked equation
  let operator := applySourceBlock incoming.bindings outgoing.bindings selected returned spectators logical source.operator
  have refined := pure_step_history_lift node rootInputs inherited outgoing outgoingOrder source actual operator
    originalAgreement read executed (by
      intro operations emitted literal traced
      have sameOps : frame.operations = operations :=
        (List.map_inj_right (f := Semantics.Observation.Op.pure)
          (fun _ _ same => Semantics.Observation.Op.pure.inj same)).mp (frame.literal.symm.trans literal)
      subst operations
      have sameEvents : emitted = parentEvents :=
        congrArg Semantics.RawTrace.Prepared.events (Option.some.inj (traced.symm.trans parentTrace))
      subst emitted
      exact ⟨output,representedAfter⟩)
  exact ⟨selected,returned,spectators,
    by simpa only [node,Qleisli.RuntimeLiteralBody.nodeSpan,operator,initial,outgoingOrder] using refined⟩

#print axioms original_graph_history
end Qleisli.RuntimeOriginalGraphAction
