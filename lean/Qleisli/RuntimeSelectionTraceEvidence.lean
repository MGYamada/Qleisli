import Qleisli.RuntimeIntervalRawFold
import Qleisli.RuntimeSectorPrefix
import Qleisli.RuntimeFoldLocality
import Qleisli.RuntimeSelectionAxes

/-! Mathematical trace/evaluation evidence for the same original selection.
Actual caller/local/owner receipts derive every circuit chunk and its exact
localization, with no complete-forest OwnerCodes premise. Only Literal's two
forest-code fields are omitted. No Carrier, Gram or Logical obligation, native
reader, acceptance gate or work counter changes. Whole-forest code availability
and successful budgeted readSource/Witness invocations remain separate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeSelectionTraceEvidence
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Semantics.Finite

/-- Exactly the trace fields of Literal for this SAME source and retained
sector, without either complete-forest code. It is mathematical evidence only. -/
structure TraceEvidence {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles)
    (selectorBits targetBits : Nat) (retained : Raw.Sector.Retained)
    (restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits selectorBits] [.bits targetBits]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained) where
  selection : RuntimeScatterTransport.Selection source.before
  selectedRoles : selection.selectedRoles = roles
  selectedPorts : selection.selected.map (·.port) = frame.selected
  traceResult : Semantics.RawTrace.Prepared
  executed : RuntimeLocalEvents.trace frame.interval.before.quantum.reference frame.operations = some traceResult
  afterState : traceResult.state = frame.interval.after.quantum.reference
  preservedFrame : frame.interval.after.quantum.frame = frame.interval.before.quantum.frame
  chunks : List (List Step)
  localRead : RuntimeLocalEvents.readChunks (selectorBits+targetBits) retained.prepared.events = .ok chunks
  localSteps : chunks.flatten = retained.steps
  bounded : RuntimeLocalEvents.bounds
    (RuntimeForestCode.forestAxes frame.interval.before.quantum.frame selection.selected).length chunks = true
  literal : traceResult.events = RuntimeLocalEvents.circuitEvents frame.interval.before.quantum.frame.length
    (RuntimeForestCode.forestAxes frame.interval.before.quantum.frame selection.selected) chunks

private theorem read_circuit (bits : Nat) (steps : List Step) (events : List Semantics.Raw.Event) :
    RuntimeLocalEvents.readChunks bits (.circuit bits steps :: events) = (do
      let rest ← RuntimeLocalEvents.readChunks bits events
      pure (steps :: rest)) := by
  simp [RuntimeLocalEvents.readChunks,List.mapM_cons]

private theorem read_local_finish (bits : Nat) (chunks : List (List Step)) :
    RuntimeLocalEvents.readChunks bits
      (RuntimeLocalEvents.localEvents bits chunks ++ [.reorder bits (List.range bits)]) = .ok chunks := by
  induction chunks with
  | nil =>
    simp only [RuntimeLocalEvents.readChunks,RuntimeLocalEvents.localEvents,List.map_nil,List.nil_append,
      List.mapM_cons,List.mapM_nil,beq_self_eq_true,Bool.and_self,ite_true,Except.bind,bind,pure]
    rfl
  | cons first rest ih =>
    change RuntimeLocalEvents.readChunks bits
      (.circuit bits first :: (RuntimeLocalEvents.localEvents bits rest ++ [.reorder bits (List.range bits)])) =
        .ok (first :: rest)
    rw [read_circuit,ih]
    rfl

/-- SAME original source, caller interval and retained sector imply exact
trace/chunk evidence without a whole-forest code-availability assumption. No
event equation, final invariant, shape or successful reader is an extra premise. -/
theorem trace_of_source {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles)
    {selectorBits targetBits : Nat} {retained : Raw.Sector.Retained}
    (restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits selectorBits] [.bits targetBits]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained) :
    Nonempty (TraceEvidence frame source selectorBits targetBits retained restricted) := by
  obtain ⟨initial,body,pieces,_initialized,localFold,initialReference,initialBits,_outputChecked,prepared,
      finishWidth,finishAxes,_finishPiece,prefixPieces,retainedSteps⟩ :=
    Qleisli.RuntimeSectorPrefix.sector_prefix (dependencies := dependencies)
      (selector := [.bits selectorBits]) (target := [.bits targetBits])
      (program := RuntimePureInterval.fragment frame.selected frame.operations outputs) (retained := retained) restricted
  have initialLive : initial.live = frame.selected :=
    congrArg Semantics.RawTrace.Interface.live initialReference
  have initialFrame : initial.frame = frame.selected.flatMap (·.wires) :=
    congrArg Semantics.RawTrace.Interface.frame initialReference
  have totalBits : initial.frame.length = selectorBits + targetBits := by
    simpa only [width,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using initialBits
  let selection : RuntimeScatterTransport.Selection source.before :=
    ⟨roles,source.selected.toList,source.selected.ordered,Qleisli.RuntimeSelectionAxes.distinct frame source⟩
  have selectedPorts : source.selected.toList.map (·.port) = frame.selected := by
    change [source.selected.first.port,source.selected.second.port] = frame.selected
    exact (RuntimeSelectionPartition.source_ports frame source).1.symm
  let spectators := (RuntimeSelectionPartition.complement source.before.bindings source.selected.toList).map (·.port)
  have partition : (source.selected.toList.map (·.port) ++ spectators).Perm frame.interval.before.quantum.live := by
    simpa only [List.map_append,spectators] using
      ((RuntimeSelectionPartition.source_input_partition frame source).map (fun binding => binding.port)).trans source.before.complete
  have embedded : frame.interval.before.quantum.live.Perm (initial.live ++ spectators) := by
    rw [initialLive,← selectedPorts]
    exact partition.symm
  have localReturn := frame.ownerReturn
  unfold Semantics.RawOwnerFlow.Returns Semantics.RawOwnerFlow.run at localReturn
  obtain ⟨ownerBefore,_seeded,tail⟩ := Option.bind_eq_some_iff.mp localReturn
  obtain ⟨ownerAfter,ownerFold,_returned⟩ := Option.bind_eq_some_iff.mp tail
  change frame.operations.foldlM Semantics.RawOwnerFlow.step ownerBefore = some ownerAfter at ownerFold
  obtain ⟨callerEvents,callerFold⟩ := Qleisli.RuntimeIntervalRawFold.interval_raw_fold frame
  let callerBody : Raw.Prepared :=
    ⟨frame.interval.after.quantum,callerEvents,frame.interval.before.quantum.frame.length⟩
  have callerRun : frame.operations.foldlM (Raw.advance (dependencies.map (·.signature)))
      ⟨frame.interval.before.quantum,[],frame.interval.before.quantum.frame.length⟩ = .ok callerBody := callerFold
  have localRun : frame.operations.foldlM (Raw.advance (dependencies.map (·.signature)))
      ⟨initial,[],initial.frame.length⟩ = .ok body := localFold
  have actualPieces : Exact.ListRel (Raw.Sector.EventPiece initial.frame.length) body.events pieces := prefixPieces
  have locality := by
    with_reducible
      exact (Qleisli.RuntimeFoldLocality.folds_locality (dependencies.map (·.signature)) frame.operations
        frame.interval.before.quantum initial callerBody body spectators ownerBefore ownerAfter pieces
        embedded callerRun localRun ownerFold actualPieces)
  obtain ⟨chunks,localEvents,callerEventsEquation,flatten,bounded,_remaining,callerFrame,_localFrame,
      _callerBits,_localBits,callerTrace,_localTrace⟩ := locality
  have axes : initial.frame.map frame.interval.before.quantum.frame.idxOf =
      RuntimeForestCode.forestAxes frame.interval.before.quantum.frame selection.selected := by
    rw [initialFrame,← selectedPorts]
    simp only [selection,RuntimeForestCode.forestAxes,List.flatMap_map]
  have axesLength : (RuntimeForestCode.forestAxes frame.interval.before.quantum.frame selection.selected).length =
      initial.frame.length := by
    rw [← axes,List.length_map]
  have localRead : RuntimeLocalEvents.readChunks (selectorBits+targetBits) retained.prepared.events = .ok chunks := by
    rw [prepared]
    change RuntimeLocalEvents.readChunks (selectorBits+targetBits)
      (body.events ++ [.reorder body.state.frame.length (Qleisli.RuntimeSectorPrefix.outputAxes
        (RuntimePureInterval.fragment frame.selected frame.operations outputs) body)]) = .ok chunks
    rw [localEvents,finishWidth,finishAxes,← totalBits]
    exact read_local_finish initial.frame.length chunks
  refine ⟨{
    selection := selection
    selectedRoles := rfl
    selectedPorts := selectedPorts
    traceResult := callerBody.reference
    executed := callerTrace
    afterState := rfl
    preservedFrame := callerFrame
    chunks := chunks
    localRead := localRead
    localSteps := flatten.trans retainedSteps.symm
    bounded := ?_
    literal := ?_
  }⟩
  · rw [axesLength]
    exact bounded
  · rw [← axes]
    exact callerEventsEquation

/-- Coefficient evaluation of the same caller trace factors through the
derived local chunks at these exact selected axes, without either forest code.
All selected Carrier, sector Gram and logical equations remain independent. -/
theorem TraceEvidence.references {Reference : Type}
    {dependencies program block start count inputs outputs roles frame source selectorBits targetBits retained restricted}
    (checked : @TraceEvidence dependencies program block start count inputs outputs roles frame source
      selectorBits targetBits retained restricted) (values : Reference → Raw.Coefficient.State) :
    (fun reference output => RuntimeLocalEvents.evaluate dependencies checked.traceResult.events (values reference) output) =
      (fun reference output => RuntimeLocalEvents.evaluate dependencies
        (RuntimeLocalEvents.localEvents (selectorBits+targetBits) checked.chunks)
        (RuntimeScatterTransport.pull output
          (RuntimeForestCode.forestAxes frame.interval.before.quantum.frame checked.selection.selected) (values reference))
        (gather output (RuntimeForestCode.forestAxes frame.interval.before.quantum.frame checked.selection.selected))) := by
  rw [checked.literal]
  funext reference output
  have point := congrFun (RuntimeLocalEvents.events_selected dependencies output frame.interval.before.quantum.frame.length
    (selectorBits+targetBits) _ checked.selection.distinct checked.chunks
    (RuntimeLocalEvents.bounds_controls checked.bounded) (RuntimeLocalEvents.bounds_targets checked.bounded) (values reference))
      (gather output (RuntimeForestCode.forestAxes frame.interval.before.quantum.frame checked.selection.selected))
  simpa only [RuntimeScatterTransport.pull,RuntimeScatterTransport.scatter_gather _ _ checked.selection.distinct] using point

#print axioms trace_of_source
#print axioms TraceEvidence.references

end Qleisli.RuntimeSelectionTraceEvidence
