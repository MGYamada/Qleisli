import Qleisli.RuntimePureProviderRefinement
import Qleisli.RawPureInstrumentAction
import Qleisli.RawActionComposition
import Qleisli.RuntimeNamedThreePackedOutput

/-! The checked provider's original body, complete program and final
permutation use one literal Raw event trace.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimePureProviderExecution
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite
open Semantics.Observation (readOps)
open Qleisli.Semantics.ObservingAction (History run)
open Qleisli.Semantics.Exact (action)
open Qleisli.Semantics.RawAction (event events)
open RuntimeNamedThreePackedInstrument (pureHistory run_pure)
open RuntimeNamedThreePackedOutput (readerFinish)

theorem entry_reference {dependencies program}
    (prepared : RuntimeInterval.Prepared dependencies program) (closed : program.classicalInputs = []) :
    prepared.entry.quantum.reference = Semantics.RawTrace.initial program.inputs := by
  obtain ⟨work,left,ran⟩ := prepared.inputRead
  unfold PureInterval.initial at ran
  obtain ⟨quantum,_,inserted,returned⟩ := bind_success _ _ _ _ _ ran
  rw [closed,List.foldlM_nil] at returned
  change (pure ({quantum} : Raw.Observation.State) : WorkM Raw.Observation.State).run _ =
    (.ok prepared.entry,left) at returned
  rw [(pure_success _ _ _ _ returned).1]
  exact Raw.inputs_reference _ _ _ (lift_success _ _ _ _ inserted).1

/-- The actual complete-program read appends exactly the final permutation
to the same trace that drives the source prefix induction. -/
theorem actual_trace {artifact context description graph index request header root demand}
    (checked : @RuntimeProviderAction.Checked artifact context description graph index request header root demand)
    (last : RuntimeInterval.Checked checked.originalBody.body.result.prepared.block
      checked.originalBody.body.result.prepared.block.operations.length 0) :
    let native := checked.paths.ir.original
    let block := checked.originalBody.body.result.prepared.block
    let finish := readerFinish native.program last.before.quantum.reference
    ∃ rawEvents : List Semantics.Raw.Event,
      readOps block.fuel block.entry.quantum.reference block.operations =
        some (last.before.quantum.reference,rawEvents.map Semantics.Observation.Event.pure) ∧
      Semantics.Observation.read native.program = some native.prepared.verified.prepared ∧
      native.prepared.verified.prepared.events = (rawEvents ++ [finish]).map Semantics.Observation.Event.pure ∧
      native.prepared.verified.prepared.state = last.before.quantum.reference := by
  intro native block finish
  obtain ⟨_,operations,pureOps⟩ := RuntimePureProviderNative.checked_pure_shape checked.originalBody.body
  obtain ⟨work,left,checkedPrefix⟩ := last.prefixRead
  have runOps := congrArg (fun ops => (Raw.Observation.checkOps root.dependencies block.fuel
    block.entry ops).run work) pureOps
  have purePrefix := runOps.symm.trans (by simpa only [List.take_length] using checkedPrefix)
  obtain ⟨rawEvents,traced⟩ :=
    RuntimeIntervalTrace.checkOps_pure_trace root.dependencies block.fuel block.entry last.before operations work left
      purePrefix
  have literal : readOps block.fuel block.entry.quantum.reference block.operations =
      some (last.before.quantum.reference,rawEvents.map Semantics.Observation.Event.pure) := by
    exact (congrArg (readOps block.fuel block.entry.quantum.reference) pureOps).trans
      (RuntimeAdjacentSlices.readOps_pure 64 _ _ _ traced)
  obtain ⟨before,after,verified⟩ := native.prepared.verification
  have original := (Raw.Observation.verify_postcondition _ _ _ _ _ verified).reader
  have entry := entry_reference checked.originalBody.body.result.prepared native.prepared.ports.noClassical.1
  have whole : Semantics.Observation.read native.program =
      some ⟨last.before.quantum.reference,(rawEvents ++ [finish]).map Semantics.Observation.Event.pure,
        (Semantics.RawTrace.initial native.program.inputs).frame.length⟩ := by
    unfold Semantics.Observation.read
    have read := literal
    change readOps 65 block.entry.quantum.reference native.program.operations = _ at read
    rw [show block.entry.quantum.reference = Semantics.RawTrace.initial native.program.inputs from entry] at read
    simp only [read,bind,Option.bind,pure,List.map_append,List.map_cons,List.map_nil,finish,readerFinish]
  have same := Option.some.inj (original.symm.trans whole)
  exact ⟨rawEvents,literal,original,congrArg Semantics.Observation.Prepared.events same,
    congrArg Semantics.Observation.Prepared.state same⟩

/-- The input code acts before the exact body history and the reader's real
output permutation. The result equals the checked logical provider action
through the original output code on every physical row. -/
theorem native_execution {artifact context description graph index request header root demand}
    (checked : @RuntimeProviderAction.Checked artifact context description graph index request header root demand)
    (last : RuntimeInterval.Checked checked.originalBody.body.result.prepared.block
      checked.originalBody.body.result.prepared.block.operations.length 0)
    (joint : Nat → Nat → ℂ) :
    let native := checked.paths.ir.original
    let block := checked.originalBody.body.result.prepared.block
    let initial : History := ⟨[],[],action native.prepared.inputCode joint⟩
    let finish := readerFinish native.program last.before.quantum.reference
    ∃ final : History,
      (do
        let (_,events) ← readOps block.fuel block.entry.quantum.reference block.operations
        run root.dependencies block.fuel events initial) = some [final] ∧
      ∀ row column, row < native.prepared.physical.rows →
        event root.dependencies finish (fun i => final.operator i column) row =
          action native.prepared.outputCode (fun i ref => action checked.action joint i ref) row column := by
  intro native block initial finish
  obtain ⟨rawEvents,literal,original,pureEvents,_⟩ := actual_trace checked last
  let final := pureHistory root.dependencies rawEvents initial
  refine ⟨final,?_,?_⟩
  · rw [literal]
    exact run_pure root.dependencies 64 rawEvents initial
  · intro row column bound
    obtain ⟨work,left,matrix⟩ := native.prepared.physicalRead
    have physical := Qleisli.Raw.PureInstrumentAction.reconstructed_action root.dependencies
      native.program native.prepared.physical work left matrix native.prepared.verified.prepared
      original (rawEvents ++ [finish]) pureEvents (action native.prepared.inputCode joint) row column bound
    rw [Qleisli.RawActionComposition.events_append] at physical
    exact physical.symm.trans ((RuntimePureProviderNative.checked_native_action checked).2 joint row column bound)

/-- The actual reconstruction binds its row count to the final original
frame, and its column count to the original input frame. -/
theorem native_dimensions {artifact context description graph index request header root demand}
    (checked : @RuntimeProviderAction.Checked artifact context description graph index request header root demand)
    (last : RuntimeInterval.Checked checked.originalBody.body.result.prepared.block
      checked.originalBody.body.result.prepared.block.operations.length 0) :
    let native := checked.paths.ir.original
    native.prepared.physical.rows = 2^last.before.quantum.frame.length ∧
      native.prepared.physical.cols = 2^native.prepared.verified.prepared.inputBits := by
  intro native
  obtain ⟨_,_,original,_,frame⟩ := actual_trace checked last
  obtain ⟨work,left,read⟩ := native.prepared.physicalRead
  unfold Raw.BranchFunction.reconstruct at read
  obtain ⟨checkedProgram,_,verified,rest⟩ := bind_success _ _ _ _ _ read
  obtain ⟨_,_,_,rest⟩ := bind_success _ _ _ _ _ rest
  obtain ⟨_,_,_,rest⟩ := bind_success _ _ _ _ _ rest
  obtain ⟨_,_,_,rest⟩ := bind_success _ _ _ _ _ rest
  obtain ⟨history,_,_,rest⟩ := bind_success _ _ _ _ _ rest
  obtain ⟨_,_,guarded,returned⟩ := bind_success _ _ _ _ _ rest
  have sizes := (guard_success _ _ _ _ guarded).1
  simp only [Bool.and_eq_true,beq_iff_eq] at sizes
  have operator := (pure_success _ _ _ _ returned).1
  have postcondition := Raw.Observation.verify_postcondition _ _ _ _ _ verified
  have same := Option.some.inj (postcondition.reader.symm.trans original)
  have sameFrame := congrArg Semantics.RawTrace.Interface.frame
    ((congrArg Semantics.Observation.Prepared.state same).trans frame)
  have widths := congrArg List.length (postcondition.frame.symm.trans sameFrame)
  exact ⟨(congrArg Semantics.Exact.Matrix.rows operator).trans
    (sizes.1.2.trans (congrArg (fun width => 2^width) widths)),
    (congrArg Semantics.Exact.Matrix.cols operator).trans (same ▸ sizes.2)⟩

#print axioms native_dimensions
#print axioms actual_trace
#print axioms native_execution
end Qleisli.RuntimePureProviderExecution
