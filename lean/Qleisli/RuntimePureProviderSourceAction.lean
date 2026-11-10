import Qleisli.RuntimePureProviderBoundary

/-! Evaluate the original provider source on the same encoded input as its
checked program, and compare the returned operator on every physical row.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimePureProviderSourceAction
open QleisliKernel QleisliKernel.Qirf QleisliKernel.SourceTypes
open RuntimeSelectionSteps (Edge)
open RuntimeForestCode (forestAxes sparseEntry)
open RuntimeSemanticForest (Frame)
open Qleisli.RuntimeLiteralBody
open Qleisli.Semantics.Exact (action scalar)
open Qleisli.Semantics.ObservingAction (History)
open Qleisli.RuntimeNamedThreePackedOutput (readerFinish final_axes final_axes_permutation)
open Qleisli.RuntimePureProviderBoundary (packedAction)

/-- The independently evaluated original source and the verified logical
matrix have equal physical coefficients after the actual provider return. -/
theorem source_execution {artifact context description graph index request header root demand}
    (checked : @RuntimeProviderAction.Checked artifact context description graph index request header root demand)
    (scope : List Edge) (joint : Nat → Nat → ℂ) :
    let native := checked.paths.ir.original
    let body := checked.originalBody.body
    let subject := SourceRuntimeScope.Subject.whole header.original.body
    let block := body.result.prepared.block
    let source : RuntimeStructuralAction.SourceState :=
      ⟨checked.originalBody.initial,header.original.body.checked.summary.parameterValues.flatMap
        SourceRuntimeValues.valueOwners,header.original.body.checked.summary.nextOwner⟩
    let initial : SourceHistory := ⟨source,[],[],joint,[]⟩
    ∃ last : RuntimeInterval.Checked block block.operations.length 0,
      ∃ returned : RuntimeOwnerMap.Checked subject.outputRoles last.after,
        ∃ result : SourceHistory, ∃ output : Frame body.result.history.bindings,
          RuntimeInterval.Computed (RuntimeInterval.check block block.operations.length 0) last ∧
          returned.bindings = body.result.history.bindings ∧
          runSourceHistories (pureRecursiveSourceSteps recursiveBodyLeaves 127 scope) [] body.result.steps
            [initial] = some [result] ∧
          ∀ row column, row < native.prepared.physical.rows →
            packedAction output (returnHistory returned.bindings result).operator row column =
              action native.prepared.outputCode (fun i ref => action checked.action joint i ref) row column := by
  intro native body subject block source initial
  obtain ⟨_,_,_,_,⟨last,_,_,_,_⟩,_⟩ := RuntimeNamedChildRuns.original_pure_body body
  let input : History := ⟨[],[],action native.prepared.inputCode joint⟩
  obtain ⟨final,performed,matrixAction⟩ := RuntimePureProviderExecution.native_execution checked last joint
  obtain ⟨_,exit,exitRead,returned,_,returnMap,results,evaluated,paired⟩ :=
    original_pure_provider_refinement body [] scope initial input [final] performed
      (fun entry entryRead => RuntimePureProviderBoundary.input_agreement checked joint entry entryRead)
  have resultCount : results.length = 1 := by
    simpa only [List.length_map,List.length_singleton] using paired.length_eq
  obtain ⟨result,single⟩ := List.length_eq_one_iff.mp resultCount
  have related : Qleisli.RuntimeCallHistory.SourceAgreementWithin (some (· = {})) none [] exit.after
      body.result.history body.result.ordinary (returnHistory returned.bindings result) final := by
    rw [single,List.map_singleton] at paired
    cases paired with
    | cons head _ => exact head
  obtain ⟨_,_,_,_,_,_,physical,bindings,output,encoded⟩ := related
  have exactReturn : returned.bindings = body.result.history.bindings := congrArg (·.bindings) returnMap |>.symm
  refine ⟨exit,returned,result,output,exitRead,exactReturn,single ▸ evaluated,?_⟩
  obtain ⟨_,_,_,_,firstState⟩ := RuntimePureProviderExecution.actual_trace checked last
  obtain ⟨_,_,_,_,exitState⟩ := RuntimePureProviderExecution.actual_trace checked exit
  have lastState := firstState.symm.trans exitState
  have same : last.before.quantum.reference = exit.after.quantum.reference :=
    lastState.trans (congrArg (fun state : Raw.Observation.State => state.quantum.reference)
      (Qleisli.RuntimeOwnerTransitionAction.empty_state exit).symm)
  obtain ⟨before,after,verified⟩ := native.prepared.verification
  have checkedState := Raw.Observation.verify_postcondition _ _ _ _ _ verified
  have finalLive : exit.after.quantum.live = [native.prepared.ports.output] := by
    have states := congrArg Semantics.RawTrace.Interface.live (firstState.trans same)
    exact states.symm.trans (checkedState.live.trans native.prepared.ports.live)
  have tokens : native.program.outputs = physical.bindings.map (fun b => b.port.token) := by
    have ports : (physical.bindings.map (·.port)).Perm [native.prepared.ports.output] := finalLive ▸ physical.complete
    have count := ports.length_eq
    obtain ⟨port,singlePort⟩ := List.length_eq_one_iff.mp count
    have original : port = native.prepared.ports.output := by
      have present : port ∈ physical.bindings.map (·.port) := by simp [singlePort]
      simpa only [List.mem_singleton] using ports.mem_iff.mp present
    have packed := congrArg (List.map (fun p : Semantics.Raw.Port => p.token))
      (singlePort.trans (congrArg (fun p => [p]) original))
    simpa only [List.map_map,Function.comp_def,List.map_cons,List.map_nil] using
      native.prepared.ports.outputPort.trans packed.symm
  have valid := exit.history.2.2.1
  have finish : readerFinish native.program last.before.quantum.reference =
      .reorder exit.after.quantum.frame.length (forestAxes exit.after.quantum.frame body.result.history.bindings) := by
    rw [same,← bindings]
    unfold readerFinish
    rw [tokens]
    exact congrArg (Semantics.Raw.Event.reorder exit.after.quantum.frame.length) (final_axes physical valid)
  have permutation := final_axes_permutation physical valid
  rw [bindings] at permutation
  have width := congrArg (fun interface : Semantics.RawTrace.Interface => interface.frame.length) same
  have rows := (RuntimePureProviderExecution.native_dimensions checked last).1
  change last.before.quantum.frame.length = exit.after.quantum.frame.length at width
  intro row column bound
  have rowsEq : native.prepared.physical.rows = 2^exit.after.quantum.frame.length :=
    rows.trans (congrArg (fun bits => 2^bits) width)
  have rowBound : row < 2^exit.after.quantum.frame.length := by rw [← rowsEq]; exact bound
  have raw := matrixAction row column bound
  rw [finish] at raw
  obtain ⟨physicalRow,inside,coordinate,applied⟩ := RuntimeNamedThreePackedOutput.reorder_gather root.dependencies
    _ _ permutation (fun i => final.operator i column) row rowBound
  rw [applied,encoded column physicalRow inside] at raw
  unfold RuntimeSemanticForest.action RuntimeForestCode.embed at raw
  rw [coordinate] at raw
  exact raw

#print axioms source_execution
end Qleisli.RuntimePureProviderSourceAction
