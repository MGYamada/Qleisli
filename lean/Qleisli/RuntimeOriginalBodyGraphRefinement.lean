import Qleisli.RuntimeSelectionGraphAction
import Qleisli.RuntimeLiteralConditionalRefinement
import Protocol.NativeContext.Bindings

/-! Reuse the original body induction with a source graph action at every
coherent selection, including selections in named bodies and selected branches.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeLiteralBody
open QleisliKernel QleisliKernel.Qirf QleisliKernel.SourceTypes
open QleisliKernel.Semantics.Observation (readOps)
open Qleisli.Semantics.ObservingAction (History run)
open RuntimePureBody (Step runBlockCore)
open RuntimeSelectionSteps (Edge)
open RuntimeNamedChildRuns (CheckedStepAt RootInputs SelectionOrigin)
open RuntimeSelectionGraphAction (original_coefficients selection_history_with sourceGraphSelection)

noncomputable def plannedBodyLeaves {artifact : Artifact} (catalogue : GenericCatalogue.Checked artifact.sources)
    (root : Validity.Root) : ScopedSourceSteps root.dependencies := by
  classical
  exact fun scope prior step source =>
    match step with
    | .pure node@(.selection ..) =>
      if original : SelectionOrigin (RuntimeSelectionGraphSource.execution artifact catalogue root) node then
        let atSelection := scope ++ [.atOrdinal prior.length]
        sourceGraphSelection node (Classical.choose (original_coefficients catalogue root atSelection original)) source
      else none
    | _ => recursiveBodyLeaves scope prior step source

theorem plannedBodyLeaves_refine {artifact : Artifact} (catalogue : GenericCatalogue.Checked artifact.sources)
    (root : Validity.Root) (depth : Nat) (origin : RootInputs)
    (scope : List Edge) (inputs : List Nat) (inherited : Option (Nat → Prop))
    {program block} (steps : List (Step root.dependencies program block)) :
    StepRefinement steps
      (fun step => CheckedStepAt
        (runBlockCore artifact root (RuntimeSelectionGraphSource.execution artifact catalogue root) depth) origin step ∧
        RecursiveLeaf step)
      (plannedBodyLeaves catalogue root scope) (fun _ => SemanticHistoryAgreesWithInherited inherited inputs)
      (inherited.map (fun holds id => ¬ holds id)) := by
  intro prior first later position checked ownerBefore ownerAfter ordinaryBefore ordinaryAfter
    owners ordinary chunk read
  refine WithChunkWriteBound.of_trace ?_
  intro writes source history outputs agrees executed
  cases first
  case pure node =>
    cases node
    case selection start count inputTokens outputTokens selector target selectorBits targetBits
        restriction inputCode outputCode labels arms logical equations layouts frame restricted codes =>
      let node := RuntimePureBody.Node.selection frame selectorBits targetBits restriction
        restricted inputCode outputCode labels arms logical equations codes layouts
      have original : SelectionOrigin (RuntimeSelectionGraphSource.execution artifact catalogue root) node := checked.1
      let atSelection := scope ++ [.atOrdinal prior.length]
      obtain ⟨owner,name,written,offset,selectorBasis,targetBasis,naturals,writtenScope,table,sourceRead,ordered⟩ :=
        Classical.choose_spec (original_coefficients catalogue root atSelection original)
      obtain ⟨expected,evaluated,paired⟩ := selection_history_with frame restricted equations codes layouts
        ordered.2.2.2.1 inputs inherited owners ordinary read agrees executed
      refine ⟨expected,?_,paired⟩
      rw [plannedBodyLeaves, dif_pos original]
      exact evaluated
    all_goals
      exact ((recursiveLeafRefinement scope inputs inherited steps _ prior _ later position
        checked owners ordinary read).apply writes) agrees executed
  all_goals
    exact ((recursiveLeafRefinement scope inputs inherited steps _ prior _ later position
      checked owners ordinary read).apply writes) agrees executed

/-- Refine the full original body and return on its checked root row,
using the original source graph at every coherent selection. The same walk
accounts for named calls, ordinary branches and the ordered returned histories. -/
theorem original_body_graph_refinement {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime)
    {assignment : List Bool} (row : RuntimeOrdinaryInputs.Row body.checked.initial assignment)
    (scope : List Edge) (sourceInitial : SourceHistory) (initial : History)
    (results : List History)
    (executed : let block := body.checked.native.block
      (do
        let (_,events) ← readOps block.fuel block.entry.quantum.reference block.operations
        run body.root.dependencies block.fuel events initial) = some results) :
    let block := body.checked.native.block
    let source := SourceRuntimeScope.Subject.whole prepared.source.body
    let history := RuntimeBodyOperations.initialHistory prepared body.checked.native runtime body.checked.inputs
    (∀ input : RuntimeOwnerMap.Checked source.initialRoles block.entry,
      RuntimeInterval.Computed (RuntimePureBody.reordered source.initialRoles block.entry history.bindings) input →
      SemanticHistoryAgrees row.ordinals block.entry {history with bindings := input.bindings} body.checked.initial.ssa sourceInitial initial) →
    ∃ ownerEnd : RuntimeStructuralAction.SourceState,
    ∃ last : RuntimeInterval.Checked block block.operations.length 0,
      RuntimeInterval.Computed (RuntimeInterval.check block block.operations.length 0) last ∧
      ∃ returned : RuntimeOwnerMap.Checked source.outputRoles last.after,
        RuntimeInterval.Computed (RuntimePureBody.reordered source.outputRoles last.after ownerEnd.bindings) returned ∧
        body.checked.result.history = {ownerEnd with bindings := returned.bindings} ∧
        ∃ expected, runSourceHistories (recursiveSourceSteps (plannedBodyLeaves prepared.source.catalogue body.root) row.ordinals 127 scope) [] body.checked.result.steps [sourceInitial] = some expected ∧
          List.Forall₂ (SemanticHistoryAgrees row.ordinals last.after body.checked.result.history body.checked.result.ordinary)
            (expected.map (returnHistory returned.bindings)) results := by
  intro block source history starts
  obtain ⟨_,_,_,flow,_⟩ := RuntimeNamedChildRuns.original_body body
  exact original_body_encoded_refinement body SemanticHistoryEncoding row.ordinals
    (sparseArmEncodingLaws row.ordinals) sourceInitial initial results
    (recursiveSourceSteps (plannedBodyLeaves prepared.source.catalogue body.root) row.ordinals 127 scope) executed
    (recursiveSourceSteps_refine (plannedBodyLeaves prepared.source.catalogue body.root) row.ordinals
      (RuntimeBranchCondition.rootEntries (.root prepared.source.body)) (rootConditionRow_of_checked row)
      (fun depth {program block} atStep steps _ _ inherited =>
        plannedBodyLeaves_refine prepared.source.catalogue body.root depth _ atStep row.ordinals inherited steps)
      127 scope body.checked.result.steps body.selections.witness none
      (RuntimeNamedChildRuns.original_body_runtime_only body) flow.conditions) starts

/-! The public theorem starts at the actual native dispatcher. The original
source, checked body and compared execution view all come from that decision.
Initial encoded amplitudes and successful mathematical execution remain explicit
premises; this is not a theorem about compiled IO or the Rust simulator. -/
theorem native_qmatch_body_graph_refinement
    (product : String) (bytes : ByteArray)
    (decision : Protocol.NativeContext.Decision .qmatchSourceV5) (work left : Nat)
    (accepted : (Protocol.NativeContext.run .qmatchSourceV5 product bytes).run work = (.ok decision,left))
    {assignment : List Bool}
    (row : RuntimeOrdinaryInputs.Row decision.value.2.checked.checked.initial assignment)
    (sourceInitial : SourceHistory) (initial : History) (results : List History)
    (executed : let body := decision.value.2.checked
      let block := body.checked.native.block
      (do
        let (_,events) ← readOps block.fuel block.entry.quantum.reference block.operations
        run body.root.dependencies block.fuel events initial) = some results) :
    let original := decision.value.2
    let body := original.checked
    let prepared := original.prepared
    let block := body.checked.native.block
    let source := SourceRuntimeScope.Subject.whole prepared.source.body
    let history := RuntimeBodyOperations.initialHistory prepared body.checked.native
      original.request.combinedRuntime body.checked.inputs
    (∀ input : RuntimeOwnerMap.Checked source.initialRoles block.entry,
      RuntimeInterval.Computed (RuntimePureBody.reordered source.initialRoles block.entry history.bindings) input →
      SemanticHistoryAgrees row.ordinals block.entry {history with bindings := input.bindings}
        body.checked.initial.ssa sourceInitial initial) →
    Protocol.ExecutionView.Packet.read bytes = .ok decision.value.1 ∧
      decision.value.1.scope = .execution ∧
      Nonempty (Protocol.ExecutionView.CheckedQmatchV5.Binding decision.value.1.original
        decision.value.1.graph original work left) ∧
      ∃ ownerEnd : RuntimeStructuralAction.SourceState,
      ∃ last : RuntimeInterval.Checked block block.operations.length 0,
        RuntimeInterval.Computed (RuntimeInterval.check block block.operations.length 0) last ∧
        ∃ returned : RuntimeOwnerMap.Checked source.outputRoles last.after,
          RuntimeInterval.Computed (RuntimePureBody.reordered source.outputRoles last.after ownerEnd.bindings) returned ∧
          body.checked.result.history = {ownerEnd with bindings := returned.bindings} ∧
          ∃ expected, runSourceHistories
              (recursiveSourceSteps (plannedBodyLeaves prepared.source.catalogue body.root) row.ordinals 127 [])
              [] body.checked.result.steps [sourceInitial] = some expected ∧
            List.Forall₂
              (SemanticHistoryAgrees row.ordinals last.after body.checked.result.history body.checked.result.ordinary)
              (expected.map (returnHistory returned.bindings)) results := by
  intro original body prepared block source history starts
  obtain ⟨packet,scope,binding⟩ :=
    Protocol.NativeContext.run_qmatch_v5_binding product bytes decision work left accepted
  exact ⟨packet,scope,binding,
    original_body_graph_refinement body row [] sourceInitial initial results executed starts⟩

/-- The same decision supplies an original row for every canonical ordinary
assignment. A caller cannot replace the checked domain with selected examples. -/
theorem native_qmatch_input_rows
    (product : String) (bytes : ByteArray)
    (decision : Protocol.NativeContext.Decision .qmatchSourceV5) (work left : Nat)
    (accepted : (Protocol.NativeContext.run .qmatchSourceV5 product bytes).run work = (.ok decision,left)) :
    Protocol.ExecutionView.Packet.read bytes = .ok decision.value.1 ∧
      ∀ assignment ∈ OrdinaryDomain.assignments decision.value.2.checked.checked.initial.domain,
        Nonempty (RuntimeOrdinaryInputs.Row decision.value.2.checked.checked.initial assignment) := by
  refine ⟨(Protocol.NativeContext.run_qmatch_v5_binding product bytes decision work left accepted).1,?_⟩
  intro assignment member
  obtain ⟨row⟩ := RuntimeOrdinaryHistories.Rows.every
    decision.value.2.checked.checked.ordinary.rows assignment member
  exact ⟨row.input⟩

#print axioms original_body_graph_refinement
#print axioms native_qmatch_body_graph_refinement
#print axioms native_qmatch_input_rows
end Qleisli.RuntimeLiteralBody
