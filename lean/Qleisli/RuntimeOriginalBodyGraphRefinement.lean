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
open RuntimeNamedChildRuns (CheckedStepAt RootInputs SelectionOrigin MixedSelectionOrigin)
open RuntimeSelectionGraphAction (original_coefficients selection_history_with sourceGraphSelection
  MixedOriginalCoefficients original_mixed_table_coefficients mixed_original_coefficients_agree
  SmallerPureLeafLaws selection_source_choices_eq)

private noncomputable def plannedBodyLeaf {artifact : Artifact} (catalogue : GenericCatalogue.Checked artifact.sources)
    (root : Validity.Root) (depth : Nat)
    (leaves : Nat → ScopedSourceSteps root.dependencies) : ScopedSourceSteps root.dependencies := by
  classical
  exact fun scope prior step source =>
    match step with
    | .pure node@(.selection ..) =>
      let atSelection := scope ++ [.atOrdinal prior.length]
      if original : SelectionOrigin (RuntimeSelectionGraphSource.execution artifact catalogue root) node then
        sourceGraphSelection node (Classical.choose (original_coefficients catalogue root atSelection original)) source
      else if mixed : ∃ coefficients, MixedOriginalCoefficients catalogue root depth leaves atSelection node coefficients then
        sourceGraphSelection node (Classical.choose mixed) source
      else none
    | _ => recursiveBodyLeaves scope prior step source

private noncomputable def earlierBodyLeaves {dependencies} (depth : Nat)
    (earlier : (lower : Nat) → lower < depth → ScopedSourceSteps dependencies) :
    Nat → ScopedSourceSteps dependencies :=
  fun lower {program block} =>
    if h : lower < depth then earlier lower h (program := program) (block := block)
    else fun _ _ _ _ => none

/-- Evaluate each written selection at the depth of its actual checked runner.
An inline child's source evaluation only uses strictly smaller depths. -/
noncomputable def plannedBodyLeaves {artifact : Artifact} (catalogue : GenericCatalogue.Checked artifact.sources)
    (root : Validity.Root) : Nat → ScopedSourceSteps root.dependencies :=
  WellFounded.fix Nat.lt_wfRel.wf (C := fun _ => ScopedSourceSteps root.dependencies) fun depth earlier =>
    plannedBodyLeaf catalogue root depth (earlierBodyLeaves depth earlier)

private theorem plannedBodyLeaves_unfold {artifact : Artifact} (catalogue : GenericCatalogue.Checked artifact.sources)
    (root : Validity.Root) (depth : Nat) {program} {block : RuntimeInterval.Block root.dependencies program} :
    plannedBodyLeaves catalogue root depth (block := block) =
      plannedBodyLeaf catalogue root depth (earlierBodyLeaves depth fun lower _ => plannedBodyLeaves catalogue root lower)
        (block := block) := by
  conv_lhs =>
    unfold plannedBodyLeaves
    rw [WellFounded.fix_eq]
  all_goals rfl

private theorem plannedBodyLeaf_refine {artifact : Artifact} (catalogue : GenericCatalogue.Checked artifact.sources)
    (root : Validity.Root) (depth : Nat) (leaves : Nat → ScopedSourceSteps root.dependencies)
    (origin : RootInputs) (scope : List Edge) (inputs : List Nat) (inherited : Option (Nat → Prop))
    {program block} (steps : List (Step root.dependencies program block))
    (localLeaves : SmallerPureLeafLaws catalogue root depth leaves inputs) :
    StepRefinement steps
      (fun step => CheckedStepAt
        (runBlockCore artifact root (RuntimeSelectionGraphSource.execution artifact catalogue root) depth) origin step ∧
        RecursiveLeaf step)
      (plannedBodyLeaf catalogue root depth leaves scope) (fun _ => SemanticHistoryAgreesWithInherited inherited inputs)
      (inherited.map (fun holds id => ¬ holds id)) := by
  classical
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
      let atSelection := scope ++ [.atOrdinal prior.length]
      have origin : SelectionOrigin (RuntimeSelectionGraphSource.execution artifact catalogue root) node ∨
          MixedSelectionOrigin (RuntimeSelectionGraphSource.execution artifact catalogue root)
            (runBlockCore artifact root (RuntimeSelectionGraphSource.execution artifact catalogue root) depth) node :=
        checked.1
      rcases origin with original | original
      · obtain ⟨owner,name,written,offset,selectorBasis,targetBasis,naturals,writtenScope,table,sourceRead,ordered⟩ :=
          Classical.choose_spec (original_coefficients catalogue root atSelection original)
        obtain ⟨expected,evaluated,paired⟩ := selection_history_with frame restricted equations codes layouts
          ordered.2.2.2.1 inputs inherited owners ordinary read agrees executed
        refine ⟨expected,?_,paired⟩
        rw [plannedBodyLeaf, dif_pos original]
        exact evaluated
      · obtain ⟨rootOwner,rootName,owner,name,event,position,selection,path,parent,armRuns⟩ := original
        obtain ⟨authored,fromTable⟩ := original_mixed_table_coefficients catalogue root depth leaves atSelection inputs
          selection path parent localLeaves armRuns
        have authoredRelated : List.Forall₂ RuntimeSelectionGraphHistory.Coefficients arms authored :=
          fromTable.2.2.2.1
        obtain ⟨expected,evaluated,paired⟩ := selection_history_with frame restricted equations codes layouts
          authoredRelated inputs inherited owners ordinary read agrees executed
        have agreesWithAuthored {selected : List RuntimeGraphCoefficients.Coefficient}
            (selectedRelated : List.Forall₂ RuntimeSelectionGraphHistory.Coefficients arms selected) :
            sourceGraphSelection node selected source = some expected :=
          (selection_source_choices_eq frame restricted equations codes layouts selectedRelated authoredRelated
            inputs inherited owners agrees).trans evaluated
        refine ⟨expected,?_,paired⟩
        by_cases named : SelectionOrigin (RuntimeSelectionGraphSource.execution artifact catalogue root) node
        · obtain ⟨_,_,_,_,_,_,_,_,_,_,ordered⟩ :=
            Classical.choose_spec (original_coefficients catalogue root atSelection named)
          rw [plannedBodyLeaf, dif_pos named]
          exact agreesWithAuthored ordered.2.2.2.1
        · have available : ∃ coefficients, MixedOriginalCoefficients catalogue root depth leaves atSelection node coefficients :=
            ⟨authored,rootOwner,rootName,owner,name,event,position,selection,path,parent,fromTable⟩
          rw [plannedBodyLeaf, dif_neg named, dif_pos available]
          exact agreesWithAuthored (mixed_original_coefficients_agree (Classical.choose_spec available))
    all_goals
      exact ((recursiveLeafRefinement scope inputs inherited steps _ prior _ later position
        checked owners ordinary read).apply writes) agrees executed
  all_goals
    exact ((recursiveLeafRefinement scope inputs inherited steps _ prior _ later position
      checked owners ordinary read).apply writes) agrees executed

theorem plannedBodyLeaves_refine {artifact : Artifact} (catalogue : GenericCatalogue.Checked artifact.sources)
    (root : Validity.Root) (inputs : List Nat) :
    ∀ depth (origin : RootInputs) (scope : List Edge) (inherited : Option (Nat → Prop))
      {program block} (steps : List (Step root.dependencies program block)),
    StepRefinement steps
      (fun step => CheckedStepAt
        (runBlockCore artifact root (RuntimeSelectionGraphSource.execution artifact catalogue root) depth) origin step ∧
        RecursiveLeaf step)
      (plannedBodyLeaves catalogue root depth scope) (fun _ => SemanticHistoryAgreesWithInherited inherited inputs)
      (inherited.map (fun holds id => ¬ holds id)) := by
  intro depth
  induction depth using Nat.strongRecOn with
  | ind depth earlier =>
    intro origin scope inherited program block steps
    rw [plannedBodyLeaves_unfold]
    refine plannedBodyLeaf_refine catalogue root depth _ origin scope inputs inherited steps ?_
    intro lower within childOrigin childProgram childBlock childScope childSteps _ childInherited
    simp only [earlierBodyLeaves, dif_pos within]
    apply pureLeafRefinement_of_semantic childSteps _ _ inputs childInherited
    refine (earlier lower within childOrigin childScope childInherited childSteps).of_certifies ?_
    intro step law
    refine ⟨law.1,?_⟩
    cases step with
    | pure node => cases node <;> exact law.2
    | _ => exact False.elim law.2

/-- Refine the full original body and return on its checked root row,
using the original arm evaluations at every coherent selection. The same walk
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
        ∃ expected, runSourceHistories (recursiveSourceStepsAt (plannedBodyLeaves prepared.source.catalogue body.root) row.ordinals 127 scope) [] body.checked.result.steps [sourceInitial] = some expected ∧
          List.Forall₂ (SemanticHistoryAgrees row.ordinals last.after body.checked.result.history body.checked.result.ordinary)
            (expected.map (returnHistory returned.bindings)) results := by
  intro block source history starts
  obtain ⟨_,_,_,flow,_⟩ := RuntimeNamedChildRuns.original_body body
  exact original_body_encoded_refinement body SemanticHistoryEncoding row.ordinals
    (sparseArmEncodingLaws row.ordinals) sourceInitial initial results
    (recursiveSourceStepsAt (plannedBodyLeaves prepared.source.catalogue body.root) row.ordinals 127 scope) executed
    (recursiveSourceStepsAt_refine (plannedBodyLeaves prepared.source.catalogue body.root) row.ordinals
      (RuntimeBranchCondition.rootEntries (.root prepared.source.body)) (rootConditionRow_of_checked row)
      (fun depth {program block} atStep steps _ _ inherited =>
        plannedBodyLeaves_refine prepared.source.catalogue body.root row.ordinals depth _ atStep inherited steps)
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
              (recursiveSourceStepsAt (plannedBodyLeaves prepared.source.catalogue body.root) row.ordinals 127 [])
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
