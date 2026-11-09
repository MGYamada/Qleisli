import Qleisli.RuntimeLiteralLocalRefinement
import Qleisli.RuntimeBranchInputDomain
import Qleisli.RuntimeLiteralSparseObservation
import Qleisli.RuntimeLiteralSparseInline
import Qleisli.RuntimeLiteralSparseNamed
import Qleisli.RuntimeLiteralSparseSelection
import Qleisli.RuntimeOriginalSparsePhi

/-! A conditional uses the original prefix to select an arm, applies the
shared recursion to its real child receipt, and passes that exact ordered
result family through the parent phis.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeLiteralBody
open QleisliKernel QleisliKernel.Qirf QleisliKernel.SourceTypes
open QleisliKernel.Semantics.Observation (Event readOps)
open Qleisli.Semantics.ObservingAction (History run)
open Qleisli.RuntimeLiteralBranchChoice (measurementBits measurementBits_retains reference_measurement_row
  sourceChoice sourceChoice_eval_iff)
open Qleisli.RuntimeOriginalBranchJoin
  (armChecked armPermutation original_arm_run original_branch_join_with_inherited original_native_phi_history sourcePhiIndex)
open Qleisli.RuntimeOriginalSparsePhi (original_sparse_phi_history)
open Qleisli.RuntimeNamedThreePackedInstrument (pureHistory)
open Qleisli.RuntimeNamedChildRuns (CheckedStep ChildRun ConditionalRun)
open Qleisli.RuntimeObservingValueRetention (Supports run_values run_retains_values)
open Qleisli.RuntimeObservingPrefix (Issued issued_mono)
open Qleisli.RuntimeObservingWrites (WritesWithin)
open RuntimePureBody (Step Steps runBlockCore)
open RuntimeOrdinarySSA (Agreement bitValue)
open RuntimeSelectionSteps (Edge)
open RuntimeNamedPrimitiveOccurrence (inspect?)

abbrev ScopedSourceSteps (dependencies : List RuntimeInterval.Dependency) :=
  ∀ {program} {block : RuntimeInterval.Block dependencies program},
    List Edge → List (Step dependencies program block) → Step dependencies program block →
      SourceHistory → Option (List SourceHistory)

private def armScope (scope : List Edge) (ordinal : Nat) (choice : Bool) : List Edge :=
  scope ++ [if choice then .thenBranch ordinal else .elseBranch ordinal]

private def enterArm (scope : List Edge) (ordinal : Nat) (choice : Bool) (history : SourceHistory) : SourceHistory :=
  {history with branches := history.branches ++ [(scope ++ [.atOrdinal ordinal],choice)]}

private noncomputable def runArms {sources caller event dependencies program block offset}
    (body : @RuntimeBranchAction.Source sources caller event)
    (actual : @RuntimeInterval.Branch dependencies program block offset)
    (left : Steps dependencies program actual.thenBlock) (right : Steps dependencies program actual.elseBlock)
    (other : ScopedSourceSteps dependencies) (scope : List Edge) (ordinal : Nat)
    (source : SourceHistory) (choice : Bool) : Option (List SourceHistory) :=
  let atArm := armScope scope ordinal choice
  let inputRoles := event.held ++ SourceRuntimeValues.owners event.before
  let incoming := enterArm scope ordinal choice source
  if choice then runSourceArm (other atArm) inputRoles
    (RuntimeBranchAction.leftRoles body) (stepList left) incoming
  else runSourceArm (other atArm) inputRoles
    (RuntimeBranchAction.rightRoles body) (stepList right) incoming

private theorem same_measurements {first second : List RuntimeOrdinaryBody.Measurement}
    (checked : RuntimeBranchAction.sameMeasurements first second = true) : first = second := by
  induction first generalizing second with
  | nil => cases second <;> simp [RuntimeBranchAction.sameMeasurements] at checked ⊢
  | cons first rest ih =>
    cases second with
    | nil => simp [RuntimeBranchAction.sameMeasurements] at checked
    | cons second tail =>
      simp only [RuntimeBranchAction.sameMeasurements,List.length_cons,beq_iff_eq,Nat.succ.injEq,
        List.zip_cons_cons,List.all_cons,Bool.and_eq_true,decide_eq_true_eq] at checked
      have sameHead : first = second := by
        cases first
        cases second
        simpa only [RuntimeOrdinaryBody.Measurement.mk.injEq] using checked.2.1
      have sameTail : rest = tail := ih (by
        simp only [RuntimeBranchAction.sameMeasurements,Bool.and_eq_true,beq_iff_eq]
        exact ⟨checked.1,checked.2.2⟩)
      rw [sameHead,sameTail]

private theorem Forall₂.with_result {A B : Type} {rel : A → B → Prop} {sources results}
    (paired : List.Forall₂ rel sources results) {next : A → B → Prop}
    (each : ∀ expected actual, actual ∈ results → rel expected actual → next expected actual) :
    List.Forall₂ next sources results := by
  induction paired with
  | nil => exact .nil
  | cons pair _ ih =>
    exact .cons (each _ _ List.mem_cons_self pair) (ih fun source result found =>
      each source result (List.mem_cons_of_mem _ found))

private theorem arm_results {dependencies program} {block : RuntimeInterval.Block dependencies program}
    {outputRoles} {before : RuntimeStructuralAction.SourceState}
    {ordinary finalOrdinary : RuntimeOrdinaryBody.State}
    {rawExit events} {history : History} {results expected}
    (encoding : HistoryEncoding) (inputs : List Nat) (bits : List Bool) (inherited : Option (Nat → Prop))
    (measurements : finalOrdinary.measurements = ordinary.measurements)
    (bitsRead : measurementBits ordinary.measurements history.values = some bits)
    (returned : @RuntimeOwnerMap.Checked outputRoles rawExit)
    (bindings : returned.bindings = before.bindings)
    (executed : run dependencies block.fuel events history = some results)
    (paired : List.Forall₂ (EncodedHistoryAgreesWithInherited encoding inherited inputs rawExit before finalOrdinary) expected results) :
    List.Forall₂ (fun source actual =>
      source.measurements = bits ∧ actual.hidden = source.outcomes.map Prod.snd ∧
      Agreement (RuntimeBranchCondition.reference inputs ordinary.measurements bits) actual.values finalOrdinary.table ∧
      encoding rawExit returned.bindings actual.operator source.operator) expected results := by
  apply Forall₂.with_result paired
  intro source actual present matched
  have oldBits := measurementBits_retains _ (run_retains_values _ _ _ _ executed actual present) bitsRead
  have currentBits := matched.2.2.1
  rw [measurements] at currentBits
  have values := matched.2.2.2.1.1
  rw [measurements,← (reference_measurement_row oldBits inputs).2] at values
  exact ⟨Option.some.inj (currentBits.symm.trans oldBits),matched.2.1,values,
    bindings.symm ▸ matched.2.2.2.2⟩

private noncomputable def finishArm {sources rootOwner rootName caller name dependencies program block offset
    path event body actual before left right ordinary leftOrdinary rightOrdinary}
    (action : @RuntimeBranchAction.Checked sources rootOwner rootName caller name dependencies program block offset
      path event body actual before left right ordinary leftOrdinary rightOrdinary)
    (choice : Bool) (source : SourceHistory) : SourceHistory :=
  { source with
    owners := action.next
    operator := fun row column => source.operator (sourcePhiIndex action.ownerPhis choice row) column}

/-- A condition uses the decoded row of its original checked input domain. -/
def ConditionInput {dependencies program block} (inputs : List Nat) :
    Step dependencies program block → Prop
  | .conditional _ _ _ _ _ action _ _ => inputs ∈ action.condition.inputs.rows
  | _ => True

private theorem child_condition_inputs {artifact root mode next program block before after steps
    ordinary finalOrdinary cursor sources rootOwner rootName owner name}
    {path : RuntimeOrdinaryBody.CallPath sources rootOwner rootName owner name}
    (flow : @RuntimeNamedChildRuns.Flow artifact root mode next (RuntimeBranchCondition.rootEntries path) program block
      before steps after ordinary finalOrdinary cursor)
    (parent : RuntimeBranchCondition.Inputs path) {inputs : List Nat} (member : inputs ∈ parent.rows) :
    ∀ step ∈ steps, ConditionInput inputs step := by
  intro step present
  have origin := flow.conditions step present
  cases step with
  | conditional _ _ _ _ _ action _ _ =>
    have rows := Qleisli.RuntimeBranchInputDomain.same_input_rows action.condition.inputs parent origin
    change inputs ∈ action.condition.inputs.rows
    rwa [rows]
  | _ => exact True.intro

private def ChildStepRefinement {dependencies program block offset}
    (actual : @RuntimeInterval.Branch dependencies program block offset)
    (left : Steps dependencies program actual.thenBlock) (right : Steps dependencies program actual.elseBlock)
    (certifies : ∀ {program block},Step dependencies program block → Prop)
    (encoding : HistoryEncoding) (inputs : List Nat) (other : ScopedSourceSteps dependencies)
    (scope : List Edge) (ordinal : Nat) (inherited : Option (Nat → Prop) := none) : Prop :=
  ((∀ step ∈ stepList left, ConditionInput inputs step) →
    StepRefinement (stepList left) certifies (other (armScope scope ordinal true))
      (fun _ => EncodedHistoryAgreesWithInherited encoding inherited inputs)
      (inherited.map (fun holds id => ¬ holds id))) ∧
  ((∀ step ∈ stepList right, ConditionInput inputs step) →
    StepRefinement (stepList right) certifies (other (armScope scope ordinal false))
      (fun _ => EncodedHistoryAgreesWithInherited encoding inherited inputs)
      (inherited.map (fun holds id => ¬ holds id)))

/-- The original condition and its actual selected arm determine the source
results before and after the same literal parent phi merge. -/
private theorem source_conditional_refines_with {artifact : Artifact} {root : Validity.Root}
    {mode : RuntimePureBody.ExecutionMode artifact root} {sources fuel program block offset rootOwner rootName caller name
    path event body actual actualRead before left right ordinary leftOrdinary rightOrdinary}
    (action : @RuntimeBranchAction.Checked sources rootOwner rootName caller name root.dependencies
      program block offset path event body actual before left right ordinary leftOrdinary rightOrdinary)
    (thenSteps : Steps root.dependencies program actual.thenBlock)
    (elseSteps : Steps root.dependencies program actual.elseBlock)
    (call : ConditionalRun artifact root mode (runBlockCore artifact root mode (fuel+1))
      (.conditional path event body actual actualRead action thenSteps elseSteps))
    (encoding : HistoryEncoding) (inputs : List Nat)
    {inherited : Option (Nat → Prop)} (laws : ArmEncodingLaws encoding inputs inherited)
    (transport : ∀ _trace : RuntimeOriginalBranch.Trace actual, ∀ choice joint (current : History),
      encoding (if choice then actual.thenState else actual.elseState)
        (armChecked action.thenFrame action.elseFrame choice).bindings current.operator joint →
      encoding actual.interval.after action.next.bindings
        (pureHistory root.dependencies [armPermutation actual choice] current).operator
        (fun row column => joint (sourcePhiIndex action.ownerPhis choice row) column))
    (member : inputs ∈ action.condition.inputs.rows) (other : ScopedSourceSteps root.dependencies)
    (scope : List Edge) (ordinal : Nat)
    (remaining : ChildStepRefinement actual thenSteps elseSteps
      (CheckedStep (runBlockCore artifact root mode fuel)) encoding inputs other scope ordinal inherited)
    {source history events results}
    (agrees : EncodedHistoryAgreesWithInherited encoding inherited inputs actual.interval.before before ordinary source history)
    (read : readOps block.fuel actual.interval.before.quantum.reference ((block.operations.drop offset).take 1) =
      some (actual.interval.after.quantum.reference,events))
    (executed : run root.dependencies block.fuel events history = some results)
    (bounded : TraceWriteBound (inherited.map (fun holds id => ¬ holds id)) events := by trivial) :
    ∃ choice expected,
      sourceChoice (RuntimeBranchCondition.reference inputs ordinary.measurements source.measurements)
        action.condition.required = some choice ∧
      runArms body actual thenSteps elseSteps other scope ordinal source choice = some expected ∧
      List.Forall₂ (EncodedHistoryAgreesWithInherited encoding inherited inputs actual.interval.after action.next action.ordinaryAfter)
        (expected.map (finishArm action choice)) results := by
  obtain ⟨trace,chosen,choiceRead,rawRun⟩ := source_branch_choice action.condition inputs member (inherited := inherited) agrees read
  have eventEq : events = [Qleisli.RuntimeOriginalBranch.branchEvent actual trace.left trace.right] :=
    congrArg Prod.snd (Option.some.inj (read.symm.trans trace.parentRead))
  let held := inherited.getD (fun _ => False)
  have branchWrites : WritesWithin [Qleisli.RuntimeOriginalBranch.branchEvent actual trace.left trace.right]
      (fun id => ¬ held id) := by
    cases inherited with
    | none => exact fun _ _ _ _ impossible => impossible
    | some _ => exact eventEq ▸ bounded
  have armWrites (choice : Bool) :
      TraceWriteBound (inherited.map (fun holds id => ¬ holds id)) (trace.armBody choice) := by
    cases inherited with
    | none => trivial
    | some holds =>
      intro event present id wrote
      cases choice
      · exact branchWrites List.mem_cons_self (.elseArm (List.mem_append.mpr (.inl present)) wrote)
      · exact branchWrites List.mem_cons_self (.thenArm (List.mem_append.mpr (.inl present)) wrote)
  have incomingSupport : Supports (fun id => held id ∨ Issued actual.interval.before id) history := by
    intro id present
    cases inherited with
    | none => exact .inr (agrees.2.2.2.1.2 present)
    | some _ => exact agrees.2.2.2.1.2 present
  have actualArm : ∃ returned, run root.dependencies actual.childFuel (trace.armBody chosen) history = some returned := by
    have ran := executed
    rw [rawRun,original_arm_run] at ran
    cases selected : run root.dependencies actual.childFuel (trace.armBody chosen) history with
    | none => simp [selected] at ran
    | some returned => exact ⟨returned,rfl⟩
  obtain ⟨returned,bodyRead⟩ := actualArm
  obtain ⟨leftRun,rightRun⟩ := conditional_arms (fuel := fuel) call trace
  let reference := RuntimeBranchCondition.reference inputs ordinary.measurements source.measurements
  have armProof : ∀ choice, Semantics.SourceOrdinary.evaluate reference action.condition.required = some (bitValue choice) →
      ∃ expected armReturned,
        runArms body actual thenSteps elseSteps other scope ordinal source choice = some expected ∧
        run root.dependencies actual.childFuel (trace.armBody choice) history = some armReturned ∧
        List.Forall₂ (fun logical result =>
          logical.measurements = source.measurements ∧ result.hidden = logical.outcomes.map Prod.snd ∧
          Agreement reference result.values (if choice then leftOrdinary.table else rightOrdinary.table) ∧
          encoding (if choice then actual.thenState else actual.elseState)
            (armChecked action.thenFrame action.elseFrame choice).bindings result.operator logical.operator) expected armReturned := by
    intro choice evaluates
    have same := Option.some.inj ((sourceChoice_eval_iff.mpr evaluates).symm.trans choiceRead)
    subst choice
    cases chosen with
    | false =>
      obtain ⟨arm⟩ := rightRun
      obtain ⟨expected,evaluated,paired⟩ := arm.refinement_with encoding inputs
        (enterArm scope ordinal false source) history (other (armScope scope ordinal false)) (inherited := inherited)
        (remaining.2 (child_condition_inputs arm.flow action.condition.inputs member)) laws agrees bodyRead (armWrites false)
      have bindings := congrArg RuntimeStructuralAction.SourceState.bindings arm.returned
      exact ⟨expected,returned,evaluated,bodyRead,arm_results (block := actual.elseBlock) encoding inputs source.measurements inherited
        (same_measurements action.noElseMeasurements).symm agrees.2.2.1 action.elseFrame bindings.symm bodyRead paired⟩
    | true =>
      obtain ⟨arm⟩ := leftRun
      obtain ⟨expected,evaluated,paired⟩ := arm.refinement_with encoding inputs
        (enterArm scope ordinal true source) history (other (armScope scope ordinal true)) (inherited := inherited)
        (remaining.1 (child_condition_inputs arm.flow action.condition.inputs member)) laws agrees bodyRead (armWrites true)
      have bindings := congrArg RuntimeStructuralAction.SourceState.bindings arm.returned
      exact ⟨expected,returned,evaluated,bodyRead,arm_results (block := actual.thenBlock) encoding inputs source.measurements inherited
        (same_measurements action.noThenMeasurements).symm agrees.2.2.1 action.thenFrame bindings.symm bodyRead paired⟩
  obtain ⟨width,sourceReference⟩ := reference_measurement_row agrees.2.2.1 inputs
  have incoming : Agreement reference history.values ordinary.table := by
    change Agreement (RuntimeBranchCondition.reference inputs ordinary.measurements source.measurements)
      history.values ordinary.table
    rw [sourceReference]
    exact agrees.2.2.2.1.1
  obtain ⟨choice,condition,expected,_,merged,sourceRead,_,mergeRead,paired⟩ :=
    original_branch_join_with_inherited action trace inputs member source.measurements width history held branchWrites
      (runArms body actual thenSteps elseSteps other scope ordinal source) (·.operator) (fun source => source.outcomes.map Prod.snd)
      (fun result => result.measurements = source.measurements)
      (fun choice => encoding (if choice then actual.thenState else actual.elseState)
        (armChecked action.thenFrame action.elseFrame choice).bindings)
      (encoding actual.interval.after action.next.bindings)
      (transport trace) incoming incomingSupport armProof
  have sameResults : merged = results := by
    have result := executed
    rw [eventEq,actual.depth,Qleisli.RuntimeLiteralHistory.run_single,mergeRead] at result
    exact Option.some.inj result
  subst merged
  obtain ⟨work,leftWork,checked⟩ := actual.interval.intervalRead
  obtain ⟨keeps,actualEvents,literal,writes⟩ := Qleisli.RuntimeObservingPrefix.checkOps_reference_with_writes
    root.dependencies block.fuel _ _ _ work leftWork checked
  have sameEvents : events = actualEvents := congrArg Prod.snd (Option.some.inj (read.symm.trans literal))
  rw [← sameEvents] at writes
  have facts := run_values root.dependencies block.fuel events history
    (fun id => held id ∨ Issued actual.interval.after id) (writes.mono (fun _ issued => .inr issued))
    (fun _ present => (incomingSupport present).imp (fun inside => inside) (issued_mono keeps)) executed
  have finalMeasurements := (congrArg RuntimeOrdinaryBody.State.measurements action.ordinaryRead).trans
    action.ordinaryVisible.measurements
  refine ⟨choice,expected,sourceChoice_eval_iff.mpr condition,sourceRead,?_⟩
  rw [List.forall₂_map_left_iff]
  apply Forall₂.with_result paired
  intro logical result present ⟨bits,hidden,values,represented⟩
  obtain ⟨retains,support⟩ := facts result present
  have measured := measurementBits_retains _ retains agrees.2.2.1
  have finalReference := (reference_measurement_row measured inputs).2
  change Agreement (RuntimeBranchCondition.reference inputs ordinary.measurements source.measurements)
    result.values action.ordinaryAfter.table at values
  rw [finalReference,← finalMeasurements] at values
  refine ⟨rfl,hidden,?_,⟨values,?_⟩,represented⟩
  · rw [finalMeasurements]
    exact measured.trans (congrArg some bits.symm)
  · intro id present
    cases inherited with
    | none => exact (support present).resolve_left (fun impossible => impossible)
    | some _ => exact support present

/-- The original condition and its actual selected arm determine the source
results before and after the same literal parent phi merge. -/
theorem source_conditional_refines {artifact : Artifact} {root : Validity.Root}
    {mode : RuntimePureBody.ExecutionMode artifact root} {sources fuel program block offset rootOwner rootName caller name
    path event body actual actualRead before left right ordinary leftOrdinary rightOrdinary}
    (action : @RuntimeBranchAction.Checked sources rootOwner rootName caller name root.dependencies
      program block offset path event body actual before left right ordinary leftOrdinary rightOrdinary)
    (thenSteps : Steps root.dependencies program actual.thenBlock)
    (elseSteps : Steps root.dependencies program actual.elseBlock)
    (call : ConditionalRun artifact root mode (runBlockCore artifact root mode (fuel+1+1))
      (.conditional path event body actual actualRead action thenSteps elseSteps))
    (inputs : List Nat) (member : inputs ∈ action.condition.inputs.rows) (other : ScopedSourceSteps root.dependencies)
    (remaining : ∀ {program block} (scope : List Edge) (steps : List (Step root.dependencies program block)),
      (∀ step ∈ steps, ConditionInput inputs step) →
      StepRefinement steps
        (fun step => CheckedStep (runBlockCore artifact root mode (fuel+1)) step ∧ NeedsSourceAction step)
        (other scope) (fun _ => HistoryAgrees inputs))
    (scope : List Edge) (ordinal : Nat) {source history events results}
    (agrees : HistoryAgrees inputs actual.interval.before before ordinary source history)
    (read : readOps block.fuel actual.interval.before.quantum.reference ((block.operations.drop offset).take 1) =
      some (actual.interval.after.quantum.reference,events))
    (executed : run root.dependencies block.fuel events history = some results) :
    ∃ choice expected,
      sourceChoice (RuntimeBranchCondition.reference inputs ordinary.measurements source.measurements)
        action.condition.required = some choice ∧
      runArms body actual thenSteps elseSteps (fun atArm => sourceStep (other atArm) atArm) scope ordinal source choice = some expected ∧
      List.Forall₂ (HistoryAgrees inputs actual.interval.after action.next action.ordinaryAfter)
        (expected.map (finishArm action choice)) results := by
  refine source_conditional_refines_with (fuel := fuel+1) action thenSteps elseSteps call NativeHistoryEncoding inputs
    (inherited := none) (nativeArmEncodingLaws inputs) ?_ member (fun atArm => sourceStep (other atArm) atArm)
    scope ordinal ?_ agrees read executed
  swap
  · exact ⟨fun rows => sourceStep_refines _ inputs _ _ (remaining _ _ rows),
      fun rows => sourceStep_refines _ inputs _ _ (remaining _ _ rows)⟩
  intro trace choice joint current encoded
  obtain ⟨frame,represented⟩ := NativeHistoryEncoding.represents (history := current) encoded
    (armChecked action.thenFrame action.elseFrame choice) rfl
  obtain ⟨output,result⟩ := original_native_phi_history actual action.ownerPhis trace choice joint current
    frame represented
  exact ⟨_,action.ownerPhis.output,action.bindings.symm,output,result⟩

/-- The original condition and its actual selected arm determine the source
results before and after the same literal parent phi merge. -/
theorem sparse_conditional_refines {artifact : Artifact} {root : Validity.Root}
    {mode : RuntimePureBody.ExecutionMode artifact root} {sources fuel program block offset rootOwner rootName caller name
    path event body actual actualRead before left right ordinary leftOrdinary rightOrdinary}
    (action : @RuntimeBranchAction.Checked sources rootOwner rootName caller name root.dependencies
      program block offset path event body actual before left right ordinary leftOrdinary rightOrdinary)
    (thenSteps : Steps root.dependencies program actual.thenBlock)
    (elseSteps : Steps root.dependencies program actual.elseBlock)
    (call : ConditionalRun artifact root mode (runBlockCore artifact root mode (fuel+1))
      (.conditional path event body actual actualRead action thenSteps elseSteps))
    (inputs : List Nat) (member : inputs ∈ action.condition.inputs.rows) (other : ScopedSourceSteps root.dependencies)
    (scope : List Edge) (ordinal : Nat) {inherited : Option (Nat → Prop)}
    (remaining : ChildStepRefinement actual thenSteps elseSteps
      (CheckedStep (runBlockCore artifact root mode fuel)) SemanticHistoryEncoding inputs other scope ordinal inherited)
    {source history events results}
    (agrees : SemanticHistoryAgreesWithInherited inherited inputs actual.interval.before before ordinary source history)
    (read : readOps block.fuel actual.interval.before.quantum.reference ((block.operations.drop offset).take 1) =
      some (actual.interval.after.quantum.reference,events))
    (executed : run root.dependencies block.fuel events history = some results)
    (bounded : TraceWriteBound (inherited.map (fun holds id => ¬ holds id)) events := by trivial) :
    ∃ choice expected,
      sourceChoice (RuntimeBranchCondition.reference inputs ordinary.measurements source.measurements)
        action.condition.required = some choice ∧
      runArms body actual thenSteps elseSteps other scope ordinal source choice = some expected ∧
      List.Forall₂ (SemanticHistoryAgreesWithInherited inherited inputs actual.interval.after action.next action.ordinaryAfter)
        (expected.map (finishArm action choice)) results := by
  refine source_conditional_refines_with action thenSteps elseSteps call SemanticHistoryEncoding inputs
    (inherited := inherited) (sparseArmEncodingLaws inputs inherited) ?_ member other scope ordinal remaining agrees read executed bounded
  intro trace choice joint current encoded
  obtain ⟨_,_,_,frame,represented⟩ := encoded
  obtain ⟨output,result⟩ := original_sparse_phi_history actual action.ownerPhis trace choice joint current frame represented
  have encodedOutput : SemanticHistoryEncoding actual.interval.after action.ownerPhis.output.bindings
      (pureHistory root.dependencies [armPermutation actual choice] current).operator
      (fun row column => joint (sourcePhiIndex action.ownerPhis choice row) column) :=
    ⟨_,action.ownerPhis.output,rfl,output,result⟩
  exact action.bindings.symm ▸ encodedOutput

/-- Every actual condition in the checked traversal has the original root's
decoded input row. This also applies to a child's retained traversal when
its call path reaches the same root. -/
theorem flow_condition_inputs {artifact root mode next rootInputs program block before after steps
    ordinary finalOrdinary cursor sources rootOwner rootName signature rootProgram}
    (flow : @RuntimeNamedChildRuns.Flow artifact root mode next rootInputs program block before steps after
      ordinary finalOrdinary cursor)
    {body : @SourceRuntimeTrace.Body sources rootOwner rootName signature}
    {prepared : RuntimeInterval.Prepared root.dependencies rootProgram} {runtime inputs}
    {initial : RuntimeOrdinaryInputs.Checked body prepared runtime inputs}
    {assignment : List Bool} (row : RuntimeOrdinaryInputs.Row initial assignment)
    (original : rootInputs = RuntimeBranchCondition.rootEntries (.root body)) :
    ∀ step ∈ steps, ConditionInput row.ordinals step := by
  intro step present
  have path := flow.conditions step present
  cases step with
  | conditional _ _ _ _ _ action _ _ =>
    exact Qleisli.RuntimeBranchInputDomain.original_row_member row action.condition.inputs (path.trans original)
  | _ => exact True.intro

/-- Instantiate the condition-row premise on the actual root body and its
checked row, without an additional assumption about the input table. -/
theorem original_body_condition_inputs {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime)
    {assignment : List Bool} (row : RuntimeOrdinaryInputs.Row body.checked.initial assignment) :
    ∀ step ∈ body.checked.result.steps, ConditionInput row.ordinals step := by
  obtain ⟨_,_,_,flow,_⟩ := RuntimeNamedChildRuns.original_body body
  exact flow_condition_inputs flow row rfl

def NeedsNonbranchAction {dependencies program block} : Step dependencies program block → Prop
  | .conditional .. => False
  | step => NeedsSourceAction step

/-- Supply the original branch action to the shared source evaluator. -/
private noncomputable def withBranchSteps {dependencies program block}
    (children : ScopedSourceSteps dependencies)
    (fallback : List (Step dependencies program block) → Step dependencies program block →
      SourceHistory → Option (List SourceHistory))
    (inputs : List Nat) (scope : List Edge) (prior : List (Step dependencies program block))
    (step : Step dependencies program block) (source : SourceHistory) : Option (List SourceHistory) :=
  match step with
  | .conditional (ordinary := ordinary) _ _ body actual _ action thenSteps elseSteps => do
    let choice ← sourceChoice (RuntimeBranchCondition.reference inputs ordinary.measurements source.measurements)
      action.condition.required
    let expected ← runArms body actual thenSteps elseSteps children scope prior.length source choice
    return expected.map (finishArm action choice)
  | _ => fallback prior step source

/-- The scoped sparse step law uses the smaller original child traversal
and the literal write exclusion on this occurrence of the branch. -/
theorem sourceStep_with_inherited_conditionals {artifact root mode fuel program block}
    (steps : List (Step root.dependencies program block)) (inputs : List Nat) (scope : List Edge)
    (inherited : Nat → Prop) (rows : ∀ step ∈ steps, ConditionInput inputs step)
    (children : ScopedSourceSteps root.dependencies)
    (childLaws : ∀ {program block} (atArm : List Edge) (nested : List (Step root.dependencies program block)),
      (∀ step ∈ nested, ConditionInput inputs step) →
      StepRefinement nested (CheckedStep (runBlockCore artifact root mode fuel))
        (children atArm) (fun _ => SemanticHistoryAgreesWithInherited (some inherited) inputs)
        (some (fun id => ¬ inherited id)))
    (fallback : List (Step root.dependencies program block) → Step root.dependencies program block →
      SourceHistory → Option (List SourceHistory))
    (remaining : StepRefinement steps
      (fun step => CheckedStep (runBlockCore artifact root mode (fuel+1)) step ∧
        (match step with | .conditional .. => False | _ => True))
      fallback (fun _ => SemanticHistoryAgreesWithInherited (some inherited) inputs)
      (some (fun id => ¬ inherited id))) :
    StepRefinement steps (CheckedStep (runBlockCore artifact root mode (fuel+1)))
      (withBranchSteps children fallback inputs scope)
      (fun _ => SemanticHistoryAgreesWithInherited (some inherited) inputs)
      (some (fun id => ¬ inherited id)) := by
  intro prior first later position checked ownerBefore ownerAfter ordinaryBefore ordinaryAfter owners ordinary
    chunk read writes source history outputs agrees executed
  have row := rows first (by rw [← position]; exact List.mem_append_right _ List.mem_cons_self)
  cases first
  case conditional path event body actual actualRead action thenSteps elseSteps =>
    rcases owners with ⟨rfl,rfl⟩
    rcases ordinary with ⟨rfl,rfl⟩
    obtain ⟨choice,expected,choiceRead,sourceRead,paired⟩ :=
      sparse_conditional_refines (fuel := fuel) action thenSteps elseSteps checked inputs row children
        scope prior.length (inherited := some inherited)
        ⟨childLaws _ _,childLaws _ _⟩ agrees read executed writes
    exact ⟨expected.map (finishArm action choice),
      by simp only [withBranchSteps,choiceRead,sourceRead,bind,Option.bind,pure],paired⟩
  all_goals
    exact remaining prior _ later position ⟨checked,trivial⟩ owners ordinary read writes agrees executed

/-- Supply the original branch action to the shared source evaluator. -/
noncomputable def withConditionals {dependencies program block}
    (children : ScopedSourceSteps dependencies)
    (fallback : List (Step dependencies program block) → Step dependencies program block →
      SourceHistory → Option (List SourceHistory))
    (inputs : List Nat) (scope : List Edge) (prior : List (Step dependencies program block))
    (step : Step dependencies program block) (source : SourceHistory) : Option (List SourceHistory) :=
  withBranchSteps (fun atArm => sourceStep (children atArm) atArm) fallback inputs scope prior step source

/-- Discharge the conditional case of the shared induction from the actual
child receipts and their smaller-fuel refinement laws. -/
theorem sourceStep_with_conditionals {artifact root mode fuel program block}
    (steps : List (Step root.dependencies program block)) (inputs : List Nat) (scope : List Edge)
    (rows : ∀ step ∈ steps, ConditionInput inputs step)
    (children : ScopedSourceSteps root.dependencies)
    (childLaws : ∀ {program block} (scope : List Edge) (steps : List (Step root.dependencies program block)),
      (∀ step ∈ steps, ConditionInput inputs step) →
      StepRefinement steps
        (fun step => CheckedStep (runBlockCore artifact root mode (fuel+1)) step ∧ NeedsSourceAction step)
        (children scope) (fun _ => HistoryAgrees inputs))
    (fallback : List (Step root.dependencies program block) → Step root.dependencies program block →
      SourceHistory → Option (List SourceHistory))
    (remaining : StepRefinement steps
      (fun step => CheckedStep (runBlockCore artifact root mode (fuel+1+1)) step ∧ NeedsNonbranchAction step)
      fallback (fun _ => HistoryAgrees inputs)) :
    StepRefinement steps (CheckedStep (runBlockCore artifact root mode (fuel+1+1)))
      (sourceStep (withConditionals children fallback inputs scope) scope) (fun _ => HistoryAgrees inputs) := by
  apply sourceStep_refines (fuel := fuel+1)
  intro prior first later position checked ownerBefore ownerAfter ordinaryBefore ordinaryAfter owners ordinary
    chunk read source history outputs agrees executed
  have row := rows first (by rw [← position]; exact List.mem_append_right _ List.mem_cons_self)
  cases first with
  | gap gap => exact False.elim checked.2
  | observation observation => exact False.elim checked.2
  | pure node =>
    exact remaining prior (.pure node) later position checked owners ordinary read agrees executed
  | named event frame body bodyRead boundary finalOrdinary nested =>
    exact remaining prior (.named event frame body bodyRead boundary finalOrdinary nested) later position
      checked owners ordinary read agrees executed
  | conditional path event body actual actualRead action thenSteps elseSteps =>
    rcases owners with ⟨rfl,rfl⟩
    rcases ordinary with ⟨rfl,rfl⟩
    obtain ⟨choice,expected,choiceRead,sourceRead,paired⟩ :=
      source_conditional_refines (artifact := artifact) (mode := mode) (fuel := fuel)
        action thenSteps elseSteps checked.1 inputs row children childLaws scope prior.length
        agrees read executed
    exact ⟨expected.map (finishArm action choice),
      by simp only [withConditionals,withBranchSteps,choiceRead,sourceRead,bind,Option.bind,pure],paired⟩

/-- Use the actual root's checked input row in the shared step theorem. -/
theorem original_body_source_steps {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime)
    {assignment : List Bool} (row : RuntimeOrdinaryInputs.Row body.checked.initial assignment)
    (scope : List Edge) (children : ScopedSourceSteps body.root.dependencies)
    (fallback : List (Step body.root.dependencies body.root.program body.checked.native.block) →
      Step body.root.dependencies body.root.program body.checked.native.block → SourceHistory → Option (List SourceHistory)) :
    let mode := RuntimePureBody.ExecutionMode.planned
      (RuntimeBodyOperations.preparation artifact prepared.source.catalogue)
      (RuntimeBodyOperations.stagedConsumption artifact prepared.source.catalogue body.root)
    (∀ {program block} (scope : List Edge) (steps : List (Step body.root.dependencies program block)),
      (∀ step ∈ steps, ConditionInput row.ordinals step) →
      StepRefinement steps
        (fun step => CheckedStep (runBlockCore artifact body.root mode 126) step ∧ NeedsSourceAction step)
        (children scope) (fun _ => HistoryAgrees row.ordinals)) →
    StepRefinement body.checked.result.steps
      (fun step => CheckedStep (runBlockCore artifact body.root mode 127) step ∧ NeedsNonbranchAction step)
      fallback (fun _ => HistoryAgrees row.ordinals) →
    StepRefinement body.checked.result.steps (CheckedStep (runBlockCore artifact body.root mode 127))
      (sourceStep (withConditionals children fallback row.ordinals scope) scope) (fun _ => HistoryAgrees row.ordinals) := by
  intro mode childLaws remaining
  exact sourceStep_with_conditionals (fuel := 125) body.checked.result.steps row.ordinals scope
    (original_body_condition_inputs body row) children childLaws fallback remaining

/-- Structural, ordinary, observation and conditional steps use the shared
sparse laws. Other original operations supply their own source action. -/
def NeedsSparseLeaf {dependencies program block} : Step dependencies program block → Prop
  | .conditional .. | .observation _ => False
  | step@(.named ..) => (inspect? step).isNone ∧ (RuntimeNamedThreeOccurrence.middle? step).isNone
  | step => NeedsSparseSourceAction step ∧ NeedsNonInline step

/-- Match the checked recursion depth. A child keeps its original path and
starts a new prefix in the scope selected by its parent condition. -/
noncomputable def sparseStepsAt {dependencies}
    (fallback : ScopedSourceSteps dependencies) (inputs : List Nat) : Nat → ScopedSourceSteps dependencies
  | 0 => fun scope => withSparseSteps (withSparseObservation (withSparseInline (fallback scope)) scope)
  | depth+1 => fun scope =>
    withSparseSteps (withSparseObservation (withSparseInline
      (withSparseSelection (withSparseNamed
        (withBranchSteps (sparseStepsAt fallback inputs depth) (fallback scope) inputs scope)))) scope)

private theorem ofList_stepList {dependencies program block} :
    (steps : Steps dependencies program block) → Steps.ofList (stepList steps) = steps
  | .nil => rfl
  | .cons first rest => congrArg (Steps.cons first) (ofList_stepList rest)

private theorem conditional_zero_impossible {artifact root mode program block step}
    (checked : @ConditionalRun artifact root mode (runBlockCore artifact root mode 0) program block step) :
    False := by
  cases checked with
  | @checked offset rootOwner rootName caller name path event source sameName actual actualRead
      leftRequest rightRequest leftPlan rightPlan before ordinary left right leftReceipts rightReceipts
      action beforeThen afterThen afterElse afterJoin thenRead elseRead joinRead =>
    change (Except.error QleisliKernel.Finite.Error.limit,beforeThen) = (Except.ok (left,leftReceipts),afterThen) at thenRead
    cases thenRead

private theorem named_zero_impossible {artifact root mode program block step}
    (checked : @ChildRun artifact root mode (runBlockCore artifact root mode 0) program block step) :
    False := by
  cases checked with
  | @named start count inputs caller before ordinary event scope body bodyRead
      rootOwner rootName path request plan initialBindings result receipts boundary
      beforeInput afterInput afterChild inputRead childRead =>
    change (Except.error QleisliKernel.Finite.Error.limit,afterInput) =
      (Except.ok (result,receipts),afterChild) at childRead
    cases childRead

/-- Compose actual nested conditionals, structural actions, observations,
ordinary SSA updates and named selections on one invariant. -/
theorem sparseStepsAt_refine {artifact root mode}
    (fallback : ScopedSourceSteps root.dependencies) (inputs : List Nat)
    (leaves : ∀ depth {program block} (scope : List Edge) (steps : List (Step root.dependencies program block)),
      StepRefinement steps
        (fun step => CheckedStep (runBlockCore artifact root mode depth) step ∧ NeedsSparseLeaf step)
        (fallback scope) (fun _ => SemanticHistoryAgrees inputs)) :
    ∀ depth {program block} (scope : List Edge) (steps : List (Step root.dependencies program block)) {count},
      RuntimeSelectionSteps.Witness (.steps 0 (Steps.ofList steps)) count →
      (∀ step ∈ steps, ConditionInput inputs step) →
      StepRefinement steps (CheckedStep (runBlockCore artifact root mode depth))
        (sparseStepsAt fallback inputs depth scope) (fun _ => SemanticHistoryAgrees inputs) := by
  intro depth
  induction depth with
  | zero =>
    intro program block scope steps count witness rows
    apply sourceStep_with_sparse_structure
    apply sourceStep_with_sparse_observation
    apply sourceStep_with_sparse_inline
    intro prior first later position checked ownerBefore ownerAfter ordinaryBefore ordinaryAfter
      owners ordinary chunk read source history outputs agrees executed
    cases first
    case conditional =>
      exact False.elim (conditional_zero_impossible checked.1.1.1)
    case named =>
      exact False.elim (named_zero_impossible checked.1.1.1)
    case observation =>
      exact False.elim checked.1.2
    all_goals
      exact leaves 0 scope steps prior _ later position ⟨checked.1.1.1,checked.1.1.2,checked.2⟩ owners ordinary read agrees executed
  | succ depth ih =>
    intro program block scope steps count witness rows
    apply sourceStep_with_sparse_structure
    apply sourceStep_with_sparse_observation
    apply sourceStep_with_sparse_inline
    intro prior first later position checked ownerBefore ownerAfter ordinaryBefore ordinaryAfter
      owners ordinary chunk read source history outputs agrees executed
    have row := rows first (by rw [← position]; exact List.mem_append_right _ List.mem_cons_self)
    cases first with
    | conditional path event body actual actualRead action thenSteps elseSteps =>
      obtain ⟨⟨_,⟨leftWitness⟩⟩,⟨_,⟨rightWitness⟩⟩⟩ :=
        RuntimeNamedThreeOccurrence.actual_conditional_steps witness prior later position.symm
      rcases owners with ⟨rfl,rfl⟩
      rcases ordinary with ⟨rfl,rfl⟩
      obtain ⟨choice,expected,choiceRead,sourceRead,paired⟩ :=
        sparse_conditional_refines (artifact := artifact) (mode := mode) (fuel := depth)
          action thenSteps elseSteps checked.1.1.1 inputs row (sparseStepsAt fallback inputs depth)
          scope prior.length (inherited := none)
          ⟨ih _ (stepList thenSteps) (by simpa only [ofList_stepList] using leftWitness),
            ih _ (stepList elseSteps) (by simpa only [ofList_stepList] using rightWitness)⟩ agrees read executed
      exact ⟨expected.map (finishArm action choice),
        by simp only [withSparseSelection,RuntimeNamedThreeOccurrence.middle?,withSparseNamed,
          withBranchSteps,choiceRead,sourceRead,bind,Option.bind,pure],paired⟩
    | named event frame body bodyRead boundary finalOrdinary children =>
      cases selected : RuntimeNamedThreeOccurrence.middle?
          (.named event frame body bodyRead boundary finalOrdinary children) with
      | some occurrence =>
        let held := RuntimeNamedThreeOccurrence.actual_steps_selection witness prior later occurrence position.symm
        have paired := sparse_named_selection_refines (fuel := depth) occurrence checked.1.1.1 held
          inputs owners ordinary read agrees executed
        exact ⟨sourceNamedSelection occurrence source,by simp only [withSparseSelection,selected],paired⟩
      | none =>
        cases inspected : inspect? (.named event frame body bodyRead boundary finalOrdinary children) with
        | none =>
          obtain ⟨expected,sourceRead,paired⟩ := leaves (depth+1) scope steps prior _ later position
            ⟨checked.1.1.1,by simp [NeedsSparseLeaf,selected,inspected]⟩
            owners ordinary read agrees executed
          exact ⟨expected,by simpa only [withSparseSelection,selected,withSparseNamed,inspected,
            withBranchSteps] using sourceRead,paired⟩
        | some held =>
          obtain ⟨expected,sourceRead,paired⟩ := sparse_named_primitive_refines (fuel := depth)
            held checked.1.1.1 inputs owners ordinary read agrees executed
          exact ⟨expected,by simpa only [withSparseSelection,selected,withSparseNamed,inspected]
            using sourceRead,paired⟩
    | observation _ => exact False.elim checked.1.2
    | gap _ =>
      exact leaves (depth+1) scope steps prior _ later position
        ⟨checked.1.1.1,checked.1.1.2,checked.2⟩ owners ordinary read agrees executed
    | pure _ =>
      exact leaves (depth+1) scope steps prior _ later position
        ⟨checked.1.1.1,checked.1.1.2,checked.2⟩ owners ordinary read agrees executed

/-- Use the decoded row of the actual checked root in the recursive sparse
step proof, including at each selected child branch. -/
theorem original_body_sparse_steps {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime)
    {assignment : List Bool} (row : RuntimeOrdinaryInputs.Row body.checked.initial assignment)
    (scope : List Edge) (fallback : ScopedSourceSteps body.root.dependencies) :
    let mode := RuntimePureBody.ExecutionMode.planned
      (RuntimeBodyOperations.preparation artifact prepared.source.catalogue)
      (RuntimeBodyOperations.stagedConsumption artifact prepared.source.catalogue body.root)
    (∀ depth {program block} (atStep : List Edge) (steps : List (Step body.root.dependencies program block)),
      StepRefinement steps
        (fun step => CheckedStep (runBlockCore artifact body.root mode depth) step ∧ NeedsSparseLeaf step)
        (fallback atStep) (fun _ => SemanticHistoryAgrees row.ordinals)) →
    StepRefinement body.checked.result.steps (CheckedStep (runBlockCore artifact body.root mode 127))
      (sparseStepsAt fallback row.ordinals 127 scope) (fun _ => SemanticHistoryAgrees row.ordinals) := by
  intro mode leaves
  exact sparseStepsAt_refine fallback row.ordinals leaves 127 scope body.checked.result.steps
    body.selections.witness (original_body_condition_inputs body row)

/-- Compare the complete original body and written return in the sparse
representation using its own decoded root row and actual checked children. -/
theorem original_body_sparse_refinement {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime)
    {assignment : List Bool} (row : RuntimeOrdinaryInputs.Row body.checked.initial assignment)
    (scope : List Edge) (sourceInitial : SourceHistory) (initial : History)
    (results : List History)
    (fallback : ScopedSourceSteps body.root.dependencies)
    (executed : let block := body.checked.native.block
      (do
        let (_,events) ← readOps block.fuel block.entry.quantum.reference block.operations
        run body.root.dependencies block.fuel events initial) = some results) :
    let block := body.checked.native.block
    let source := SourceRuntimeScope.Subject.whole prepared.source.body
    let mode := RuntimePureBody.ExecutionMode.planned
      (RuntimeBodyOperations.preparation artifact prepared.source.catalogue)
      (RuntimeBodyOperations.stagedConsumption artifact prepared.source.catalogue body.root)
    let history := RuntimeBodyOperations.initialHistory prepared body.checked.native runtime body.checked.inputs
    (∀ depth {program block} (atStep : List Edge) (steps : List (Step body.root.dependencies program block)),
      StepRefinement steps
        (fun step => CheckedStep (runBlockCore artifact body.root mode depth) step ∧ NeedsSparseLeaf step)
        (fallback atStep) (fun _ => SemanticHistoryAgrees row.ordinals)) →
    (∀ input : RuntimeOwnerMap.Checked source.initialRoles block.entry,
      RuntimeInterval.Computed (RuntimePureBody.reordered source.initialRoles block.entry history.bindings) input →
      SemanticHistoryAgrees row.ordinals block.entry {history with bindings := input.bindings} body.checked.initial.ssa sourceInitial initial) →
    ∃ ownerEnd : RuntimeStructuralAction.SourceState,
    ∃ last : RuntimeInterval.Checked block block.operations.length 0,
      RuntimeInterval.Computed (RuntimeInterval.check block block.operations.length 0) last ∧
      ∃ returned : RuntimeOwnerMap.Checked source.outputRoles last.after,
        RuntimeInterval.Computed (RuntimePureBody.reordered source.outputRoles last.after ownerEnd.bindings) returned ∧
        body.checked.result.history = {ownerEnd with bindings := returned.bindings} ∧
        ∃ expected, runSourceHistories (sparseStepsAt fallback row.ordinals 127 scope) [] body.checked.result.steps [sourceInitial] = some expected ∧
          List.Forall₂ (SemanticHistoryAgrees row.ordinals last.after body.checked.result.history body.checked.result.ordinary)
            (expected.map (returnHistory returned.bindings)) results := by
  intro block source mode history leaves starts
  exact original_body_encoded_refinement body SemanticHistoryEncoding row.ordinals
    (sparseArmEncodingLaws row.ordinals) sourceInitial initial results
    (sparseStepsAt fallback row.ordinals 127 scope) executed
    (original_body_sparse_steps body row scope fallback leaves) starts

#print axioms source_conditional_refines
#print axioms sparse_conditional_refines
#print axioms sourceStep_with_inherited_conditionals
#print axioms sparseStepsAt_refine
#print axioms original_body_sparse_steps
#print axioms original_body_sparse_refinement
#print axioms sourceStep_with_conditionals
#print axioms original_body_condition_inputs
#print axioms original_body_source_steps
end Qleisli.RuntimeLiteralBody
