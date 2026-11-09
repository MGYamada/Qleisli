import Qleisli.RuntimeLiteralBodyRefinement
import Qleisli.RuntimeLiteralNamedPrimitive
import Qleisli.RuntimeLiteralReturnOrder
import Qleisli.RuntimeLiteralBranchChoice
import Qleisli.RuntimeLiteralConditionalArms

/-! Compose the source-local steps with the shared body induction. Each
outcome carries its original source position, and the source operator is
evaluated independently in the retained logical coordinates.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeLiteralBody
open QleisliKernel QleisliKernel.Qirf
open QleisliKernel.Semantics.Observation (readOps)
open Qleisli.Semantics.ObservingAction (History run)
open Qleisli.RuntimeForestProduct (referenceAction)
open Qleisli.RuntimeOriginalBranchJoin (RepresentsOperator)
open Qleisli.RuntimeLiteralHistory
  (Agrees gap_history observation_source_history sourceErasure sourcePrimitive named_primitive_history
    sourceReturn return_order reordered_source)
open Qleisli.RuntimeNamedChildRuns (CheckedStep ChildRun OrdinaryAligned)
open Qleisli.RuntimeNamedSourceFlow (Aligned)
open Qleisli.RuntimeLiteralBranchChoice (measurementBits measurementBits_retains)
open Qleisli.RuntimeObservingValueRetention (run_retains_values)
open Qleisli.RuntimeOriginalObservationValues (observation_measurement_keys observation_measurement_ids)
open RuntimeForestCode (Frame)
open RuntimeNamedPrimitiveOccurrence (Occurrence inspect?)
open RuntimeOwnerMap (Map byOwner)
open RuntimePureBody (Step)
open RuntimeSelectionSteps (Edge)

/-- The logical action, outcome sites and visible measurement bits of the
evaluated source prefix. A discard contributes only a hidden outcome. -/
structure SourceHistory where
  owners : RuntimeStructuralAction.SourceState
  outcomes : List (List Edge × Nat)
  measurements : List Bool
  operator : Nat → Nat → ℂ
  branches : List (List Edge × Bool) := []

/-- Keep the complete source owner state, the original outcome order and the
ordinary SSA interpretation on the same encoded history. -/
def HistoryAgrees (inputs : List Nat) (state : Raw.Observation.State)
    (owners : RuntimeStructuralAction.SourceState) (ordinary : RuntimeOrdinaryBody.State)
    (source : SourceHistory) (history : History) : Prop :=
  source.owners = owners ∧ history.hidden = source.outcomes.map Prod.snd ∧
  measurementBits ordinary.measurements history.values = some source.measurements ∧
  Agrees inputs state ordinary history ∧
  ∃ roles, ∃ checked : RuntimeOwnerMap.Checked roles state,
    checked.bindings = owners.bindings ∧ ∃ frame : Frame checked, RepresentsOperator frame history source.operator

/-- Select the actual original branch using the measured bits computed by
the source prefix. The same literal event runs that child's history list. -/
theorem source_branch_choice {sources rootOwner rootName owner name dependencies program block offset
    path event actual owners ordinary}
    (checked : @RuntimeBranchCondition.Checked sources rootOwner rootName owner name dependencies program
      block offset path event actual ordinary)
    (inputs : List Nat) (member : inputs ∈ checked.inputs.rows) {expected history events}
    (agrees : HistoryAgrees inputs actual.interval.before owners ordinary expected history)
    (read : readOps block.fuel actual.interval.before.quantum.reference ((block.operations.drop offset).take 1) =
      some (actual.interval.after.quantum.reference,events)) :
    ∃ trace : Qleisli.RuntimeOriginalBranch.Trace actual, ∃ choice,
      Qleisli.RuntimeLiteralBranchChoice.sourceChoice
        (RuntimeBranchCondition.reference inputs ordinary.measurements expected.measurements) checked.required = some choice ∧
      run dependencies block.fuel events history = (do
        let selected ← run dependencies actual.childFuel (trace.armEvents choice) history
        selected.mapM (Qleisli.Semantics.ObservingAction.merge choice actual.classical)) := by
  obtain ⟨trace⟩ := Qleisli.RuntimeOriginalBranch.original_branch_events actual
  exact ⟨trace,Qleisli.RuntimeLiteralBranchChoice.branch_choice checked trace inputs member history
    agrees.2.2.1 agrees.2.2.2.1.1 read⟩

private def recordObservation (source : SourceHistory) (site : List Edge) (survivors : Map) (measured : Option Nat)
    (result : Nat × (Nat → Nat → ℂ)) : SourceHistory :=
  { source with
    owners := {source.owners with bindings := survivors}
    outcomes := source.outcomes ++ [(site,result.1)]
    measurements := source.measurements ++ (if measured.isSome then [result.1 == 1] else [])
    operator := result.2 }

private noncomputable def sourceNamedPrimitive {dependencies program block step}
    (held : @Occurrence dependencies program block step) (source : SourceHistory) :
    Option (List SourceHistory) :=
  match held with
  | .named (boundary := boundary) original bound => do
    let [returned] := boundary.mapped | none
    let operator ← sourcePrimitive original.event source.owners.bindings boundary.after.bindings
      bound.binding returned source.operator
    return [{source with owners := boundary.after, operator}]

/-- Evaluate the original gap, observation and supported named steps. The
remaining constructors use their own source action. -/
noncomputable def sourceStep {dependencies program block}
    (other : List (@Step dependencies program block) → Step dependencies program block →
      SourceHistory → Option (List SourceHistory))
    (scope : List Edge) (prior : List (@Step dependencies program block))
    (step : Step dependencies program block) (source : SourceHistory) : Option (List SourceHistory) :=
  match step with
  | .gap _ => some [source]
  | .observation (event := event) observation => do
    let spectators := RuntimeObservationAction.spectators event
    let survivors ← spectators.mapM (byOwner source.owners.bindings)
    let outcomes ← sourceErasure observation.checked.operand spectators source.owners.bindings source.operator
    return outcomes.map (recordObservation source (scope ++ [.atOrdinal prior.length]) survivors observation.checked.measured)
  | .pure _ | .conditional .. => other prior step source
  | .named .. =>
    match inspect? step with
    | some held => sourceNamedPrimitive held source
    | none => other prior step source

/-- These constructors supply their own local source action law. -/
def NeedsSourceAction {dependencies program block} : @Step dependencies program block → Prop
  | .gap _ | .observation _ => False
  | .pure _ | .conditional .. => True
  | step => (inspect? step).isNone

private def sameFrame {state firstRoles secondRoles}
    {first : RuntimeOwnerMap.Checked firstRoles state} {second : RuntimeOwnerMap.Checked secondRoles state}
    (same : first.bindings = second.bindings) (frame : Frame first) : Frame second :=
  ⟨same ▸ frame.owners,frame.code,by rw [← same]; exact frame.original⟩

private theorem sameFrame_represents {state firstRoles secondRoles}
    {first : RuntimeOwnerMap.Checked firstRoles state} {second : RuntimeOwnerMap.Checked secondRoles state}
    (same : first.bindings = second.bindings) (frame : Frame first) {history operator}
    (represented : RepresentsOperator frame history operator) :
    RepresentsOperator (sameFrame same frame) history operator := by
  intro col row bound
  simpa only [referenceAction, Frame.embedding, sameFrame, ← same] using represented col row bound

theorem HistoryAgrees.represents {inputs state owners ordinary source history roles}
    (agrees : HistoryAgrees inputs state owners ordinary source history)
    (checked : RuntimeOwnerMap.Checked roles state) (bindings : checked.bindings = owners.bindings) :
    ∃ frame : Frame checked, RepresentsOperator frame history source.operator := by
  obtain ⟨_,_,_,_,_,actual,actualBindings,frame,represented⟩ := agrees
  have same := actualBindings.trans bindings.symm
  exact ⟨sameFrame same frame,sameFrame_represents same frame represented⟩

private theorem sourceNamedPrimitive_refines {artifact root execution fuel program block step}
    (held : @Occurrence root.dependencies program block step)
    (call : ChildRun artifact root execution (RuntimePureBody.runBlockCore artifact root execution (fuel+1)) step)
    (inputs : List Nat) {ownerBefore ownerAfter ordinaryBefore ordinaryAfter}
    (owners : Aligned ownerBefore ownerAfter step) (ordinary : OrdinaryAligned ordinaryBefore ordinaryAfter step)
    {chunk source history outputs}
    (read : readOps block.fuel (stepSpan step).checked.before.quantum.reference (stepSpan step).operations =
      some ((stepSpan step).checked.after.quantum.reference,chunk))
    (agrees : HistoryAgrees inputs (stepSpan step).checked.before ownerBefore ordinaryBefore source history)
    (executed : run root.dependencies block.fuel chunk history = some outputs) :
    ∃ expected, sourceNamedPrimitive held source = some expected ∧
      List.Forall₂ (HistoryAgrees inputs (stepSpan step).checked.after ownerAfter ordinaryAfter) expected outputs := by
  have law := named_primitive_history held call
  cases held with
  | @named start count tokens sources caller before childHistory childRetired old first size inputToken outputToken role kind
      event scope body bodyRead boundary finalOrdinary primitive original bound =>
    rcases owners with ⟨rfl,rfl⟩
    rcases ordinary with ⟨rfl,rfl⟩
    obtain ⟨ownerState,hidden,bits,values,_,checked,bindings,input,represented⟩ := agrees
    obtain ⟨returned,mapped,output,operator,result,sourceRead,rfl,sameValues,sameHidden,measurements,resultAgrees,resultRepresents⟩ :=
      law checked input bindings inputs history source.operator values represented read executed
    have incoming := congrArg RuntimeStructuralAction.SourceState.bindings ownerState
    refine ⟨[{source with owners := boundary.after, operator}],?_,.cons
      ⟨rfl,sameHidden.trans hidden,?_,resultAgrees,_,boundary.afterFrame,boundary.sameAfter,output,resultRepresents⟩ .nil⟩
    · simp only [sourceNamedPrimitive,mapped,incoming,← bindings,← boundary.sameAfter,bind,Option.bind,pure,sourceRead]
    · rw [sameValues,measurements]
      exact bits

theorem sourceStep_refines {artifact root execution fuel program block}
    (steps : List (@Step root.dependencies program block))
    (inputs : List Nat) (scope : List Edge)
    (other : List (@Step root.dependencies program block) → Step root.dependencies program block →
      SourceHistory → Option (List SourceHistory))
    (remaining : StepRefinement steps
      (fun step => CheckedStep (RuntimePureBody.runBlockCore artifact root execution (fuel+1)) step ∧ NeedsSourceAction step)
      other (fun _ => HistoryAgrees inputs)) :
    StepRefinement steps (CheckedStep (RuntimePureBody.runBlockCore artifact root execution (fuel+1)))
      (sourceStep other scope) (fun _ => HistoryAgrees inputs) := by
  intro prior first later position certified ownerBefore ownerAfter ordinaryBefore ordinaryAfter
    owners ordinary chunk read source history outputs agrees executed
  cases first with
  | pure node =>
    exact remaining prior (.pure node) later position ⟨certified,trivial⟩ owners ordinary read agrees executed
  | named event frame body bodyRead boundary finalOrdinary children =>
    cases inspected : inspect? (.named event frame body bodyRead boundary finalOrdinary children) with
    | none =>
      obtain ⟨expected,source,related⟩ := remaining prior (.named event frame body bodyRead boundary finalOrdinary children)
        later position ⟨certified,by simp [NeedsSourceAction,inspected]⟩ owners ordinary read agrees executed
      exact ⟨expected,by simpa only [sourceStep,inspected] using source,related⟩
    | some held =>
      obtain ⟨expected,source,related⟩ :=
        sourceNamedPrimitive_refines held certified inputs owners ordinary read agrees executed
      exact ⟨expected,by simpa only [sourceStep,inspected] using source,related⟩
  | conditional path event sourceBody actual actualRead action thenSteps elseSteps =>
    exact remaining prior (.conditional path event sourceBody actual actualRead action thenSteps elseSteps)
      later position ⟨certified,trivial⟩ owners ordinary read agrees executed
  | gap gap =>
    rcases owners with ⟨rfl,rfl⟩
    rcases ordinary with ⟨rfl,rfl⟩
    obtain ⟨ownerState,hidden,bits,values,_,checked,bindings,input,represented⟩ := agrees
    have beforeBindings := RuntimeBoundaryOwnerEvidence.check_bindings gap.beforeFrame gap.beforeRead
    have afterBindings := RuntimeBoundaryOwnerEvidence.check_bindings gap.afterFrame gap.afterRead
    let inputFrame := sameFrame (bindings.trans beforeBindings.symm) input
    obtain ⟨output,paired⟩ := gap_history gap inputFrame inputs history source.operator values
      (sameFrame_represents _ _ represented) read executed
    cases paired with
    | @cons _ result _ _ matched tail =>
      cases tail
      have retains := run_retains_values _ _ _ _ executed result List.mem_cons_self
      exact ⟨[source],rfl,.cons
        ⟨ownerState,matched.1.trans hidden,measurementBits_retains _ retains bits,
          matched.2.1,_,gap.afterFrame,afterBindings,output,matched.2.2⟩ .nil⟩
  | observation observation =>
    rcases owners with ⟨rfl,rfl⟩
    rcases ordinary with ⟨rfl,rfl⟩
    obtain ⟨ownerState,hidden,bits,values,_,checked,bindings,input,represented⟩ := agrees
    obtain ⟨_,output,expected,erased,paired⟩ :=
      observation_source_history observation bindings input inputs history source.operator values represented read executed
    simp only [bindings] at erased
    have incoming := congrArg RuntimeStructuralAction.SourceState.bindings ownerState
    have survivors := Qleisli.RuntimeOriginalObservation.original_after_bindings observation.checked
    let record := recordObservation source (scope ++ [.atOrdinal prior.length])
      observation.checked.after.bindings observation.checked.measured
    refine ⟨expected.map record,?_,?_⟩
    · simp only [sourceStep, incoming, survivors, erased, bind, Option.bind, pure, record]
    · rw [List.forall₂_map_left_iff]
      apply paired.imp
      intro expectedResult result matched
      refine ⟨?_,?_,?_,matched.2.2.1,_,observation.checked.after,rfl,output,matched.2.2.2⟩
      · simp [record, recordObservation, RuntimeOrdinaryBody.Observation.after, ownerState]
      · simpa [record, recordObservation, hidden] using matched.2.1
      · have keys := observation_measurement_keys observation
        cases measured : observation.checked.measured with
        | none =>
          rw [measured] at keys
          simpa only [keys,matched.1,measured,record,recordObservation,Option.isSome,
            Bool.false_eq_true,if_false,List.append_nil] using bits
        | some id =>
          rw [measured] at keys
          obtain ⟨key,outputId,keys⟩ := keys
          have fresh := (observation_measurement_ids observation measured).1
          have unused := Qleisli.RuntimeOriginalClassicalJoin.lookup_unissued (fun member => fresh (values.2 member))
          have newBit := Semantics.OrdinaryValue.lookup_append_fresh (expectedResult.1 == 1) unused
          have oldBits := measurementBits_retains _
            (Semantics.OrdinaryValue.append_extends history.values [(id,expectedResult.1 == 1)]) bits
          rw [keys,matched.1,measured]
          unfold measurementBits at oldBits ⊢
          simp only [List.mapM_append,oldBits,List.mapM_cons,List.mapM_nil,outputId,newBit,bind,Option.bind,pure,
            record,recordObservation,measured,Option.isSome,if_true]

noncomputable def returnHistory (returned : Map) (source : SourceHistory) : SourceHistory :=
  { source with
    owners := {source.owners with bindings := returned}
    operator := sourceReturn source.owners.bindings returned source.operator }

private noncomputable def returnByRoles (roles : List RuntimeOwnerMap.Owner) (source : SourceHistory) :
    Option SourceHistory :=
  (roles.mapM (byOwner source.owners.bindings)).map (fun bindings => returnHistory bindings source)

/-- Run the original arm in source input order and return its results in
source output order. Both orders are computed from the original owner roles. -/
noncomputable def runSourceArm {dependencies program block}
    (next : List (@Step dependencies program block) → Step dependencies program block →
      SourceHistory → Option (List SourceHistory))
    (inputRoles outputRoles : List RuntimeOwnerMap.Owner) (steps : List (@Step dependencies program block))
    (source : SourceHistory) : Option (List SourceHistory) := do
  let input ← returnByRoles inputRoles source
  let results ← runSourceHistories next [] steps [input]
  results.mapM (returnByRoles outputRoles)

private theorem return_family (roles : List RuntimeOwnerMap.Owner) (returned : Map) :
    ∀ sources : List SourceHistory,
      (∀ source ∈ sources, roles.mapM (byOwner source.owners.bindings) = some returned) →
      sources.mapM (returnByRoles roles) = some (sources.map (returnHistory returned)) := by
  intro sources
  induction sources with
  | nil => intro _; rfl
  | cons first rest ih =>
    intro each
    have head := each first List.mem_cons_self
    have tail := ih (fun source member => each source (List.mem_cons_of_mem _ member))
    simp [List.mapM_cons,returnByRoles,head,tail]

private theorem sourceReturn_refines {state roles before ordinary}
    (inputs : List Nat) (returned : RuntimeOwnerMap.Checked roles state)
    (read : RuntimeInterval.Computed (RuntimePureBody.reordered roles state before.bindings) returned)
    {source history}
    (agrees : HistoryAgrees inputs state before ordinary source history) :
    HistoryAgrees inputs state {before with bindings := returned.bindings} ordinary
      (returnHistory returned.bindings source) history := by
  obtain ⟨owners,hidden,bits,values,_,checked,bindings,input,represented⟩ := agrees
  rw [← bindings] at read
  obtain ⟨output,encoded⟩ := return_order input returned read history source.operator represented
  refine ⟨by simp [returnHistory,owners],hidden,bits,values,_,returned,rfl,output,?_⟩
  simpa only [returnHistory,owners,← bindings] using encoded

private theorem history_at_arm_entry {parent child owners ordinary source history}
    (inputs : List Nat)
    (live : child.quantum.live = parent.quantum.live) (axes : child.quantum.frame = parent.quantum.frame)
    (issued : parent.classical ⊆ child.classical)
    (agrees : HistoryAgrees inputs parent owners ordinary source history) :
    HistoryAgrees inputs child owners ordinary source history := by
  obtain ⟨sourceOwners,hidden,bits,values,roles,checked,bindings,input,represented⟩ := agrees
  let entry : RuntimeOwnerMap.Checked roles child :=
    ⟨checked.bindings,checked.ordered,checked.ownersDistinct,checked.tokensDistinct,live.symm ▸ checked.complete⟩
  let frame : Frame entry := ⟨input.owners,input.code,input.original⟩
  refine ⟨sourceOwners,hidden,bits,⟨values.1,?_⟩,roles,entry,bindings,frame,?_⟩
  · intro id member
    exact Qleisli.RuntimeObservingPrefix.issued_mono issued (values.2 member)
  · intro col row bound
    have actual := represented col row (by simpa only [axes] using bound)
    simpa only [referenceAction,RuntimeForestCode.Frame.embedding,frame,entry,axes] using actual

/-- Use the same concrete source-step induction for an actual recursive arm.
The inherited history enters in original source order and returns in the
checked order consumed by the parent's phi merge. -/
theorem ArmFlow.source_refinement {artifact root mode fuel program block inputRoles outputRoles
    before after ordinary finalOrdinary steps rawExit output events parent}
    (arm : @ArmFlow artifact root mode (RuntimePureBody.runBlockCore artifact root mode (fuel+1))
      program block inputRoles outputRoles before after ordinary finalOrdinary steps parent rawExit output events)
    (inputs : List Nat) (scope : List Edge) (sourceInitial : SourceHistory) (initial : History) {results}
    (other : List (Step root.dependencies program block) → Step root.dependencies program block →
      SourceHistory → Option (List SourceHistory))
    (remaining : StepRefinement steps
      (fun step => CheckedStep (RuntimePureBody.runBlockCore artifact root mode (fuel+1)) step ∧ NeedsSourceAction step)
      other (fun _ => HistoryAgrees inputs))
    (agrees : HistoryAgrees inputs parent before ordinary sourceInitial initial)
    (executed : run root.dependencies block.fuel events initial = some results) :
    ∃ expected,
      runSourceArm (sourceStep other scope) inputRoles outputRoles steps sourceInitial = some expected ∧
      List.Forall₂ (HistoryAgrees inputs rawExit after finalOrdinary) expected results := by
  have entry := sourceReturn_refines inputs arm.input arm.inputRead
    (history_at_arm_entry inputs arm.live arm.axes arm.issued agrees)
  obtain ⟨expected,sourceRun,paired⟩ := (arm.trace.executes_singleton executed).ordered_refinement
    arm.flow.source arm.flow.ordinary (sourceStep other scope) (fun _ => HistoryAgrees inputs) [] _
    arm.flow.calls (sourceStep_refines steps inputs scope other remaining) (.cons entry .nil)
  refine ⟨expected.map (returnHistory output.bindings),?_,?_⟩
  · have initialOrder : inputRoles.mapM (byOwner sourceInitial.owners.bindings) = some arm.input.bindings := by
      rw [agrees.1]
      exact reordered_source arm.input arm.inputRead
    have finalOrder := reordered_source output arm.outputRead
    have ownerPairs : List.Forall₂ (fun source _ => source.owners = arm.beforeReturn ∧ True) expected results :=
      paired.imp (fun _ _ matched => ⟨matched.1,True.intro⟩)
    have sourceOwners := (List.forall₂_and_left expected results).mp ownerPairs |>.1
    have orders := return_family outputRoles output.bindings expected (fun source member =>
      sourceOwners source member ▸ finalOrder)
    simp only [runSourceArm,returnByRoles,initialOrder,Option.map,bind,Option.bind,sourceRun,orders]
  · rw [List.forall₂_map_left_iff,arm.returned]
    apply paired.imp
    intro source actual matched
    apply sourceReturn_refines inputs output arm.outputRead
    exact Eq.mp (congrArg (fun state => HistoryAgrees inputs state arm.beforeReturn finalOrdinary source actual)
      arm.sameExit) matched

/-- The same ordered execution proof covers the concrete source actions and
the literal final source return. Every remaining step must supply its source
law at the exact occurrence and in the same incoming history. -/
theorem original_body_source_refinement {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime)
    (inputs : List Nat) (scope : List Edge) (sourceInitial : SourceHistory) (initial : History)
    (results : List History)
    (other : List (Step body.root.dependencies body.root.program body.checked.native.block) →
      Step body.root.dependencies body.root.program body.checked.native.block →
      SourceHistory → Option (List SourceHistory))
    (executed : let block := body.checked.native.block
      (do
        let (_,events) ← readOps block.fuel block.entry.quantum.reference block.operations
        run body.root.dependencies block.fuel events initial) = some results) :
    let block := body.checked.native.block
    let source := QleisliKernel.SourceTypes.SourceRuntimeScope.Subject.whole prepared.source.body
    let mode := RuntimePureBody.ExecutionMode.planned
      (RuntimeBodyOperations.preparation artifact prepared.source.catalogue)
      (RuntimeBodyOperations.stagedConsumption artifact prepared.source.catalogue body.root)
    let history := RuntimeBodyOperations.initialHistory prepared body.checked.native runtime body.checked.inputs
    StepRefinement body.checked.result.steps
      (fun step => CheckedStep (RuntimePureBody.runBlockCore artifact body.root mode 127) step ∧ NeedsSourceAction step)
      other (fun _ => HistoryAgrees inputs) →
    (∀ input : RuntimeOwnerMap.Checked source.initialRoles block.entry,
      RuntimeInterval.Computed (RuntimePureBody.reordered source.initialRoles block.entry history.bindings) input →
      HistoryAgrees inputs block.entry {history with bindings := input.bindings} body.checked.initial.ssa sourceInitial initial) →
    ∃ ownerEnd : RuntimeStructuralAction.SourceState,
    ∃ last : RuntimeInterval.Checked block block.operations.length 0,
      RuntimeInterval.Computed (RuntimeInterval.check block block.operations.length 0) last ∧
      ∃ returned : RuntimeOwnerMap.Checked source.outputRoles last.after,
        RuntimeInterval.Computed (RuntimePureBody.reordered source.outputRoles last.after ownerEnd.bindings) returned ∧
        body.checked.result.history = {ownerEnd with bindings := returned.bindings} ∧
        ∃ expected, runSourceHistories (sourceStep other scope) [] body.checked.result.steps [sourceInitial] = some expected ∧
          List.Forall₂ (HistoryAgrees inputs last.after body.checked.result.history body.checked.result.ordinary)
            (expected.map (returnHistory returned.bindings)) results := by
  intro block source mode history remaining starts
  obtain ⟨ownerEnd,last,lastRead,⟨returned,returnRead,returnedHistory⟩,expected,sourceRead,paired⟩ :=
    original_body_ordered_refinement body sourceInitial initial results (sourceStep other scope)
      (fun _ => HistoryAgrees inputs) executed
      (sourceStep_refines (fuel := 126) body.checked.result.steps inputs scope other remaining) starts
  have finish : ∀ (output : RuntimeOwnerMap.Checked source.outputRoles last.after),
      RuntimeInterval.Computed (RuntimePureBody.reordered source.outputRoles last.after ownerEnd.bindings) output →
      ∀ {expected actual}, HistoryAgrees inputs last.before ownerEnd body.checked.result.ordinary expected actual →
      HistoryAgrees inputs last.after {ownerEnd with bindings := output.bindings} body.checked.result.ordinary
        (returnHistory output.bindings expected) actual := by
    rw [Qleisli.RuntimeOwnerTransitionAction.empty_state last]
    exact sourceReturn_refines inputs
  refine ⟨ownerEnd,last,lastRead,returned,returnRead,returnedHistory,expected,sourceRead,?_⟩
  rw [List.forall₂_map_left_iff,returnedHistory]
  exact paired.imp (fun _ _ matched => finish returned returnRead matched)

#print axioms sourceStep_refines
#print axioms source_branch_choice
#print axioms ArmFlow.source_refinement
#print axioms original_body_source_refinement
end Qleisli.RuntimeLiteralBody
