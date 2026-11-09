import Qleisli.RuntimeLiteralBodyRefinement
import Qleisli.RuntimeLiteralNamedPrimitive
import Qleisli.RuntimeLiteralReturnOrder

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
    sourceReturn return_order)
open Qleisli.RuntimeNamedChildRuns (CheckedStep ChildRun OrdinaryAligned)
open Qleisli.RuntimeNamedSourceFlow (Aligned)
open RuntimeForestCode (Frame)
open RuntimeNamedPrimitiveOccurrence (Occurrence inspect?)
open RuntimeOwnerMap (Map byOwner)
open RuntimePureBody (Step)
open RuntimeSelectionSteps (Edge)

/-- The logical action and outcome sites of the evaluated source prefix. -/
structure SourceHistory where
  owners : RuntimeStructuralAction.SourceState
  outcomes : List (List Edge × Nat)
  operator : Nat → Nat → ℂ

/-- Keep the complete source owner state, the original outcome order and the
ordinary SSA interpretation on the same encoded history. -/
def HistoryAgrees (inputs : List Nat) (state : Raw.Observation.State)
    (owners : RuntimeStructuralAction.SourceState) (ordinary : RuntimeOrdinaryBody.State)
    (source : SourceHistory) (history : History) : Prop :=
  source.owners = owners ∧ history.hidden = source.outcomes.map Prod.snd ∧
  Agrees inputs state ordinary history ∧
  ∃ roles, ∃ checked : RuntimeOwnerMap.Checked roles state,
    checked.bindings = owners.bindings ∧ ∃ frame : Frame checked, RepresentsOperator frame history source.operator

private def recordObservation (source : SourceHistory) (site : List Edge) (survivors : Map)
    (result : Nat × (Nat → Nat → ℂ)) : SourceHistory :=
  { owners := {source.owners with bindings := survivors}
    outcomes := source.outcomes ++ [(site,result.1)]
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
    return outcomes.map (recordObservation source (scope ++ [.atOrdinal prior.length]) survivors)
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
    obtain ⟨ownerState,hidden,values,_,checked,bindings,input,represented⟩ := agrees
    obtain ⟨returned,mapped,output,operator,result,sourceRead,rfl,sameValues,sameHidden,resultAgrees,resultRepresents⟩ :=
      law checked input bindings inputs history source.operator values represented read executed
    have incoming := congrArg RuntimeStructuralAction.SourceState.bindings ownerState
    refine ⟨[{source with owners := boundary.after, operator}],?_,
      .cons ⟨rfl,sameHidden.trans hidden,resultAgrees,_,boundary.afterFrame,boundary.sameAfter,output,resultRepresents⟩ .nil⟩
    simp only [sourceNamedPrimitive,mapped,incoming,← bindings,← boundary.sameAfter,bind,Option.bind,pure,sourceRead]

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
    obtain ⟨ownerState,hidden,values,_,checked,bindings,input,represented⟩ := agrees
    have beforeBindings := RuntimeBoundaryOwnerEvidence.check_bindings gap.beforeFrame gap.beforeRead
    have afterBindings := RuntimeBoundaryOwnerEvidence.check_bindings gap.afterFrame gap.afterRead
    let inputFrame := sameFrame (bindings.trans beforeBindings.symm) input
    obtain ⟨output,paired⟩ := gap_history gap inputFrame inputs history source.operator values
      (sameFrame_represents _ _ represented) read executed
    cases paired with
    | cons matched tail =>
      cases tail
      exact ⟨[source],rfl,.cons
        ⟨ownerState,matched.1.trans hidden,matched.2.1,_,gap.afterFrame,afterBindings,output,matched.2.2⟩ .nil⟩
  | observation observation =>
    rcases owners with ⟨rfl,rfl⟩
    rcases ordinary with ⟨rfl,rfl⟩
    obtain ⟨ownerState,hidden,values,_,checked,bindings,input,represented⟩ := agrees
    obtain ⟨_,output,expected,erased,paired⟩ :=
      observation_source_history observation bindings input inputs history source.operator values represented read executed
    simp only [bindings] at erased
    have incoming := congrArg RuntimeStructuralAction.SourceState.bindings ownerState
    have survivors := Qleisli.RuntimeOriginalObservation.original_after_bindings observation.checked
    let record := recordObservation source (scope ++ [.atOrdinal prior.length]) observation.checked.after.bindings
    refine ⟨expected.map record,?_,?_⟩
    · simp only [sourceStep, incoming, survivors, erased, bind, Option.bind, pure, record]
    · rw [List.forall₂_map_left_iff]
      apply paired.imp
      intro expectedResult result matched
      refine ⟨?_,?_,matched.2.2.1,_,observation.checked.after,rfl,output,matched.2.2.2⟩
      · simp [record, recordObservation, RuntimeOrdinaryBody.Observation.after, ownerState]
      · simpa [record, recordObservation, hidden] using matched.2.1

noncomputable def returnHistory (returned : Map) (source : SourceHistory) : SourceHistory :=
  { source with
    owners := {source.owners with bindings := returned}
    operator := sourceReturn source.owners.bindings returned source.operator }

private theorem sourceReturn_refines {state roles before ordinary}
    (inputs : List Nat) (returned : RuntimeOwnerMap.Checked roles state)
    (read : RuntimeInterval.Computed (RuntimePureBody.reordered roles state before.bindings) returned)
    {source history}
    (agrees : HistoryAgrees inputs state before ordinary source history) :
    HistoryAgrees inputs state {before with bindings := returned.bindings} ordinary
      (returnHistory returned.bindings source) history := by
  obtain ⟨owners,hidden,values,_,checked,bindings,input,represented⟩ := agrees
  rw [← bindings] at read
  obtain ⟨output,encoded⟩ := return_order input returned read history source.operator represented
  refine ⟨by simp [returnHistory,owners],hidden,values,_,returned,rfl,output,?_⟩
  simpa only [returnHistory,owners,← bindings] using encoded

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
#print axioms original_body_source_refinement
end Qleisli.RuntimeLiteralBody
