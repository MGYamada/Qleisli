import Qleisli.PureNamedScopeView
import Qleisli.RuntimeLiteralGeneralNamed
import Qleisli.RuntimeLiteralSelectionWitness

/-! Compose an original pure child by reusing the checked named-call history
law on the identical native subject and actual child steps.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeLiteralBody
open QleisliKernel QleisliKernel.Qirf
open RuntimePureBody (Node Nodes Step Steps runBlockCore)
open Qleisli.RuntimeNamedChildRuns (Flow RootInputs PureCallAt IsPureLiteral)
open Qleisli.RuntimeNamedSourceFlow (Returned)
open Qleisli.RuntimePureNamedScope (callView callView_subject PureBlock pureChildBlock)
open Qleisli.RuntimeCallHistory (named_history_entry_of_entry named_source_traversal_of_flow)

private abbrev Subject (dependencies : List Semantics.Finite.Dependency) :=
  (p : Semantics.Observation.Program) × RuntimeInterval.Prepared dependencies p

private abbrev LiteralSteps {dependencies} (subject : Subject dependencies) :=
  List (Step dependencies subject.1 subject.2.block)

private def pureScope {dependencies program block start count inputs} {effect : Semantics.Raw.Effect}
    (scope : @RuntimeCallInterval.Checked dependencies program block start count inputs)
    (empty : scope.interval.before.classical = []) (unitary : effect = .unitary) :
    RuntimeCallScope.Checked block start count inputs {} effect := by
  subst effect
  exact callView scope empty

private theorem pureScope_interval {dependencies program block start count inputs} {effect : Semantics.Raw.Effect}
    (scope : @RuntimeCallInterval.Checked dependencies program block start count inputs)
    (empty : scope.interval.before.classical = []) (unitary : effect = .unitary) :
    (pureScope scope empty unitary).interval = scope.interval := by
  subst effect
  rfl

private theorem pureScope_selected {dependencies program block start count inputs} {effect : Semantics.Raw.Effect}
    (scope : @RuntimeCallInterval.Checked dependencies program block start count inputs)
    (empty : scope.interval.before.classical = []) (unitary : effect = .unitary) :
    (pureScope scope empty unitary).selected = scope.selected := by
  subst effect
  rfl

private theorem pureScope_ssa {dependencies program block start count inputs} {effect : Semantics.Raw.Effect}
    (scope : @RuntimeCallInterval.Checked dependencies program block start count inputs)
    (empty : scope.interval.before.classical = []) (unitary : effect = .unitary) :
    (pureScope scope empty unitary).visible.ssa = {} := by
  subst effect
  rfl

private theorem pureScope_subject {dependencies program block start count inputs} {effect : Semantics.Raw.Effect}
    (scope : @RuntimeCallInterval.Checked dependencies program block start count inputs)
    (empty : scope.interval.before.classical = []) (unitary : effect = .unitary) :
    (⟨(pureScope scope empty unitary).program, (pureScope scope empty unitary).prepared⟩ :
      Subject dependencies) = ⟨scope.program,scope.prepared⟩ := by
  subst effect
  exact callView_subject scope empty

/-- Only the dependent index changes when the same checked pure interval is
presented to the shared call law. Child steps and native state are retained. -/
def originalPureStep {dependencies program block start count inputs sources caller before child retired}
    (event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller)
    (scope : @RuntimeCallInterval.Checked dependencies program block start count inputs)
    (body : SourceTypes.SourceRuntimeTrace.Body event.target.signature)
    (bodyRead : RuntimeInterval.Computed (SourceTypes.SourceRuntimeTrace.readNamedBody event) body)
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before child retired body.checked.summary.value)
    (empty : scope.interval.before.classical = []) (unitary : event.effect = .unitary)
    (steps : List (Step dependencies scope.program scope.prepared.block)) : Step dependencies program block :=
  .named event (pureScope scope empty unitary) body bodyRead
    ((pureScope_interval scope empty unitary).symm ▸ boundary) {}
    (Steps.ofList (cast (congrArg LiteralSteps (pureScope_subject scope empty unitary).symm) steps))

theorem originalPureStep_span {dependencies program block start count inputs sources caller before child retired}
    (event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller)
    (scope : @RuntimeCallInterval.Checked dependencies program block start count inputs)
    (body : SourceTypes.SourceRuntimeTrace.Body event.target.signature)
    (bodyRead : RuntimeInterval.Computed (SourceTypes.SourceRuntimeTrace.readNamedBody event) body)
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before child retired body.checked.summary.value)
    (empty : scope.interval.before.classical = []) (unitary : event.effect = .unitary)
    (steps : List (Step dependencies scope.program scope.prepared.block)) :
    stepSpan (originalPureStep event scope body bodyRead boundary empty unitary steps) =
      ⟨start,count,scope.interval⟩ := by
  change (⟨start,count,(pureScope scope empty unitary).interval⟩ : Span block) = _
  rw [pureScope_interval]

private theorem stepList_ofList {dependencies program block} (steps : List (Step dependencies program block)) :
    stepList (Steps.ofList steps) = steps := by
  induction steps with
  | nil => rfl
  | cons first rest ih => exact congrArg (List.cons first) ih

/-- The original pure node supplies the child step list by structural
conversion. The accepted child flow proves that it is the actual list. -/
noncomputable def evaluateOriginalPureNamed {dependencies program block}
    (children : ScopedSourceSteps dependencies) (sourceScope : List RuntimeSelectionSteps.Edge) (ordinal : Nat)
    (step : Step dependencies program block) (source : SourceHistory) : Option (List SourceHistory) :=
  match step with
  | .pure (.named event scope body bodyRead boundary actions) =>
    if empty : scope.interval.before.classical = [] then
      if unitary : event.effect = .unitary then
        evaluateGeneralNamed children sourceScope ordinal
          (originalPureStep event scope body bodyRead boundary empty unitary
            (stepList (Qleisli.RuntimeLiteralSelectionWitness.pureSteps actions))) source
      else none
    else none
  | _ => none

theorem evaluateOriginalPureNamed_from_actual {dependencies program block start count args sources caller before child retired}
    (event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller)
    (scope : @RuntimeCallInterval.Checked dependencies program block start count args)
    (body : SourceTypes.SourceRuntimeTrace.Body event.target.signature)
    (bodyRead : RuntimeInterval.Computed (SourceTypes.SourceRuntimeTrace.readNamedBody event) body)
    (boundary : RuntimeNamedBoundary.Checked scope.interval args event before child retired body.checked.summary.value)
    (empty : scope.interval.before.classical = []) (unitary : event.effect = .unitary)
    (actions : List (Node dependencies scope.program scope.prepared.block))
    (steps : List (Step dependencies scope.program scope.prepared.block))
    (actualSteps : steps = actions.map Step.pure)
    (children : ScopedSourceSteps dependencies) (sourceScope : List RuntimeSelectionSteps.Edge) (ordinal : Nat)
    (source : SourceHistory) :
    evaluateOriginalPureNamed children sourceScope ordinal
      (.pure (.named event scope body bodyRead boundary (Nodes.ofList actions))) source =
    evaluateGeneralNamed children sourceScope ordinal
      (originalPureStep event scope body bodyRead boundary empty unitary steps) source := by
  simp only [evaluateOriginalPureNamed,empty,unitary,dif_pos,
    Qleisli.RuntimeLiteralSelectionWitness.pureSteps_ofList,stepList_ofList,← actualSteps]

/-- The same child step list retains the original pure block shape and each
named callback's actual incoming empty ordinary state. -/
def PureChildFactsOfStep {artifact : Artifact} {root : Validity.Root}
    {mode : RuntimePureBody.ExecutionMode artifact root} (fuel : Nat) (origin : RootInputs)
    {program block} (step : Step root.dependencies program block) : Prop :=
  match step with
  | .named _ scope _ _ _ _ children =>
    PureBlock scope.prepared.block ∧
      (∀ first ∈ stepList children, IsPureLiteral first) ∧
      ∀ first ∈ stepList children, PureCallAt (runBlockCore artifact root mode fuel) origin {} first
  | _ => False

/-- A position-indexed law may use extra receipts proved for the same
actual step list. The original history induction already tracks the position. -/
theorem StepRefinement.of_scoped_certifies {dependencies program block} {Source : Type}
    {steps : List (@Step dependencies program block)} {weak strong next related allowed}
    (law : StepRefinement (SourceHistory := Source) steps strong next related allowed)
    (checked : ∀ step ∈ steps, weak step → strong step) :
    StepRefinement steps weak next related allowed := by
  intro earlier first later position weakProof
  apply law earlier first later position
  apply checked first
  · rw [← position]
    exact List.mem_append_right _ List.mem_cons_self
  · exact weakProof

private structure OriginalChildFlow {artifact : Artifact} {root : Validity.Root}
    {mode : RuntimePureBody.ExecutionMode artifact root} {fuel : Nat}
    (origin : RootInputs)
    {owner name} {signature : SourceTypes.SourceRuntimeContext.Signature artifact.sources owner name}
    (body : SourceTypes.SourceRuntimeTrace.Body signature)
    (assigned : RuntimeOwnerMap.Map) (after : RuntimeStructuralAction.SourceState)
    (subject : Subject root.dependencies) where
  entry : RuntimeOwnerMap.Checked (SourceTypes.SourceRuntimeScope.Subject.whole body).initialRoles subject.2.block.entry
  entryRead : RuntimeInterval.Computed
    (RuntimePureBody.reordered (SourceTypes.SourceRuntimeScope.Subject.whole body).initialRoles
      subject.2.block.entry assigned) entry
  steps : LiteralSteps subject
  last : RuntimeStructuralAction.SourceState
  flow : @Flow artifact root mode (runBlockCore artifact root mode fuel) origin subject.1 subject.2.block
    ⟨entry.bindings,(SourceTypes.SourceRuntimeScope.Subject.whole body).initialRoles,
      body.checked.summary.nextOwner⟩ steps last {} {} subject.2.block.operations.length
  returned : Returned subject.2.block (SourceTypes.SourceRuntimeScope.Subject.whole body).outputRoles last after
  shape : PureBlock subject.2.block
  allPure : ∀ first ∈ steps, IsPureLiteral first
  calls : ∀ first ∈ steps, PureCallAt (runBlockCore artifact root mode fuel) origin {} first

private theorem transported_steps {artifact root mode fuel origin owner name signature assigned after old new}
    {body : @SourceTypes.SourceRuntimeTrace.Body artifact.sources owner name signature}
    (same : old = new) (flow : @OriginalChildFlow artifact root mode fuel origin owner name signature body assigned after old) :
    (same ▸ flow : OriginalChildFlow origin body assigned after new).steps = cast (congrArg LiteralSteps same) flow.steps := by
  cases same
  rfl

/-- The original successful pure callback supplies the named-call law for
its exact literal steps, with every spectator and reference column. -/
theorem original_pure_step_refines {artifact : Artifact} {root : Validity.Root}
    {mode : RuntimePureBody.ExecutionMode artifact root} {fuel origin program block start count args caller before}
    (event : SourceTypes.SourceRuntimeContext.NamedEvent artifact.sources caller)
    (scope : @RuntimeCallInterval.Checked root.dependencies program block start count args)
    (body : SourceTypes.SourceRuntimeTrace.Body event.target.signature)
    (bodyRead : RuntimeInterval.Computed (SourceTypes.SourceRuntimeTrace.readNamedBody event) body)
    {rootOwner rootName} (parent : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName caller event.target.callerName)
    (request : RuntimeContextRequest.Context) (plan : mode.queries.BodyData (.whole body) request)
    {assigned : RuntimeOwnerMap.Map}
    {result : RuntimePureBody.BlockResult root.dependencies scope.program scope.prepared.block}
    {receipts : List mode.Receipt}
    (boundary : RuntimeNamedBoundary.Checked scope.interval args event before result.history result.retired body.checked.summary.value)
    (empty : scope.interval.before.classical = []) (unitary : event.effect = .unitary)
    (sourceRead : RuntimeInterval.Computed (RuntimeSourceBoundary.bindings
      (SourceTypes.SourceRuntimeScope.Subject.whole body).initialRoles
      ((scope.selected.zip event.inputOwners).map fun (port,role) =>
        (⟨port,role.basis⟩ : Semantics.CarrierInterface.Owner))) assigned)
    (childRead : RuntimeInterval.Computed
      (runBlockCore artifact root mode (fuel+1) .pureBody .localScope (.whole body)
        (.named event body bodyRead parent) scope.program request plan
        ⟨assigned,(SourceTypes.SourceRuntimeScope.Subject.whole body).initialRoles,body.checked.summary.nextOwner⟩
        {} scope.prepared.block) (result,receipts))
    (rootEntries : RuntimeBranchCondition.rootEntries (.named event body bodyRead parent) = origin)
    (inputs : List Nat) (inherited : Option (Nat → Prop))
    (children : ScopedSourceSteps root.dependencies) (sourceScope : List RuntimeSelectionSteps.Edge) (ordinal : Nat) :
    GeneralNamedRefinesOn (artifact := artifact) (mode := mode)
      (some (· = {})) fuel origin inputs inherited children sourceScope ordinal
      (originalPureStep event scope body bodyRead boundary empty unitary result.steps) ∧
    PureChildFactsOfStep (artifact := artifact) (mode := mode) fuel origin
      (originalPureStep event scope body bodyRead boundary empty unitary result.steps) := by
  obtain ⟨entry,entryRead,last,flow,returned,sameOrdinary⟩ :=
    Qleisli.RuntimeNamedChildRuns.step_flow_mode artifact root mode (runBlockCore artifact root mode fuel)
      .pureBody .localScope (Qleisli.RuntimeNamedChildRuns.core_pure_preserves_ordinary artifact root mode fuel)
      (.whole body) (.named event body bodyRead parent) scope.program request plan _ {} scope.prepared.block
      (result,receipts) childRead
  have ordinaryEq : result.ordinary = ({} : RuntimeOrdinaryBody.State) := (sameOrdinary.pure rfl).ordinary
  let original : @OriginalChildFlow artifact root mode fuel origin _ _ _ body assigned result.history
      ⟨scope.program,scope.prepared⟩ :=
    ⟨entry,entryRead,result.steps,last,by simpa only [rootEntries,Prod.fst,ordinaryEq] using flow,
      returned,pureChildBlock scope,(sameOrdinary.pure rfl).allPure,
      by simpa only [rootEntries,Prod.fst] using (sameOrdinary.pure rfl).calls⟩
  let view := pureScope scope empty unitary
  let sameSubject := pureScope_subject scope empty unitary
  let shifted : @OriginalChildFlow artifact root mode fuel origin _ _ _ body assigned result.history
      ⟨view.program,view.prepared⟩ := sameSubject.symm ▸ original
  have stepsEq : shifted.steps = cast (congrArg LiteralSteps sameSubject.symm) result.steps :=
    transported_steps sameSubject.symm original
  have inputRead : RuntimeInterval.Computed (RuntimeSourceBoundary.bindings
      (SourceTypes.SourceRuntimeScope.Subject.whole body).initialRoles
      ((view.selected.zip event.inputOwners).map fun (port,role) =>
        (⟨port,role.basis⟩ : Semantics.CarrierInterface.Owner))) assigned := by
    simpa only [view,pureScope_selected] using sourceRead
  let viewedBoundary : RuntimeNamedBoundary.Checked view.interval args event before result.history result.retired
      body.checked.summary.value := (pureScope_interval scope empty unitary).symm ▸ boundary
  have entryHistory := named_history_entry_of_entry
    (Qleisli.RuntimeSparseNamedBoundary.named_entry_of_bindings (bodyRead := bodyRead) (boundary := viewedBoundary)
      (finalOrdinary := {}) (steps := Steps.ofList shifted.steps) shifted.entry inputRead shifted.entryRead)
  have traversal := named_source_traversal_of_flow (bodyRead := bodyRead) (boundary := viewedBoundary)
    shifted.entry inputRead shifted.entryRead
    (by simpa only [view,pureScope_ssa] using shifted.flow) shifted.returned
  have sameStep : originalPureStep event scope body bodyRead boundary empty unitary result.steps =
      .named event view body bodyRead viewedBoundary {} (Steps.ofList shifted.steps) := by
    rw [stepsEq]
    rfl
  rw [sameStep]
  constructor
  · intro source history events results agrees read executed writes laws
    exact named_refines_of_traversal entryHistory traversal (domain := some (· = {}))
      (admitted := pureScope_ssa scope empty unitary) inputs inherited children sourceScope ordinal
      agrees read executed writes laws
  · refine ⟨shifted.shape,?_,?_⟩
    · simpa only [stepList_ofList] using shifted.allPure
    · simpa only [stepList_ofList] using shifted.calls

/-- The shared recursion cannot consume a pure named child at zero fuel. -/
theorem pure_named_zero_impossible {artifact root mode origin ordinary program block node}
    (child : @Qleisli.RuntimeNamedChildRuns.PureChildRunAt artifact root mode
      (runBlockCore artifact root mode 0) origin ordinary program block node) : False := by
  cases child with
  | named unitary inputRead read rootRead => cases read

#print axioms StepRefinement.of_scoped_certifies
#print axioms evaluateOriginalPureNamed_from_actual
#print axioms originalPureStep_span
#print axioms pure_named_zero_impossible
#print axioms original_pure_step_refines

private theorem boundary_after_transport {dependencies program block start count args sources caller before child retired value}
    {event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller}
    {original view : @RuntimeInterval.Checked dependencies program block start count}
    (same : view = original)
    (boundary : RuntimeNamedBoundary.Checked original args event before child retired value) :
    ((same.symm ▸ boundary) : RuntimeNamedBoundary.Checked view args event before child retired value).after =
      boundary.after := by
  cases same
  rfl

/-- The local successor rule applies the actual pure child on the original
caller step. The recursive law receives that child's actual pure block and
per-occurrence callback records. -/
theorem pure_named_successor {artifact : Artifact} {root : Validity.Root}
    {mode : RuntimePureBody.ExecutionMode artifact root} {fuel origin program block node}
    (call : @Qleisli.RuntimeNamedChildRuns.PureChildRunAt artifact root mode
      (runBlockCore artifact root mode (fuel+1)) (some origin) {} program block node)
    (parentShape : PureBlock block)
    (inputs : List Nat) (inherited : Option (Nat → Prop))
    (children : ScopedSourceSteps root.dependencies)
    (sourceScope : List RuntimeSelectionSteps.Edge) (ordinal : Nat)
    (descend : ∀ {childProgram childBlock} (scope : List RuntimeSelectionSteps.Edge)
      (steps : List (Step root.dependencies childProgram childBlock)), PureBlock childBlock →
      (∀ first ∈ steps, IsPureLiteral first) →
      ∀ childInherited,
      StepRefinement steps
        (fun first => Qleisli.RuntimeNamedChildRuns.CheckedStepAt (runBlockCore artifact root mode fuel) origin first ∧
          PureCallAt (runBlockCore artifact root mode fuel) origin {} first)
        (children scope)
        (fun _ => Qleisli.RuntimeCallHistory.SourceAgreementWithin (some (· = {})) childInherited inputs)
        (childInherited.map (fun holds id => ¬ holds id))) :
    ∀ {ownerBefore ownerAfter ordinaryBefore ordinaryAfter},
      Qleisli.RuntimeNamedSourceFlow.Aligned ownerBefore ownerAfter (.pure node) →
      Qleisli.RuntimeNamedChildRuns.OrdinaryAligned ordinaryBefore ordinaryAfter (.pure node) →
      ∀ {chunk}, QleisliKernel.Semantics.Observation.readOps block.fuel
        (nodeSpan node).checked.before.quantum.reference (nodeSpan node).operations =
          some ((nodeSpan node).checked.after.quantum.reference,chunk) →
      WithChunkWriteBound (inherited.map (fun holds id => ¬ holds id)) chunk
        (∀ {expected actual outputs},
          Qleisli.RuntimeCallHistory.SourceAgreementWithin (some (· = {})) inherited inputs
            (nodeSpan node).checked.before ownerBefore ordinaryBefore expected actual →
          Qleisli.Semantics.ObservingAction.run root.dependencies block.fuel chunk actual = some outputs →
          ∃ expectedOutputs,
            evaluateOriginalPureNamed children sourceScope ordinal (.pure node) expected = some expectedOutputs ∧
            List.Forall₂ (Qleisli.RuntimeCallHistory.SourceAgreementWithin (some (· = {})) inherited inputs
              (nodeSpan node).checked.after ownerAfter ordinaryAfter) expectedOutputs outputs) := by
  cases call with
  | @named start count args caller before event scope body bodyRead rootOwner rootName parent request plan
      assigned result receipts boundary beforeInput afterInput afterChild unitary inputRead childRead rootRead =>
    intro ownerBefore ownerAfter ordinaryBefore ordinaryAfter owners ordinary chunk read
    refine WithChunkWriteBound.of_trace ?_
    intro writes source actual outputs agrees executed
    obtain ⟨ownerIn,ownerOut⟩ := owners
    subst ownerBefore
    subst ownerAfter
    subst ordinaryAfter
    rcases agrees with ⟨rfl,agrees⟩
    have empty := parentShape.prefix scope.interval
    have rootEntry := rootRead origin rfl
    have actualRead : RuntimeInterval.Computed _ (result,receipts) := ⟨afterInput,afterChild,childRead⟩
    obtain ⟨_,_,_,_,_,facts⟩ := Qleisli.RuntimeNamedChildRuns.step_flow_mode artifact root mode
      (runBlockCore artifact root mode fuel) .pureBody .localScope
      (Qleisli.RuntimeNamedChildRuns.core_pure_preserves_ordinary artifact root mode fuel)
      (.whole body) (.named event body bodyRead parent) scope.program request plan _ {} scope.prepared.block
      (result,receipts) actualRead
    have literal : result.steps = result.actions.map Step.pure := (facts.pure rfl).literal
    obtain ⟨law,shape,allPure,calls⟩ := original_pure_step_refines (mode := mode) (fuel := fuel)
      event scope body bodyRead parent request plan boundary empty unitary ⟨beforeInput,afterInput,inputRead⟩
      actualRead rootEntry inputs inherited children sourceScope ordinal
    dsimp only [GeneralNamedRefinesOn,originalPureStep] at law
    let view := pureScope scope empty unitary
    have frameEq : view.interval = scope.interval := pureScope_interval scope empty unitary
    have viewAgrees : SemanticHistoryAgreesWithInherited inherited inputs view.interval.before before {} source actual := by
      rw [frameEq]
      exact agrees
    have viewRead : QleisliKernel.Semantics.Observation.readOps block.fuel view.interval.before.quantum.reference
        ((block.operations.drop start).take count) = some (view.interval.after.quantum.reference,chunk) := by
      rw [frameEq]
      exact read
    obtain ⟨expected,evaluated,related⟩ :=
      law viewAgrees viewRead executed writes (fun _ =>
        (descend _ _ shape allPure _).of_scoped_certifies
          (fun first present checked => ⟨checked,calls first present⟩))
    refine ⟨expected,?_,?_⟩
    · rw [evaluateOriginalPureNamed_from_actual event scope body bodyRead boundary empty unitary result.actions
        result.steps literal]
      exact evaluated
    · apply related.imp
      intro logical native h
      refine ⟨rfl,?_⟩
      have afterEq := boundary_after_transport (pureScope_interval scope empty unitary) boundary
      rw [afterEq, pureScope_interval] at h
      exact h

#print axioms pure_named_successor

end Qleisli.RuntimeLiteralBody
