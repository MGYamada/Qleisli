import Qleisli.RuntimeCallHistorySourceState
import Qleisli.RuntimeLiteralStructuralRefinement

/-! Use the original checked child traversal on the same literal histories
that the parent execution produces on each physical spectator coordinate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeCallHistory
open QleisliKernel QleisliKernel.Qirf
open RuntimePureBody (Step runBlockCore)
open Qleisli.RuntimeNamedChildRuns (CheckedStep Flow RootInputs)
open Qleisli.RuntimeNamedSourceFlow (Returned)
open Qleisli.RuntimeLiteralBody
  (SourceHistory SemanticHistoryAgreesWithInherited StepRefinement refineFlowWithWrites
    runSourceHistories returnHistory sparse_return_refines cast_represents)
open Qleisli.RuntimeLiteralBranchChoice (measurementBits)
open Qleisli.RuntimeObservingWrites (WritesWithin)
open Qleisli.RuntimeObservingPrefix (Issued)
open Qleisli.RuntimeObservingValueRetention (Supports)
open Qleisli.RuntimeSemanticForest (Frame)
open Qleisli.RuntimeStructuralHistory (Represents)
open Qleisli.Semantics.ObservingAction (History)

/-- The callee's ordinary inputs use its actual visible table while its
source prefix retains the caller's measurement keys and hidden outcomes. -/
theorem source_input_on_slice {dependencies program block start count inputs ordinary effect roles}
    (scope : @RuntimeCallScope.Checked dependencies program block start count inputs ordinary effect)
    (checked : RuntimeOwnerMap.Checked roles scope.prepared.block.entry)
    (state : RuntimeStructuralAction.SourceState) (bindings : checked.bindings = state.bindings)
    (frame : Frame checked.bindings) (ordinals : List Nat)
    (source : SourceHistory) (actual : History) (localHistory : Nat → History)
    (joint : Nat → Nat → Nat → ℂ)
    (values : ∀ high, actual.values = (localHistory high).values)
    (outcomes : ∀ high, actual.hidden = (localHistory high).hidden)
    (hidden : actual.hidden = source.outcomes.map Prod.snd)
    (measured : measurementBits ordinary.measurements actual.values = some source.measurements)
    (ordinaryAgrees : RuntimeOrdinarySSA.Agreement
      (RuntimeOrdinaryBody.valuation ordinals ordinary.measurements actual.values) actual.values ordinary.table)
    (represented : ∀ high, Represents frame scope.prepared.block.entry (localHistory high) (joint high)) :
    ∀ high, SemanticHistoryAgreesWithInherited (some (fun id => id ∈ actual.values.map Prod.fst)) ordinals
      scope.prepared.block.entry state scope.visible.ssa
      {source with owners := state, operator := joint high} (localHistory high) := by
  intro high
  refine ⟨rfl,(outcomes high).symm.trans hidden,?_,⟨visible_child_input scope ordinals actual localHistory
    values ordinaryAgrees high,?_⟩,_,checked,bindings,bindings ▸ frame,?_⟩
  · rw [scope.visible.measurements,← values high]
    exact measured
  · intro id present
    exact .inl (by rwa [values high])
  · exact cast_represents bindings frame (represented high)

/-- Refine the actual child's source prefix and written return on each
literal result list paired by the successful caller run. The local laws
are tied to the same checked steps, including recursive child receipts. -/
theorem CheckedCallRun.refine_source_slices
    {artifact root mode fuel rootInputs program block start count inputs ordinary effect}
    {scope : @RuntimeCallScope.Checked root.dependencies program block start count inputs ordinary effect}
    {spectators actual localHistory parentEvents childEvents parents children}
    (checked : CheckedCallRun scope spectators actual localHistory parentEvents childEvents parents children)
    {startState finish after steps finalOrdinary roles}
    (flow : @Flow artifact root mode (runBlockCore artifact root mode fuel) rootInputs
      scope.program scope.prepared.block startState steps finish scope.visible.ssa finalOrdinary
      scope.prepared.block.operations.length)
    (returned : Returned scope.prepared.block roles finish after)
    (ordinals : List Nat) (sourceInitial : Nat → SourceHistory)
    (next : List (Step root.dependencies scope.program scope.prepared.block) →
      Step root.dependencies scope.program scope.prepared.block → SourceHistory → Option (List SourceHistory))
    (laws : StepRefinement steps (CheckedStep (runBlockCore artifact root mode fuel)) next
      (fun _ => SemanticHistoryAgreesWithInherited (some (fun id => id ∈ actual.values.map Prod.fst)) ordinals)
      (some (fun id => id ∉ actual.values.map Prod.fst)))
    (avoids : WritesWithin childEvents (fun id => id ∉ actual.values.map Prod.fst))
    (starts : ∀ high, SemanticHistoryAgreesWithInherited (some (fun id => id ∈ actual.values.map Prod.fst))
      ordinals scope.prepared.block.entry startState scope.visible.ssa (sourceInitial high) (localHistory high)) :
    ∃ owners : RuntimeOwnerMap.Checked roles scope.localAfter,
      RuntimeInterval.Computed (RuntimePureBody.reordered roles scope.localAfter finish.bindings) owners ∧
      after = {finish with bindings := owners.bindings} ∧
      ∀ high, ∃ expected,
        runSourceHistories next [] steps [sourceInitial high] = some expected ∧
        List.Forall₂
          (SemanticHistoryAgreesWithInherited (some (fun id => id ∈ actual.values.map Prod.fst))
            ordinals scope.localAfter after finalOrdinary)
          (expected.map (returnHistory owners.bindings)) (children.map (fun history => history high)) := by
  obtain ⟨owners,order,afterOrder⟩ := actual_child_return scope returned
  obtain ⟨native,_,_,_,_⟩ := returned
  refine ⟨owners,order,afterOrder,?_⟩
  intro high
  have beforeExit := actual_child_before_return scope native
  have literal := checked.childRead
  rw [← beforeExit] at literal
  obtain ⟨expected,evaluated,paired⟩ := refineFlowWithWrites flow native (sourceInitial high) (localHistory high)
    next (fun _ => SemanticHistoryAgreesWithInherited (some (fun id => id ∈ actual.values.map Prod.fst)) ordinals)
    (fun id => id ∉ actual.values.map Prod.fst) literal (checked.paired.childRun high) avoids laws (starts high)
  refine ⟨expected,evaluated,?_⟩
  rw [List.forall₂_map_left_iff]
  apply paired.imp
  intro source nativeHistory agrees
  rw [afterOrder]
  exact sparse_return_refines ordinals (inherited := some (fun id => id ∈ actual.values.map Prod.fst))
    owners order (beforeExit ▸ agrees)

private theorem maps_equal {first second : RuntimeOwnerMap.Map}
    (owners : first.map (·.owner) = second.map (·.owner))
    (ports : first.map (·.port) = second.map (·.port)) : first = second := by
  induction first generalizing second with
  | nil =>
    cases second with
    | nil => rfl
    | cons _ _ => cases owners
  | cons first rest ih =>
    cases second with
    | nil => cases owners
    | cons second tail =>
      simp only [List.map_cons,List.cons.injEq] at owners ports
      have same : first = second := by
        cases first
        cases second
        simp_all
      rw [same,ih owners.2 ports.2]

private theorem assigned_unique {roles carriers first second}
    (left : RuntimeInterval.Computed (RuntimeSourceBoundary.bindings roles carriers) first)
    (right : RuntimeInterval.Computed (RuntimeSourceBoundary.bindings roles carriers) second) : first = second := by
  apply maps_equal
  · exact (RuntimeNamedPrimitiveInputs.bindings_roles left).trans
      (RuntimeNamedPrimitiveInputs.bindings_roles right).symm
  · have aliases := (RuntimeBoundaryOwnerEvidence.bindings_carriers left).trans
      (RuntimeBoundaryOwnerEvidence.bindings_carriers right).symm
    simpa only [RuntimeForestCode.carrierOwners,List.map_map,Function.comp_def] using
      congrArg (List.map (fun carrier : Semantics.CarrierInterface.Owner => carrier.port)) aliases

private theorem stepList_ofList {dependencies program block} (steps : List (@Step dependencies program block)) :
    Qleisli.RuntimeLiteralBody.stepList (RuntimePureBody.Steps.ofList steps) = steps := by
  induction steps with
  | nil => rfl
  | cons first rest ih => exact congrArg (List.cons first) ih

/-- The original child receipt retains the complete traversal on the same
written argument bindings used by the source-derived slice input. -/
def NamedSourceTraversal {artifact : Artifact} {root : Validity.Root}
    {mode : RuntimePureBody.ExecutionMode artifact root} (fuel : Nat) {program block} :
    @Step root.dependencies program block → Prop
  | .named (childHistory := after) (sources := sources) event scope body _ boundary finalOrdinary steps =>
    let subject := SourceTypes.SourceRuntimeScope.Subject.whole body
    ∀ (input : RuntimeOwnerMap.Checked subject.initialRoles scope.prepared.block.entry)
      (assigned : RuntimeOwnerMap.Map),
      RuntimeInterval.Computed (RuntimeSourceBoundary.bindings subject.initialRoles
        ((scope.selected.zip (boundary.input.ordered.map (·.owner))).map fun (port,role) =>
          (⟨port,role.basis⟩ : Semantics.CarrierInterface.Owner))) assigned →
      RuntimeInterval.Computed (RuntimePureBody.reordered subject.initialRoles scope.prepared.block.entry assigned) input →
      ∃ rootOwner rootName,
      ∃ path : RuntimeOrdinaryBody.CallPath sources rootOwner rootName
        event.target.resolution.moduleName event.target.resolution.declaration.name,
      ∃ finish,
        Flow (runBlockCore artifact root mode fuel) (RuntimeBranchCondition.rootEntries path)
          ⟨input.bindings,subject.initialRoles,body.checked.summary.nextOwner⟩
          (Qleisli.RuntimeLiteralBody.stepList steps) finish scope.visible.ssa finalOrdinary
          scope.prepared.block.operations.length ∧
        Returned scope.prepared.block subject.outputRoles finish after
  | _ => True

theorem actual_named_source_traversal {artifact root mode fuel program block step}
    (call : @Qleisli.RuntimeNamedChildRuns.ChildRun artifact root mode
      (runBlockCore artifact root mode (fuel+1)) program block step) :
    NamedSourceTraversal (artifact := artifact) (mode := mode) fuel step := by
  cases call with
  | @named start count inputs caller before ordinary event scope body bodyRead
      rootOwner rootName path request plan originalAssigned result receipts boundary
      beforeInput afterInput afterChild inputRead childRead =>
    intro input assigned assignedRead ordered
    obtain ⟨initial,initialOrdered,finish,flow,returned⟩ :=
      Qleisli.RuntimeNamedChildRuns.core_flow artifact root mode fuel
        .localScope (.whole body) path scope.program request plan _ scope.visible.ssa
        scope.prepared.block (result,receipts) ⟨afterInput,afterChild,childRead⟩
    have sourceRead : RuntimeInterval.Computed _ originalAssigned := ⟨beforeInput,afterInput,inputRead⟩
    have roles := (RuntimeNamedFrameAxes.mixed_bound_axes scope boundary).1
    have sameAssigned : originalAssigned = assigned :=
      assigned_unique sourceRead (by simpa only [roles] using assignedRead)
    have initialMap := RuntimeNamedPrimitiveInputs.reordered_original
      (RuntimeNamedPrimitiveInputs.bindings_roles sourceRead) initial initialOrdered
    have inputMap := RuntimeNamedPrimitiveInputs.reordered_original
      (RuntimeNamedPrimitiveInputs.bindings_roles assignedRead) input ordered
    have sameInput : input.bindings = initial.bindings :=
      inputMap.trans (sameAssigned.symm.trans initialMap.symm)
    refine ⟨rootOwner,rootName,path,finish,?_,returned⟩
    simpa only [sameInput,stepList_ofList] using flow

#print axioms source_input_on_slice
#print axioms CheckedCallRun.refine_source_slices
#print axioms actual_named_source_traversal
end Qleisli.RuntimeCallHistory
