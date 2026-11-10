import Qleisli.RuntimeCallHistorySourceReturn
import Qleisli.RuntimeLiteralConditionalRefinement

/-! The actual original named call combines the same source prefix law on
its child components with the checked caller return. Nested writes respect
the inherited history of the original parent chunk.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeLiteralBody
open QleisliKernel QleisliKernel.Qirf
open QleisliKernel.Semantics.Observation (readOps)
open Qleisli.Semantics.ObservingAction (run)
open Qleisli.RuntimeCallHistory
  (NamedHistoryEntry NamedSourceTraversal actual_named_history_entry actual_named_source_traversal
    callerSourceResult callerSourceResult_congr componentJoint)
open Qleisli.RuntimeNamedChildRuns (CheckedStep ChildRun)
open RuntimePureBody (Step runBlockCore)
open RuntimeSelectionSteps (Edge)
open Qleisli.RuntimeSemanticForest (product)

private def namedScope {sources caller} (scope : List Edge) (ordinal : Nat)
    (event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller) : List Edge :=
  scope ++ [.named ordinal caller event.target.callerName event.call.calleeOffset
    event.target.resolution.moduleName event.target.resolution.declaration.name]

private def bindPorts (roles : List RuntimeOwnerMap.Owner)
    (ports : List RuntimeOwnerMap.Port) : RuntimeOwnerMap.Map :=
  (roles.zip ports).map fun (role,port) => ⟨role,port⟩

private theorem bindPorts_projections (bindings : RuntimeOwnerMap.Map) :
    bindPorts (bindings.map (·.owner)) (bindings.map (·.port)) = bindings := by
  induction bindings with
  | nil => rfl
  | cons first rest ih =>
    cases first
    simp only [bindPorts,List.map_cons,List.zip_cons_cons] at ih ⊢
    rw [ih]

private theorem binding_assignment {roles carriers assigned}
    (read : RuntimeInterval.Computed (RuntimeSourceBoundary.bindings roles carriers) assigned) :
    assigned = bindPorts roles (carriers.map (·.port)) := by
  have owners := RuntimeNamedPrimitiveInputs.bindings_roles read
  have ports := congrArg (List.map (fun carrier : Semantics.CarrierInterface.Owner => carrier.port)) (RuntimeBoundaryOwnerEvidence.bindings_carriers read)
  simp only [RuntimeForestCode.carrierOwners,List.map_map,Function.comp_def] at ports
  rw [← owners,← ports,bindPorts_projections]

/-- Initial source owners come from the written parameter roles and the
ports selected for those arguments, with no choice of a proof witness. -/
def namedSourceEntry (roles : List RuntimeOwnerMap.Owner) (ports : List RuntimeOwnerMap.Port)
    (nextOwner : Nat) : RuntimeStructuralAction.SourceState :=
  ⟨bindPorts roles ports,roles,nextOwner⟩

private noncomputable def callerFromColumns
    {dependencies program start count inputs sources caller block before child retired value}
    {event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller}
    {interval : @RuntimeInterval.Checked dependencies program block start count}
    (boundary : RuntimeNamedBoundary.Checked interval inputs event before child retired value)
    (spectators : RuntimeOwnerMap.Map) (columns : List (List SourceHistory)) : Option (List SourceHistory) := do
  let initial ← columns[0]?
  if columns.all (fun column => column.length == initial.length) then
    some (initial.mapIdx fun ordinal first =>
      callerSourceResult boundary spectators fun index =>
        ((columns[index]?).bind fun column => column[ordinal]?).getD first)
  else none

private theorem mapM_columns {α : Type} {read : Nat → Option α} {columns : Nat → α}
    (indices : List Nat) (computed : ∀ index ∈ indices, read index = some (columns index)) :
    indices.mapM read = some (indices.map columns) := by
  induction indices with
  | nil => rfl
  | cons first rest ih =>
    have head := computed first List.mem_cons_self
    have tail := ih (fun index member => computed index (List.mem_cons_of_mem _ member))
    simp [List.mapM_cons,head,tail]

private theorem caller_from_columns
    {dependencies program start count inputs sources caller block before child retired value}
    {event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller}
    {interval : @RuntimeInterval.Checked dependencies program block start count}
    (boundary : RuntimeNamedBoundary.Checked interval inputs event before child retired value)
    (spectators : RuntimeOwnerMap.Map) (family : List (Nat → SourceHistory))
    (read : Nat → Option (List SourceHistory))
    (computed : ∀ index < max 1 (product spectators).labels.length, read index = some (family.map (· index))) :
    let count := max 1 (product spectators).labels.length
    ((List.range count).mapM read).bind (callerFromColumns boundary spectators) =
      some (family.map (callerSourceResult boundary spectators)) := by
  let count := max 1 (product spectators).labels.length
  let columns := (List.range count).map (fun index => family.map (· index))
  change ((List.range count).mapM read).bind (callerFromColumns boundary spectators) = _
  rw [mapM_columns (List.range count) (fun index member => computed index (List.mem_range.mp member))]
  have columnAt (index : Nat) (bounded : index < count) : columns[index]? = some (family.map (· index)) := by
    simp only [columns,List.getElem?_map,List.getElem?_range bounded,Option.map_some]
  have zero := columnAt 0 (Nat.lt_of_lt_of_le (by decide : 0 < 1) (le_max_left _ _))
  have shape : columns.all (fun column => column.length == (family.map (· 0)).length) = true := by
    simp [columns]
  change callerFromColumns boundary spectators columns = some _
  simp only [callerFromColumns,zero,bind,Option.bind,shape,if_true,Option.some.injEq]
  apply List.ext_getElem
  · simp
  · intro ordinal left right
    have bounded : ordinal < family.length := by simpa using right
    simp only [List.getElem_mapIdx,List.getElem_map]
    apply callerSourceResult_congr
    · simp [zero,List.getElem?_eq_getElem bounded]
    · intro index supported
      have inColumns : index < count := Nat.lt_of_lt_of_le supported (le_max_right _ _)
      simp [columnAt index inColumns,List.getElem?_eq_getElem bounded]

/-- Evaluate the actual child prefix on each supported spectator column and
use column zero for the source history. Child returns retain their order. -/
noncomputable def evaluateGeneralNamed {dependencies program block}
    (children : ScopedSourceSteps dependencies) (sourceScope : List Edge) (ordinal : Nat)
    (step : Step dependencies program block) (source : SourceHistory) : Option (List SourceHistory) :=
  match step with
  | .named (before := before) (childHistory := after) event scope body _ boundary _ steps => do
    let selected := boundary.input.ordered
    let spectators := RuntimeSelectionPartition.complement before.bindings selected
    let subject := SourceTypes.SourceRuntimeScope.Subject.whole body
    let ports := (scope.selected.zip (selected.map (·.owner))).map Prod.fst
    let initial := namedSourceEntry subject.initialRoles ports body.checked.summary.nextOwner
    let next := children (namedScope sourceScope ordinal event)
    let nested := stepList steps
    let columns ← (List.range (max 1 (product spectators).labels.length)).mapM fun index => do
      let operator := componentJoint before.bindings selected spectators source.operator index
      (runSourceHistories next [] nested [{source with owners := initial, operator}]).map
        (List.map (returnHistory after.bindings))
    callerFromColumns boundary spectators columns
  | _ => none

/-- The original child uses its own source scope and exact stored step list.
Each logical component starts with the caller's outcomes and visible bits.
The shared recursive law is instantiated with this actual history's IDs. -/
def GeneralNamedRefines {artifact : Artifact} {root : Validity.Root}
    {mode : RuntimePureBody.ExecutionMode artifact root} (fuel : Nat)
    (inputs : List Nat) (inherited : Option (Nat → Prop))
    (children : ScopedSourceSteps root.dependencies) (sourceScope : List Edge)
    (ordinal : Nat) {program block} : Step root.dependencies program block → Prop
  | step@(.named (start := start) (count := count) (before := before) (ordinary := ordinary)
      event scope _ _ boundary finalOrdinary steps) =>
    let next := children (namedScope sourceScope ordinal event)
    let nested := stepList steps
    ∀ {source history events results},
      SemanticHistoryAgreesWithInherited inherited inputs scope.interval.before before ordinary source history →
      readOps block.fuel scope.interval.before.quantum.reference ((block.operations.drop start).take count) =
        some (scope.interval.after.quantum.reference,events) →
      run root.dependencies block.fuel events history = some results →
      TraceWriteBound (inherited.map (fun holds id => ¬ holds id)) events →
      StepRefinement nested (CheckedStep (runBlockCore artifact root mode fuel)) next
        (fun _ => SemanticHistoryAgreesWithInherited (some (fun id => id ∈ history.values.map Prod.fst)) inputs)
        (some (fun id => id ∉ history.values.map Prod.fst)) →
      ∃ expected,
        evaluateGeneralNamed children sourceScope ordinal step source = some expected ∧
        List.Forall₂
          (SemanticHistoryAgreesWithInherited inherited inputs scope.interval.after boundary.after finalOrdinary)
          expected results
  | _ => True

/-- The local named-call law uses the actual child receipt and the actual
literal caller event, preserving the ordered result family. -/
theorem general_named_refines {artifact root mode fuel program block step}
    (call : @ChildRun artifact root mode (runBlockCore artifact root mode (fuel+1)) program block step)
    (inputs : List Nat) (inherited : Option (Nat → Prop))
    (children : ScopedSourceSteps root.dependencies) (sourceScope : List Edge) (ordinal : Nat) :
    GeneralNamedRefines (artifact := artifact) (mode := mode) fuel inputs inherited children sourceScope ordinal step := by
  have entry : NamedHistoryEntry step := actual_named_history_entry call
  have traversal : NamedSourceTraversal (artifact := artifact) (mode := mode) fuel step :=
    actual_named_source_traversal call
  cases call with
  | @named start count args caller before ordinary event scope body bodyRead
      rootOwner rootName path request plan assigned result receipts boundary
      beforeInput afterInput afterChild inputRead childRead =>
    intro source history events results agrees read executed writes laws
    obtain ⟨input,assigned,assignedRead,ordered,_,prepared⟩ := entry
    obtain ⟨_,_,_,_,flow,returned⟩ := traversal input assigned assignedRead ordered
    obtain ⟨_,hidden,bits,values,_,checked,bindings,frame,represented⟩ := agrees
    let parent : Qleisli.RuntimeSemanticForest.Frame checked.bindings := bindings.symm ▸ frame
    obtain ⟨childFrame,childInput⟩ := prepared checked parent bindings
    obtain ⟨_,_,_,checkedRun⟩ := childInput source.operator history (cast_represents bindings.symm frame represented)
    obtain ⟨childEvents,actualChildren,ran⟩ := checkedRun read executed
    have avoids := by
      cases inherited with
      | none => exact ran.child_writes_avoid_input values.2
      | some holds => exact ran.child_writes_avoid_nested_input holds values.2 writes
    obtain ⟨_,family,_,weights,projection,paired⟩ :=
      ran.refine_weighted_child_sources input childFrame checked.bindings boundary.input.ordered _
        source history rfl flow returned inputs hidden bits values.1 _ laws avoids
    have returned := ran.caller_history_after_return boundary checked parent bindings inputs inherited
      result.ordinary values.2 weights paired
    have inputOrder := RuntimeNamedPrimitiveInputs.reordered_original
      (RuntimeNamedPrimitiveInputs.bindings_roles assignedRead) input ordered
    have inputShape := inputOrder.trans (binding_assignment assignedRead)
    simp only [List.map_map,Function.comp_def] at inputShape
    let spectators := RuntimeSelectionPartition.complement before.bindings boundary.input.ordered
    refine ⟨family.map (callerSourceResult boundary spectators),?_,by simpa only [bindings] using returned⟩
    change Option.bind ((List.range _).mapM _) (callerFromColumns boundary spectators) = _
    apply caller_from_columns
    intro index _
    obtain ⟨expected,evaluated,ordered⟩ := projection index
    simp only [bindings,inputShape] at evaluated
    simp only [namedSourceEntry,evaluated,Option.map_some,ordered]

#print axioms general_named_refines
end Qleisli.RuntimeLiteralBody
