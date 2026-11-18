import Qleisli.RuntimeCallHistorySourceReturn
import Qleisli.RuntimeRoutedSelectedReturn

/-! The actual original named call combines the same source prefix law on
its child components with the checked caller return. Nested writes respect
the inherited history of the original parent chunk.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeLiteralBody
open QleisliKernel QleisliKernel.Qirf
open QleisliKernel.Semantics.Observation (readOps)
open Qleisli.Semantics.ObservingAction (History run)
open Qleisli.RuntimeCallHistory
  (NamedHistoryEntry NamedSourceTraversal actual_named_history_entry actual_named_source_traversal
    callerSourceResult callerSourceResult_congr componentJoint InOrdinaryDomain SourceAgreementWithin
    prepared_child_history original_pure_call_run actual_pure_child_endpoints routedSourceResult routedSourceResult_congr
    actual_routed_source_traversal original_routed_named_input original_routed_named_run projected_child_endpoints)
open Qleisli.RuntimeNamedChildRuns (CheckedStepAt ChildRunAt ConditionFrom Flow RootInputs RoutedChildRunAt)
open Qleisli.RuntimeNamedSourceFlow (Returned)
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

private noncomputable def callerFromColumns (combine : (Nat → SourceHistory) → SourceHistory)
    (columns : List (List SourceHistory)) : Option (List SourceHistory) := do
  let initial ← columns[0]?
  if columns.all (fun column => column.length == initial.length) then
    some (initial.mapIdx fun ordinal first =>
      combine fun index => ((columns[index]?).bind fun column => column[ordinal]?).getD first)
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

private theorem caller_from_columns (dimension : Nat) (combine : (Nat → SourceHistory) → SourceHistory)
    (congruent : ∀ {first second}, first 0 = second 0 →
      (∀ index < dimension, first index = second index) → combine first = combine second)
    (family : List (Nat → SourceHistory)) (read : Nat → Option (List SourceHistory))
    (computed : ∀ index < max 1 dimension, read index = some (family.map (· index))) :
    let count := max 1 dimension
    ((List.range count).mapM read).bind (callerFromColumns combine) = some (family.map combine) := by
  let count := max 1 dimension
  let columns := (List.range count).map (fun index => family.map (· index))
  change ((List.range count).mapM read).bind (callerFromColumns combine) = _
  rw [mapM_columns (List.range count) (fun index member => computed index (List.mem_range.mp member))]
  have columnAt (index : Nat) (bounded : index < count) : columns[index]? = some (family.map (· index)) := by
    simp only [columns,List.getElem?_map,List.getElem?_range bounded,Option.map_some]
  have zero := columnAt 0 (Nat.lt_of_lt_of_le (by decide : 0 < 1) (le_max_left _ _))
  have shape : columns.all (fun column => column.length == (family.map (· 0)).length) = true := by
    simp [columns]
  change callerFromColumns combine columns = some _
  simp only [callerFromColumns,zero,bind,Option.bind,shape,if_true,Option.some.injEq]
  apply List.ext_getElem
  · simp
  · intro ordinal left right
    have bounded : ordinal < family.length := by simpa using right
    simp only [List.getElem_mapIdx,List.getElem_map]
    apply congruent
    · simp [zero,List.getElem?_eq_getElem bounded]
    · intro index supported
      have inColumns : index < count := Nat.lt_of_lt_of_le supported (le_max_right _ _)
      simp [columnAt index inColumns,List.getElem?_eq_getElem bounded]

/-- Evaluate the actual child prefix on each supported spectator column and
use column zero for the source history. Child returns retain their order. -/
noncomputable def evaluateNamedChild
    {dependencies program block start count args sources caller before after retired childProgram childBlock}
    {interval : @RuntimeInterval.Checked dependencies program block start count}
    (event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller)
    (body : SourceTypes.SourceRuntimeTrace.Body event.target.signature)
    (ports : List RuntimeOwnerMap.Port)
    (boundary : RuntimeNamedBoundary.Checked interval args event before after retired body.checked.summary.value)
    (nested : List (Step dependencies childProgram childBlock))
    (children : ScopedSourceSteps dependencies) (sourceScope : List Edge) (ordinal : Nat)
    (source : SourceHistory) : Option (List SourceHistory) := do
  let selected := boundary.input.ordered
  let spectators := RuntimeSelectionPartition.complement before.bindings selected
  let subject := SourceTypes.SourceRuntimeScope.Subject.whole body
  let inputPorts := (ports.zip (selected.map (·.owner))).map Prod.fst
  let initial := namedSourceEntry subject.initialRoles inputPorts body.checked.summary.nextOwner
  let next := children (namedScope sourceScope ordinal event)
  let columns ← (List.range (max 1 (product spectators).labels.length)).mapM fun index => do
    let operator := componentJoint before.bindings selected spectators source.operator index
    (runSourceHistories next [] nested [{source with owners := initial, operator}]).map
      (List.map (returnHistory after.bindings))
  callerFromColumns (callerSourceResult boundary spectators) columns

/-- Evaluate the written selected subprogram on each parked logical column.
The resulting source action restores the original owner grouping and uses
the exact returned phi order from the native routing receipt. -/
noncomputable def evaluateRoutedChild {dependencies program block sources caller}
    (access : @RuntimePureBody.RoutedAccess dependencies program block sources caller)
    (steps : RuntimePureBody.Steps dependencies access.frame.program access.frame.prepared.block)
    (children : ScopedSourceSteps dependencies) (sourceScope : List Edge) (ordinal : Nat)
    (source : SourceHistory) : Option (List SourceHistory) := do
  let entered := RuntimeExclusiveCoordinates.enterHistory access.opening source
  let selected := access.boundary.input.ordered
  let parked := access.frame.moves.map (·.2.original.thenBinding)
  let subject := SourceTypes.SourceRuntimeScope.Subject.whole access.source
  let inputPorts := (access.frame.selected.zip (selected.map (·.owner))).map Prod.fst
  let initial := namedSourceEntry subject.initialRoles inputPorts access.source.checked.summary.nextOwner
  let next := children (namedScope sourceScope ordinal access.event)
  let columns ← (List.range (max 1 (product parked).labels.length)).mapM fun index => do
    let operator := componentJoint access.opening.frame.bindings selected parked entered.operator index
    (runSourceHistories next [] (stepList steps) [{entered with owners := initial, operator}]).map
      (List.map (returnHistory access.childHistory.bindings))
  callerFromColumns (routedSourceResult access) columns

noncomputable def evaluateGeneralNamed {dependencies program block}
    (children : ScopedSourceSteps dependencies) (sourceScope : List Edge) (ordinal : Nat)
    (step : Step dependencies program block) (source : SourceHistory) : Option (List SourceHistory) :=
  match step with
  | .named event scope body _ boundary _ steps =>
    evaluateNamedChild event body scope.selected boundary (stepList steps) children sourceScope ordinal source
  | _ => none

/-- The original child uses its own source scope and exact stored step list.
Each logical component starts with the caller's outcomes and visible bits.
The shared recursive law is instantiated with this actual history's IDs. -/
def GeneralNamedRefinesOn {artifact : Artifact} {root : Validity.Root}
    {mode : RuntimePureBody.ExecutionMode artifact root} (domain : Option (RuntimeOrdinaryBody.State → Prop)) (fuel : Nat)
    (origin : RootInputs) (inputs : List Nat) (inherited : Option (Nat → Prop))
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
      ((∀ first ∈ nested, ConditionFrom origin first) →
        StepRefinement nested (CheckedStepAt (runBlockCore artifact root mode fuel) origin) next
          (fun _ => SourceAgreementWithin domain (some (fun id => id ∈ history.values.map Prod.fst)) inputs)
          (some (fun id => id ∉ history.values.map Prod.fst))) →
      ∃ expected,
        evaluateGeneralNamed children sourceScope ordinal step source = some expected ∧
        List.Forall₂
          (SemanticHistoryAgreesWithInherited inherited inputs scope.interval.after boundary.after finalOrdinary)
          expected results
  | _ => True

abbrev GeneralNamedRefines {artifact : Artifact} {root : Validity.Root}
    {mode : RuntimePureBody.ExecutionMode artifact root} :=
  @GeneralNamedRefinesOn artifact root mode none

/-- Compose the original argument history, actual child flow and caller
return. Both observing and pure call receipts can supply this same law. -/
theorem named_refines_of_traversal {artifact : Artifact} {root : Validity.Root}
    {mode : RuntimePureBody.ExecutionMode artifact root} {fuel origin program block start count args ordinary sources caller before child retired}
    {event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller}
    {scope : @RuntimeCallScope.Checked root.dependencies program block start count args ordinary event.effect}
    {body : SourceTypes.SourceRuntimeTrace.Body event.target.signature}
    {bodyRead : SourceTypes.SourceRuntimeTrace.NamedRead event body}
    {boundary : RuntimeNamedBoundary.Checked scope.interval args event before child retired body.checked.summary.value}
    {finalOrdinary} {steps : RuntimePureBody.Steps root.dependencies scope.program scope.prepared.block}
    (entry : NamedHistoryEntry (.named event scope body bodyRead boundary finalOrdinary steps))
    (traversal : NamedSourceTraversal (artifact := artifact) (mode := mode) fuel origin
      (.named event scope body bodyRead boundary finalOrdinary steps))
    (domain : Option (RuntimeOrdinaryBody.State → Prop) := none)
    (admitted : InOrdinaryDomain domain scope.visible.ssa := by trivial)
    (inputs : List Nat) (inherited : Option (Nat → Prop))
    (children : ScopedSourceSteps root.dependencies) (sourceScope : List Edge) (ordinal : Nat) :
    GeneralNamedRefinesOn (artifact := artifact) (mode := mode) domain fuel origin inputs inherited children sourceScope ordinal
      (.named event scope body bodyRead boundary finalOrdinary steps) := by
  intro source history events results agrees read executed writes laws
  obtain ⟨input,assigned,assignedRead,ordered,_,prepared⟩ := entry
  obtain ⟨_,flow,returned⟩ := traversal input assigned assignedRead ordered
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
    Qleisli.RuntimeCallHistory.CheckedCallRun.refine_weighted_child_sources input childFrame
      checked.bindings boundary.input.ordered _ source history ran rfl flow returned inputs hidden bits values.1 _
      (domain := domain) (admitted := admitted) (laws flow.conditions) avoids
  have returned := ran.caller_history_after_return boundary
    (Qleisli.RuntimeSparseNamedBoundary.CallExit.of_mixed scope boundary) checked parent bindings inputs inherited
    finalOrdinary values.2 weights paired
  have inputOrder := RuntimeNamedPrimitiveInputs.reordered_original
    (RuntimeNamedPrimitiveInputs.bindings_roles assignedRead) input ordered
  have inputShape := inputOrder.trans (binding_assignment assignedRead)
  simp only [List.map_map,Function.comp_def] at inputShape
  let spectators := RuntimeSelectionPartition.complement before.bindings boundary.input.ordered
  refine ⟨family.map (callerSourceResult boundary spectators),?_,by simpa only [bindings] using returned⟩
  change Option.bind ((List.range _).mapM _) (callerFromColumns (callerSourceResult boundary spectators)) = _
  apply caller_from_columns (product spectators).labels.length _ (callerSourceResult_congr boundary spectators)
  intro index _
  obtain ⟨expected,evaluated,ordered⟩ := projection index
  simp only [bindings,inputShape] at evaluated
  simp only [namedSourceEntry,evaluated,Option.map_some,ordered]

/-- A pure callback can start inside a mixed caller. Use its actual local
program and unchanged source SSA, retaining all inherited caller values. -/
theorem pure_named_refines_of_flow {artifact : Artifact} {root : Validity.Root}
    {mode : RuntimePureBody.ExecutionMode artifact root}
    {fuel origin program block start count args sources caller before child retired}
    {event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller}
    (scope : @RuntimeCallInterval.Checked root.dependencies program block start count args)
    (body : SourceTypes.SourceRuntimeTrace.Body event.target.signature)
    (boundary : RuntimeNamedBoundary.Checked scope.interval args event before child retired body.checked.summary.value)
    (input : RuntimeOwnerMap.Checked (SourceTypes.SourceRuntimeScope.Subject.whole body).initialRoles
      scope.prepared.block.entry)
    {assigned : RuntimeOwnerMap.Map}
    (assignedRead : RuntimeInterval.Computed (RuntimeSourceBoundary.bindings
      (SourceTypes.SourceRuntimeScope.Subject.whole body).initialRoles
      ((scope.selected.zip event.inputOwners).map fun (port,role) =>
        (⟨port,role.basis⟩ : Semantics.CarrierInterface.Owner))) assigned)
    (ordered : RuntimeInterval.Computed (RuntimePureBody.reordered
      (SourceTypes.SourceRuntimeScope.Subject.whole body).initialRoles scope.prepared.block.entry assigned) input)
    {steps finish ordinary}
    (flow : @Flow artifact root mode (runBlockCore artifact root mode fuel) origin scope.program scope.prepared.block
      ⟨input.bindings,(SourceTypes.SourceRuntimeScope.Subject.whole body).initialRoles,body.checked.summary.nextOwner⟩
      steps finish ordinary ordinary scope.prepared.block.operations.length)
    (returned : Returned scope.prepared.block (SourceTypes.SourceRuntimeScope.Subject.whole body).outputRoles finish child)
    (inputs : List Nat) (inherited : Option (Nat → Prop))
    (children : ScopedSourceSteps root.dependencies) (sourceScope : List Edge) (ordinal : Nat)
    {source : SourceHistory} {history : History} {events results}
    (agrees : SemanticHistoryAgreesWithInherited inherited inputs scope.interval.before before ordinary source history)
    (read : readOps block.fuel scope.interval.before.quantum.reference ((block.operations.drop start).take count) =
      some (scope.interval.after.quantum.reference,events))
    (executed : run root.dependencies block.fuel events history = some results)
    (writes : TraceWriteBound (inherited.map (fun holds id => ¬ holds id)) events)
    (laws : StepRefinement steps (CheckedStepAt (runBlockCore artifact root mode fuel) origin)
      (children (namedScope sourceScope ordinal event))
      (fun _ => SourceAgreementWithin (some (· = ordinary)) (some (fun id => id ∈ history.values.map Prod.fst)) inputs)
      (some (fun id => id ∉ history.values.map Prod.fst))) :
    ∃ expected, evaluateNamedChild event body scope.selected boundary steps children sourceScope ordinal source =
      some expected ∧ List.Forall₂
      (SemanticHistoryAgreesWithInherited inherited inputs scope.interval.after boundary.after ordinary) expected results := by
  have ports : scope.selected = boundary.input.ordered.map (·.port) :=
    Option.some.inj (scope.atEntry.symm.trans boundary.input.atEntry)
  have inputOrder := RuntimeNamedPrimitiveInputs.reordered_original
    (RuntimeNamedPrimitiveInputs.bindings_roles assignedRead) input ordered
  have sameCarriers : RuntimeForestCode.carrierOwners input.bindings =
      RuntimeForestCode.carrierOwners boundary.input.ordered := by
    rw [inputOrder,RuntimeBoundaryOwnerEvidence.bindings_carriers assignedRead,
      RuntimeNamedPrimitiveInputs.named_input_carriers_on boundary ports]
  obtain ⟨_,hidden,bits,values,_,checked,bindings,frame,represented⟩ := agrees
  let parent : Qleisli.RuntimeSemanticForest.Frame checked.bindings := bindings.symm ▸ frame
  obtain ⟨childFrame,childInput⟩ := prepared_child_history scope.prepared boundary ports checked bindings
    sameCarriers parent history source.operator (cast_represents bindings.symm frame represented)
  obtain ⟨childEvents,actualChildren,ran⟩ :=
    original_pure_call_run scope boundary checked bindings history _ childInput read executed
  have avoids := by
    cases inherited with
    | none => exact ran.child_writes_avoid_input values.2
    | some holds => exact ran.child_writes_avoid_nested_input holds values.2 writes
  obtain ⟨_,family,_,weights,projection,paired⟩ :=
    Qleisli.RuntimeCallHistory.CallRunOn.refine_weighted_child_sources input childFrame
      checked.bindings boundary.input.ordered _ source history ran rfl flow returned
      (actual_pure_child_endpoints scope) inputs hidden bits values.1 rfl id _
      (domain := some (· = ordinary)) (admitted := rfl) laws avoids
  have output := ran.caller_history_after_return boundary
    (Qleisli.RuntimeSparseNamedBoundary.CallExit.of_pure scope boundary) checked parent bindings inputs inherited
    ordinary values.2 weights paired
  have inputShape := inputOrder.trans (binding_assignment assignedRead)
  have roles := (RuntimeSelectionPartition.order_values before.bindings event.inputOwners
    boundary.input.ordered boundary.input.orderRead).2
  rw [← roles] at inputShape
  simp only [List.map_map,Function.comp_def] at inputShape
  let spectators := RuntimeSelectionPartition.complement before.bindings boundary.input.ordered
  refine ⟨family.map (callerSourceResult boundary spectators),?_,by simpa only [bindings] using output⟩
  change Option.bind ((List.range _).mapM _) (callerFromColumns (callerSourceResult boundary spectators)) = _
  apply caller_from_columns (product spectators).labels.length _ (callerSourceResult_congr boundary spectators)
  intro index _
  obtain ⟨expected,evaluated,ordered⟩ := projection index
  simp only [bindings,inputShape] at evaluated
  rw [ordered]
  simpa only [namedSourceEntry,Option.map_some] using
    congrArg (Option.map (List.map (returnHistory child.bindings))) evaluated

/-- The local named-call law uses the actual child receipt and the actual
literal caller event, preserving the ordered result family. -/
theorem general_named_refines {artifact root mode fuel origin program block step}
    (call : @ChildRunAt artifact root mode (runBlockCore artifact root mode (fuel+1)) (some origin) program block step)
    (inputs : List Nat) (inherited : Option (Nat → Prop))
    (children : ScopedSourceSteps root.dependencies) (sourceScope : List Edge) (ordinal : Nat) :
    GeneralNamedRefines (artifact := artifact) (mode := mode) fuel origin inputs inherited children sourceScope ordinal step := by
  have entry := actual_named_history_entry call.forget
  have traversal := actual_named_source_traversal call
  cases call
  intro source history events results agrees read executed writes laws
  exact named_refines_of_traversal entry traversal none True.intro inputs inherited children sourceScope ordinal
    agrees read executed writes laws

/-- A routed call refines the full original prefix, call and suffix.
Its weighted child laws use the same root row and the incoming history IDs. -/
def GeneralRoutedRefines {artifact : Artifact} {root : Validity.Root}
    {mode : RuntimePureBody.ExecutionMode artifact root} (fuel : Nat)
    (origin : RootInputs) (inputs : List Nat) (inherited : Option (Nat → Prop))
    (children : ScopedSourceSteps root.dependencies) (sourceScope : List Edge)
    (ordinal : Nat) {program block} : Step root.dependencies program block → Prop
  | .routedNamed access steps =>
    let original := access.closed.route.literal
    let next := children (namedScope sourceScope ordinal access.event)
    let nested := stepList steps
    ∀ {source history events results},
      SemanticHistoryAgreesWithInherited inherited inputs original.before access.before access.ordinary source history →
      readOps block.fuel original.before.quantum.reference
        ((block.operations.drop (access.offset - RuntimeExclusiveAction.routeCount access.access)).take
          (RuntimeExclusiveAction.routeCount access.access+1+RuntimeExclusiveAction.routeCount access.access)) =
        some (original.after.quantum.reference,events) →
      run root.dependencies block.fuel events history = some results →
      TraceWriteBound (inherited.map (fun holds id => ¬ holds id)) events →
      ((∀ first ∈ nested, ConditionFrom origin first) →
        StepRefinement nested (CheckedStepAt (runBlockCore artifact root mode fuel) origin) next
          (fun _ => SourceAgreementWithin none (some (fun id => id ∈ history.values.map Prod.fst)) inputs)
          (some (fun id => id ∉ history.values.map Prod.fst))) →
      ∃ expected,
        evaluateRoutedChild access steps children sourceScope ordinal source = some expected ∧
        List.Forall₂
          (SemanticHistoryAgreesWithInherited inherited inputs original.after access.closed.after access.closed.finalOrdinary.ssa)
          expected results
  | _ => True

/-- Consume the actual routed callback, the verified caller/child execution
pair and the existing arbitrary-reference weighted return theorem. -/
theorem general_routed_refines {artifact root mode fuel origin program block step}
    (call : @RoutedChildRunAt artifact root mode (runBlockCore artifact root mode (fuel+1)) (some origin) program block step)
    (inputs : List Nat) (inherited : Option (Nat → Prop))
    (children : ScopedSourceSteps root.dependencies) (sourceScope : List Edge) (ordinal : Nat) :
    GeneralRoutedRefines (artifact := artifact) (mode := mode) fuel origin inputs inherited children sourceScope ordinal step := by
  have traversal := actual_routed_source_traversal call
  cases call with
  | @checked caller access rootOwner rootName path controlled request plan initial result receipts
      beforeInput afterInput afterChild inputRead childRead history retired ordinary rootRead =>
    intro source native events outputs agrees read executed writes laws
    obtain ⟨input,assigned,assignedRead,ordered,_,flow,returned⟩ := traversal
    let entered := RuntimeExclusiveCoordinates.enterHistory access.opening source
    let parked := access.frame.moves.map (·.2.original.thenBinding)
    obtain ⟨atEntry,available,childFrame,paired⟩ := original_routed_named_input access agrees input assignedRead ordered
    let localHistory := RuntimeCallHistory.inputHistory childFrame access.frame.prepared.block.entry.quantum.frame
      access.opening.frame.bindings access.boundary.input.ordered parked entered.operator native
    obtain ⟨childEvents,childOutputs,ran⟩ := original_routed_named_run access native localHistory
      (by simpa only [List.map_map,Function.comp_def] using paired) read executed
    obtain ⟨_,hidden,bits,values,_,_,_,_,_⟩ := atEntry
    have avoids := by
      cases inherited with
      | none => exact ran.child_writes_avoid_input values.2
      | some holds => exact ran.child_writes_avoid_nested_input holds values.2 writes
    have visible : RuntimeOrdinarySSA.Agreement
        (RuntimeOrdinaryBody.valuation inputs access.ordinary.measurements native.values) native.values access.ordinary.table →
        RuntimeOrdinarySSA.Agreement
          (RuntimeOrdinaryBody.valuation inputs access.frame.visible.ssa.measurements native.values) native.values
          access.frame.visible.ssa.table := by
      intro original id expression member
      change (id,expression) ∈ access.frame.visible.table at member
      rw [access.frame.visible.original] at member
      exact original id expression (List.mem_filter.mp member).1
    obtain ⟨_,family,_,weights,projection,refines⟩ :=
      ran.refine_weighted_child_sources input childFrame access.opening.frame.bindings access.boundary.input.ordered
        parked entered native rfl flow returned (projected_child_endpoints access.frame access.projected)
        inputs hidden bits values.1 rfl visible (children (namedScope sourceScope ordinal access.event))
        (domain := none) (admitted := True.intro) (laws := laws flow.conditions) (avoids := avoids)
    have output := ran.caller_history_after_routed_return access available inputs inherited values.2 weights refines
    have inputOrder := RuntimeNamedPrimitiveInputs.reordered_original
      (RuntimeNamedPrimitiveInputs.bindings_roles assignedRead) input ordered
    have inputShape := inputOrder.trans (binding_assignment assignedRead)
    simp only [List.map_map,Function.comp_def] at inputShape
    refine ⟨family.map (routedSourceResult access),?_,output⟩
    change Option.bind ((List.range _).mapM _) (callerFromColumns (routedSourceResult access)) = _
    apply caller_from_columns (product parked).labels.length _ (routedSourceResult_congr access)
    intro index _
    obtain ⟨expected,evaluated,assembled⟩ := projection index
    simp only [inputShape] at evaluated
    rw [assembled]
    exact congrArg (Option.map (List.map (returnHistory access.childHistory.bindings))) evaluated

#print axioms general_named_refines
#print axioms general_routed_refines
#print axioms pure_named_refines_of_flow
end Qleisli.RuntimeLiteralBody
