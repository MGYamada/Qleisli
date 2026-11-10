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
    callerSourceResult componentJoint)
open Qleisli.RuntimeNamedChildRuns (CheckedStep ChildRun)
open RuntimePureBody (Step runBlockCore)
open RuntimeSelectionSteps (Edge)

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

/-- The original child uses its own source scope and exact stored step list.
Each logical component starts with the caller's outcomes and visible bits.
The shared recursive law is instantiated with this actual history's IDs. -/
def GeneralNamedRefines {artifact : Artifact} {root : Validity.Root}
    {mode : RuntimePureBody.ExecutionMode artifact root} (fuel : Nat)
    (inputs : List Nat) (inherited : Option (Nat → Prop))
    (children : ScopedSourceSteps root.dependencies) (sourceScope : List Edge)
    (ordinal : Nat) {program block} : Step root.dependencies program block → Prop
  | .named (start := start) (count := count) (before := before) (ordinary := ordinary)
      (childHistory := after) event scope body _ boundary finalOrdinary steps =>
    let selected := boundary.input.ordered
    let spectators := RuntimeSelectionPartition.complement before.bindings selected
    let subject := SourceTypes.SourceRuntimeScope.Subject.whole body
    let ports := (scope.selected.zip (selected.map (·.owner))).map Prod.fst
    let initial := namedSourceEntry subject.initialRoles ports body.checked.summary.nextOwner
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
      ∃ family : List (Nat → SourceHistory),
        (∀ index, ∃ expected,
          let operator := componentJoint before.bindings selected spectators source.operator index
          runSourceHistories next [] nested [{source with owners := initial, operator}] = some expected ∧
          family.map (fun result => result index) = expected.map (returnHistory after.bindings)) ∧
        List.Forall₂
          (SemanticHistoryAgreesWithInherited inherited inputs scope.interval.after boundary.after finalOrdinary)
          (family.map (callerSourceResult boundary spectators)) results
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
    refine ⟨family,?_,?_⟩
    · simpa only [bindings,inputShape,namedSourceEntry] using projection
    · simpa only [bindings] using returned

#print axioms general_named_refines
end Qleisli.RuntimeLiteralBody
