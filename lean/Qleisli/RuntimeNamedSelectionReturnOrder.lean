import Qleisli.RuntimeNamedSelectionInputEncoding
import Mathlib.Data.List.Perm.Subperm

/-! The original child return permutes its complete owner map. The named boundary
retains the actual mapped outputs and untouched caller owners in order.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeNamedSelectionReturnOrder
open QleisliKernel QleisliKernel.Qirf
open RuntimeOwnerMap (Binding Map)
open RuntimeForestCode

theorem final_checkpoint {dependencies program block start count}
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (last : RuntimeInterval.Checked block block.operations.length 0)
    (endIndex : start+count = block.operations.length) : interval.after = last.after := by
  let next : RuntimeInterval.Checked block (start+count) 0 :=
    { range := by rw [endIndex]; exact last.range
      before := last.before
      prefixRead := by rw [endIndex]; exact last.prefixRead
      after := last.after
      intervalRead := by simpa only [List.take_zero] using last.intervalRead }
  exact (RuntimeAdjacentSlices.adjacent interval next).trans
    (RuntimeAdjacentSlices.adjacent last last).symm

/-- The real return is a permutation of all source bindings in the selected
interval's after-map. Completeness is compared at the same full Raw state. -/
theorem returned_permutation {dependencies program block start count roles sourceBefore sourceAfter afterRoles}
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (checked : RuntimeOwnerMap.Checked afterRoles interval.after)
    (returned : RuntimeNamedSourceFlow.Returned block roles sourceBefore sourceAfter)
    (sameBindings : sourceBefore.bindings = checked.bindings)
    (endIndex : start+count = block.operations.length) :
    sourceAfter.bindings.Perm checked.bindings := by
  obtain ⟨native,_read,ordered,reordered,result⟩ := returned
  have sameEnd := final_checkpoint interval native endIndex
  have subset : ordered.bindings ⊆ checked.bindings := by
    rw [← sameBindings]
    exact RuntimeNamedPrimitiveOutputs.reordered_subset reordered
  have counts : ordered.bindings.length = checked.bindings.length := by
    have liveLength := congrArg (fun state : RuntimeOwnerMap.State => state.quantum.live.length) sameEnd
    simpa only [List.length_map] using
      ordered.complete.length_eq.trans (liveLength.symm.trans checked.complete.length_eq.symm)
  have unique : ordered.bindings.Nodup := List.Pairwise.of_map (fun b : Binding => b.port.token)
    (fun _ _ different equal => different (congrArg (fun b : Binding => b.port.token) equal)) ordered.tokensDistinct
  obtain ⟨all,perm,contained⟩ := List.subperm_iff.mp (unique.subperm subset)
  have same : ordered.bindings = all := contained.eq_of_length (counts.trans perm.length_eq.symm)
  rw [result]
  exact same ▸ perm

/-- The retained caller complement uses full owner identity, so it also
preserves spectator order and each separate zero-width owner. -/
theorem caller_after_order
    {dependencies program block callStart callCount inputs ordinary effect sources caller before child retired value}
    {event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller}
    (scope : @RuntimeCallScope.Checked dependencies program block callStart callCount inputs ordinary effect)
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before child retired value)
    {roles} (checked : RuntimeOwnerMap.Checked roles scope.interval.before)
    (sameBindings : checked.bindings = before.bindings) :
    let spectators := RuntimeSelectionPartition.complement checked.bindings boundary.input.ordered
    boundary.afterFrame.bindings = spectators++boundary.mapped ∧
      (boundary.mapped++spectators).Perm boundary.afterFrame.bindings := by
  intro spectators
  have facts := RuntimeSelectionPartition.order_values before.bindings event.inputOwners
    boundary.input.ordered boundary.input.orderRead
  have selected : boundary.input.ordered ⊆ checked.bindings := by rw [sameBindings]; exact facts.1
  have unique : (checked.bindings.map (fun b => b.owner.ordinal)).Nodup := by
    simpa only [← checked.ordered,List.map_map,Function.comp_def] using checked.ownersDistinct
  have members (b : Binding) (inCaller : b ∈ checked.bindings) :
      b.owner ∈ event.inputOwners ↔ b ∈ boundary.input.ordered := by
    rw [← facts.2]
    constructor
    · intro member
      obtain ⟨arg,found,owner⟩ := List.mem_map.mp member
      have same := RuntimeOwnerTransitionAction.map_unique (fun b : Binding => b.owner.ordinal)
        checked.bindings unique arg (selected found) b inCaller (congrArg (·.ordinal) owner)
      simpa only [same] using found
    · intro member
      exact List.mem_map_of_mem member
  have complement : before.bindings.filter (fun b => !event.inputOwners.contains b.owner) = spectators := by
    rw [← sameBindings]
    unfold spectators RuntimeSelectionPartition.complement
    apply List.filter_congr
    intro b member
    by_cases chosen : b ∈ boundary.input.ordered
    · simp [chosen,(members b member).mpr chosen]
    · have other : b.owner ∉ event.inputOwners := fun belongs => chosen ((members b member).mp belongs)
      simp [chosen,other]
  have after : boundary.afterFrame.bindings = spectators++boundary.mapped :=
    boundary.sameAfter.trans (boundary.afterBindings.trans (by rw [complement]))
  exact ⟨after,after ▸ List.perm_append_comm⟩

private def SelectionReturnOrder
    {dependencies program block callStart callCount inputs ordinary effect sources caller before child retired value}
    {event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller}
    (scope : @RuntimeCallScope.Checked dependencies program block callStart callCount inputs ordinary effect)
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before child retired value)
    {node : RuntimePureBody.Node dependencies scope.program scope.prepared.block}
    (stored : RuntimeSelectionWitness.Checked node) : Prop :=
  match stored with
  | .selection (codes := codes) _ _ =>
    child.bindings.Perm codes.owners.transport.after.bindings ∧
    carrierOwners boundary.mapped = carrierOwners child.bindings ∧
    ∀ {roles} (checked : RuntimeOwnerMap.Checked roles scope.interval.before),
      checked.bindings = before.bindings →
      let spectators := RuntimeSelectionPartition.complement checked.bindings boundary.input.ordered
      boundary.afterFrame.bindings = spectators++boundary.mapped ∧
        (boundary.mapped++spectators).Perm boundary.afterFrame.bindings

def OccurrenceReturnOrder {dependencies rootItem rootCount program block step}
    {witness : @RuntimeSelectionSteps.Witness dependencies rootItem rootCount}
    (occurrence : @RuntimeNamedThreeOccurrence.Middle dependencies program block step)
    (held : RuntimeNamedThreeOccurrence.RetainedData witness occurrence) : Prop :=
  match occurrence,held with
  | .named (scope := scope) (boundary := boundary) _ _,held => SelectionReturnOrder scope boundary held.literal

/-- Use the original final written return of the same real selection child.
No assumed permutation, caller output code or copied source map is used. -/
theorem actual_occurrence_return_order {artifact root execution fuel program block step rootItem rootCount}
    {witness : @RuntimeSelectionSteps.Witness root.dependencies rootItem rootCount}
    (occurrence : @RuntimeNamedThreeOccurrence.Middle root.dependencies program block step)
    (call : RuntimeNamedChildRuns.ChildRun artifact root execution
      (RuntimePureBody.runBlockCore artifact root execution (fuel+1)) step)
    (held : RuntimeNamedThreeOccurrence.RetainedData witness occurrence)
    (coverage : RuntimeNamedSelectionOn.Coverage occurrence held) : OccurrenceReturnOrder occurrence held := by
  have original := RuntimeNamedSelectionInputs.actual_occurrence_source occurrence call
  cases occurrence with
  | @named start count inputs sources caller before childHistory childRetired ordinary event scope body read boundary finalOrdinary node selected =>
    change SelectionReturnOrder scope boundary held.literal
    dsimp only [RuntimeNamedSelectionOn.Coverage] at coverage
    cases stored : held.literal with
    | @selection first size localInputs outputs selector target frame selectorBits targetBits retained restricted
        inputCode outputCode labels expected logical equations codes layouts literal nativeRead =>
      have bounds : first = 0 ∧ size = ((block.operations.drop start).take count).length := by
        simpa only [stored] using coverage
      have endIndex : first+size = scope.prepared.block.operations.length := by
        rw [bounds.1,bounds.2,Nat.zero_add]
        rfl
      obtain ⟨entry,_input,returned⟩ := original.2
      exact ⟨returned_permutation frame.interval codes.owners.transport.after returned rfl endIndex,
        RuntimeNamedCodeTransport.returned_carriers boundary,caller_after_order scope boundary⟩

#print axioms final_checkpoint
#print axioms returned_permutation
#print axioms caller_after_order
#print axioms actual_occurrence_return_order
end Qleisli.RuntimeNamedSelectionReturnOrder
