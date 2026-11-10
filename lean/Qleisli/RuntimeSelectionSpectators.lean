import Qleisli.RuntimeOwnerFlowSeeds
import Qleisli.RuntimeOwnerFlowSteps
import Qleisli.RuntimeIntervalStates
import QleisliKernel.Qirf.RuntimeNamedFrameAxes

/-! Untouched source bindings from the same local and whole-caller flow.
The actual selected seed/return and complete caller seed/fold/resolve/order
receipts determine every spectator, including separate Unit owners. No lowering
shape, final wire/code equality, separability or acceptance rule is assumed.
This result alone supplies no selected action, code transport or Gram theorem.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeSelectionSpectators
open QleisliKernel QleisliKernel.Finite QleisliKernel.Semantics QleisliKernel.Qirf
open RuntimeOwnerMap (Binding Map)
open Qleisli.RuntimeOwnerTransitionAction
open Qleisli.RuntimeOwnerFlowSeeds

/-- A local pure interval and the complete original source transport preserve
every source binding outside the selected owners. The two receipts may use
separate reads of the same literal block and bounds. -/
theorem interval_spectators {dependencies program block arity start count inputs outputs roles beforeRoles}
    (frame : @RuntimePureInterval.Checked dependencies program block arity start count inputs outputs roles)
    (interval : RuntimeInterval.Checked block start count)
    (before : RuntimeOwnerMap.Checked beforeRoles interval.before)
    (transport : RuntimeOwnerTransition.Checked interval before.bindings)
    (chosen : Map) (owners : chosen.map (·.owner) = roles)
    (ports : chosen.map (·.port) = frame.selected)
    (partition : (chosen ++ RuntimeSelectionPartition.complement before.bindings chosen).Perm before.bindings) :
    ∀ binding ∈ transport.after.bindings, binding.owner ∉ roles → binding ∈ before.bindings := by
  obtain ⟨operations,initial,final,moved,parsed,seeded,flow,resolved,reordered⟩ := transport.flow
  have operationsEq : operations = frame.operations :=
    (List.map_inj_right (f := Semantics.Observation.Op.pure)
      (fun _ _ equal => Semantics.Observation.Op.pure.inj equal)).mp
      ((Sector.pureOps_bound _ _ parsed).symm.trans frame.literal)
  subst operations
  have localReturn := frame.ownerReturn
  unfold RawOwnerFlow.Returns RawOwnerFlow.run at localReturn
  obtain ⟨selectedInitial,selectedSeed,tail⟩ := Option.bind_eq_some_iff.mp localReturn
  obtain ⟨selectedFinal,selectedFlow,selectedReturn⟩ := Option.bind_eq_some_iff.mp tail
  change RawOwnerFlow.seed roles frame.selected = some selectedInitial at selectedSeed
  change frame.operations.foldlM RawOwnerFlow.step selectedInitial = some selectedFinal at selectedFlow
  change RawOwnerFlow.returned outputs selectedFinal = some roles at selectedReturn
  have selectedRead : RawOwnerFlow.seed (chosen.map (·.owner)) (chosen.map (·.port)) = some selectedInitial := by
    rw [owners,ports]
    exact selectedSeed
  have caller := seed_partition before.bindings initial seeded
  have selected := seed_partition chosen selectedInitial selectedRead
  have mapped := partition.symm.map seedCell
  rw [List.map_append] at mapped
  have context := caller.trans (mapped.trans (selected.symm.append_right _))
  have cellsUnique : ((before.bindings.map seedCell).map Prod.fst).Nodup := by
    simpa only [List.map_map,Function.comp_def,seedCell] using before.tokensDistinct
  have unique := (caller.map Prod.fst).nodup_iff.mpr cellsUnique
  have extended := Qleisli.RuntimeOwnerFlowSteps.fold_extension frame.operations context unique selectedFlow flow
  have movedSubset := (RuntimeSelectionPartition.order_values _ _ _ reordered).1
  have afterTokens : (interval.after.quantum.live.map (·.token)).Nodup :=
    (transport.after.complete.map (·.token)).nodup
      (by simpa only [List.map_map] using transport.after.tokensDistinct)
  have inputTokens : frame.selected.map (·.token) = inputs :=
    (RuntimeNamedFrameAxes.selectedPorts _ _ _ frame.atEntry).2
  intro binding member notChosen
  obtain ⟨work,left,ran⟩ := resolved
  obtain ⟨cell,present,origin,newLive⟩ := resolved_origins interval.after final moved work left ran
    binding (movedSubset member)
  rcases List.mem_append.mp (extended.1.mem_iff.mp present) with localCell | spectatorCell
  · obtain ⟨token,owner,bits,localOrigin,ownerMember⟩ := returned_cells outputs selectedReturn cell localCell
    have sameOwner : owner = binding.owner :=
      (RawOwnerFlow.Tree.owner.inj (congrArg Prod.snd (localOrigin.symm.trans origin))).1
    exact False.elim (notChosen (sameOwner ▸ ownerMember))
  · have originalCell := context.mem_iff.mpr (List.mem_append.mpr (Or.inr spectatorCell))
    obtain ⟨old,oldMember,seedOrigin⟩ := seed_origins before.bindings initial seeded cell originalCell
    have sameCell := seedOrigin.symm.trans origin
    have sameToken : old.port.token = binding.port.token := congrArg Prod.fst sameCell
    have sameOwner : old.owner = binding.owner :=
      (RawOwnerFlow.Tree.owner.inj (congrArg Prod.snd sameCell)).1
    have notInput : old.port.token ∉ inputs := by
      rw [← inputTokens,← ports,List.map_map]
      intro chosenToken
      obtain ⟨other,inside,token⟩ := List.mem_map.mp chosenToken
      have original : other ∈ before.bindings :=
        partition.mem_iff.mp (List.mem_append_left _ inside)
      have equal := map_unique (fun value : Binding => value.port.token) _ before.tokensDistinct
        other original old oldMember token
      apply notChosen
      rw [← sameOwner,← equal,← owners]
      exact List.mem_map_of_mem inside
    have notContains : inputs.contains old.port.token = false :=
      Bool.eq_false_iff.mpr (fun h => notInput (List.contains_iff_mem.mp h))
    have oldLive := before.complete.mem_iff.mp (List.mem_map.mpr ⟨old,oldMember,rfl⟩)
    rw [RuntimeIntervalStates.same_before interval frame.interval] at oldLive
    have oldSpectator : old.port ∈ PureInterval.spectators frame.interval.before inputs :=
      List.mem_filter.mpr ⟨oldLive,by simp only [notContains,Bool.not_false]⟩
    have oldAfter : old.port ∈ interval.after.quantum.live := by
      rw [RuntimeIntervalStates.same_after interval frame.interval]
      exact (List.mem_filter.mp (frame.spectators ▸ oldSpectator)).1
    have samePort := map_unique (fun port : Semantics.Raw.Port => port.token) _ afterTokens
      old.port oldAfter binding.port newLive sameToken
    have equal : old = binding := by
      cases old
      cases binding
      simp_all
    exact equal ▸ oldMember

/-- Both selected owners in the original sector use the common pure interval law. -/
theorem selection_spectators {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles) :
    ∀ binding ∈ source.transport.after.bindings,
      binding.owner ≠ source.selected.first.owner → binding.owner ≠ source.selected.second.owner →
        binding ∈ source.before.bindings := by
  have owners := (RuntimeSelectionPartition.order_values _ _ _ source.selected.ordered).2
  have ports : source.selected.toList.map (·.port) = frame.selected :=
    (RuntimeSelectionPartition.source_ports frame source).1.symm
  have partition := RuntimeSelectionPartition.source_input_partition frame source
  intro binding member notFirst notSecond
  apply interval_spectators frame frame.interval source.before source.transport source.selected.toList
    owners ports partition binding member
  rw [← owners]
  simp [notFirst, notSecond]

#print axioms interval_spectators
#print axioms selection_spectators

end Qleisli.RuntimeSelectionSpectators
