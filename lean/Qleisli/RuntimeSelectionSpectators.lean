import Qleisli.RuntimeOwnerFlowSeeds
import Qleisli.RuntimeOwnerFlowSteps

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

/-- Every surviving owner outside the authentic selected source pair is the
identical original caller binding. The local successful owner return and the
same global operation flow exclude reassignment to an equal-width spectator. -/
theorem selection_spectators {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles) :
    ∀ binding ∈ source.transport.after.bindings,
      binding.owner ≠ source.selected.first.owner → binding.owner ≠ source.selected.second.owner →
        binding ∈ source.before.bindings := by
  obtain ⟨operations,initial,final,moved,parsed,seeded,flow,resolved,reordered⟩ := source.transport.flow
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
  have selected := RuntimeSelectionPartition.order_values _ _ _ source.selected.ordered
  have ownersEq : source.selected.toList.map (·.owner) = roles := selected.2
  have portsEq : source.selected.toList.map (·.port) = frame.selected := by
    change [source.selected.first.port,source.selected.second.port] = frame.selected
    exact (RuntimeSelectionPartition.source_ports frame source).1.symm
  have arguments : RawOwnerFlow.seed (source.selected.toList.map (·.owner))
      (source.selected.toList.map (·.port)) = RawOwnerFlow.seed roles frame.selected := by
    rw [ownersEq,portsEq]
  have selectedRead := arguments.trans selectedSeed
  have context := selection_seed_context frame source initial selectedInitial seeded selectedRead
  have extended := Qleisli.RuntimeOwnerFlowSteps.fold_extension frame.operations context.1 context.2 selectedFlow flow
  have movedSubset := (RuntimeSelectionPartition.order_values _ _ _ reordered).1
  have firstMember : source.selected.first ∈ source.before.bindings := selected.1 (by simp)
  have secondMember : source.selected.second ∈ source.before.bindings := selected.1 (by simp)
  have afterTokens : (frame.interval.after.quantum.live.map (·.token)).Nodup :=
    (source.transport.after.complete.map (·.token)).nodup
      (by simpa only [List.map_map] using source.transport.after.tokensDistinct)
  intro binding member notFirst notSecond
  obtain ⟨work,leftWork,ran⟩ := resolved
  obtain ⟨cell,present,origin,newLive⟩ := resolved_origins frame.interval.after final moved work leftWork ran
    binding (movedSubset member)
  have classified : cell ∈ selectedFinal ∨ cell ∈ initial := by
    rcases List.mem_append.mp (extended.1.mem_iff.mp present) with localCell | spectatorCell
    · exact Or.inl localCell
    · exact Or.inr (context.1.mem_iff.mpr (List.mem_append.mpr (Or.inr spectatorCell)))
  rcases classified with localCell | originalCell
  · obtain ⟨token,owner,bits,selectedOrigin,ownerMember⟩ := returned_cells outputs selectedReturn cell localCell
    have sameOwner : owner = binding.owner :=
      (RawOwnerFlow.Tree.owner.inj (congrArg Prod.snd (selectedOrigin.symm.trans origin))).1
    rw [← selected.2] at ownerMember
    change owner ∈ [source.selected.first.owner,source.selected.second.owner] at ownerMember
    rcases List.mem_cons.mp ownerMember with first | later
    · exact False.elim (notFirst (sameOwner.symm.trans first))
    · rcases List.mem_cons.mp later with second | impossible
      · exact False.elim (notSecond (sameOwner.symm.trans second))
      · cases impossible
  · obtain ⟨old,oldMember,seedOrigin⟩ := seed_origins source.before.bindings initial seeded cell originalCell
    have sameCell := seedOrigin.symm.trans origin
    have sameToken : old.port.token = binding.port.token := congrArg Prod.fst sameCell
    have sameOwner : old.owner = binding.owner :=
      (RawOwnerFlow.Tree.owner.inj (congrArg Prod.snd sameCell)).1
    have differentFirst : old.port.token ≠ source.selected.first.port.token := by
      intro equal
      have same := map_unique (fun value : Binding => value.port.token) _ source.before.tokensDistinct
        old oldMember _ firstMember equal
      exact notFirst (sameOwner.symm.trans (congrArg Binding.owner same))
    have differentSecond : old.port.token ≠ source.selected.second.port.token := by
      intro equal
      have same := map_unique (fun value : Binding => value.port.token) _ source.before.tokensDistinct
        old oldMember _ secondMember equal
      exact notSecond (sameOwner.symm.trans (congrArg Binding.owner same))
    have notInput : old.port.token ∉ inputs := by
      rw [source.inputTokens]
      intro present
      rcases List.mem_cons.mp present with first | later
      · exact differentFirst first
      · rcases List.mem_cons.mp later with second | impossible
        · exact differentSecond second
        · cases impossible
    have notContains : inputs.contains old.port.token = false :=
      Bool.eq_false_iff.mpr (fun h => notInput (List.contains_iff_mem.mp h))
    have oldLive := source.before.complete.mem_iff.mp (List.mem_map.mpr ⟨old,oldMember,rfl⟩)
    have oldSpectator : old.port ∈ PureInterval.spectators frame.interval.before inputs :=
      List.mem_filter.mpr ⟨oldLive,by simp only [notContains,Bool.not_false]⟩
    have oldAfter : old.port ∈ frame.interval.after.quantum.live :=
      (List.mem_filter.mp (frame.spectators ▸ oldSpectator)).1
    have samePort := map_unique (fun port : Semantics.Raw.Port => port.token) _ afterTokens
      old.port oldAfter binding.port newLive sameToken
    have equal : old = binding :=
      (congrArg (fun owner => (⟨owner,old.port⟩ : Binding)) sameOwner).trans
        (congrArg (fun port => (⟨binding.owner,port⟩ : Binding)) samePort)
    exact equal ▸ oldMember

#print axioms selection_spectators

end Qleisli.RuntimeSelectionSpectators
