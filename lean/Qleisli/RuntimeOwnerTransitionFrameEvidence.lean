import Qleisli.RuntimeOwnerLeafOrigins
import Qleisli.RuntimeOwnerBindingFacts
import Qleisli.RuntimeForestFrameEvidence
import QleisliKernel.Raw.Ownership

/-! Derived per-owner availability across the same checked owner transition.
Original owner/width leaves survive the actual seed/fold/resolve/order runs.
Port validity fixes wire lengths at both complete boundaries, so the existing
readOwner computations agree. Physical wire placement and code/action equality
do not follow. No action-only local receipt supplies a complete caller map.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeOwnerTransitionFrameEvidence
open QleisliKernel QleisliKernel.Finite QleisliKernel.Semantics QleisliKernel.Qirf
open RuntimeOwnerMap (Binding Map)
open RuntimeForestCode (OwnerCode OwnerCodes Frame)
open Qleisli.RuntimeOwnerLeafOrigins
open Qleisli.RuntimeOwnerTransitionAction (seedCell seed_origins resolved_origins)

/-- Every returned binding comes from an original complete source owner with
the same actual bit count. This follows from the actual recorded flow, not an
identification of equal-width source types or a proposed output invariant. -/
theorem binding_origins {dependencies program block start count}
    {interval : @RuntimeInterval.Checked dependencies program block start count} {before : Map}
    (source : RuntimeOwnerTransition.Checked interval before) :
    ∀ binding ∈ source.after.bindings,
      ∃ old ∈ before, old.owner = binding.owner ∧ old.port.bits = binding.port.bits := by
  obtain ⟨operations,initial,final,moved,_parsed,seeded,flow,resolved,reordered⟩ := source.flow
  let allowed : SourceOwners.Owner → Nat → Prop := fun owner bits =>
    ∃ old ∈ before, old.owner = owner ∧ old.port.bits = bits
  have initialOrigins : Supports allowed initial := by
    intro cell member
    obtain ⟨old,oldMember,same⟩ := seed_origins before initial seeded cell member
    rw [same]
    exact .leaf ⟨old,oldMember,rfl,rfl⟩
  have finalOrigins := fold_supported operations initialOrigins flow
  have movedSubset := (RuntimeSelectionPartition.order_values _ _ _ reordered).1
  obtain ⟨work,left,ran⟩ := resolved
  intro binding member
  obtain ⟨cell,present,same,_live⟩ := resolved_origins interval.after final moved work left ran
    binding (movedSubset member)
  have original := finalOrigins cell present
  rw [same] at original
  exact owner_value original

private theorem code_member {bindings : Map} (owners : OwnerCodes bindings) :
    ∀ binding ∈ bindings, Nonempty (OwnerCode binding) := by
  induction owners with
  | nil => intro binding member; cases member
  | @cons firstBinding bindings first rest ih =>
    intro binding member
    rcases List.mem_cons.mp member with same | later
    · subst binding; exact ⟨first⟩
    · exact ih binding later

private theorem codes_of_members (bindings : Map) :
    (∀ binding ∈ bindings, Nonempty (OwnerCode binding)) → Nonempty (OwnerCodes bindings) := by
  induction bindings with
  | nil => intro _available; exact ⟨.nil⟩
  | cons binding bindings ih =>
    intro available
    obtain ⟨first⟩ := available binding List.mem_cons_self
    obtain ⟨tail⟩ := ih (fun value member => available value (List.mem_cons_of_mem _ member))
    exact ⟨.cons first tail⟩

private theorem binding_shape {roles state} (checked : RuntimeOwnerMap.Checked roles state)
    (valid : Raw.stateValid state.quantum = true) (binding : Binding)
    (present : binding ∈ checked.bindings) : binding.port.bits = binding.port.wires.length := by
  have live : binding.port ∈ state.quantum.live :=
    checked.complete.mem_iff.mp (List.mem_map.mpr ⟨binding,present,rfl⟩)
  exact ((Raw.Ownership.valid state.quantum valid).ports binding.port live).1

/-- Original BEFORE owner receipts propagate across this exact checked
transition. The reader ignores token and wire placement, but its complete basis,
bit count and wire length are proved equal from the original runs and validity. -/
theorem ownerCodes_after {dependencies program block start count roles}
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (before : RuntimeOwnerMap.Checked roles interval.before)
    (source : RuntimeOwnerTransition.Checked interval before.bindings)
    (available : Nonempty (OwnerCodes before.bindings)) :
    Nonempty (OwnerCodes source.after.bindings) := by
  obtain ⟨owners⟩ := available
  apply codes_of_members
  intro current member
  obtain ⟨old,oldMember,sameOwner,sameBits⟩ := binding_origins source current member
  obtain ⟨original⟩ := code_member owners old oldMember
  have oldShape := binding_shape before interval.history.1 old oldMember
  have currentShape := binding_shape source.after interval.history.2.2.1 current member
  have lengths : current.port.wires.length = old.port.wires.length :=
    currentShape.symm.trans (sameBits.symm.trans oldShape)
  have sameRead : Carrier.readOwner ⟨current.port,current.owner.basis⟩ =
      Carrier.readOwner ⟨old.port,old.owner.basis⟩ := by
    unfold Carrier.readOwner
    rw [← sameOwner,← sameBits,lengths]
  refine ⟨⟨original.layout,?_⟩⟩
  rw [sameRead]
  exact original.original

/-- The same returned complete map consequently has a mathematical sparse
Frame. No readFrame invocation, remaining-work bound or code-action equality
is asserted for this or any unrelated intermediate boundary. -/
theorem frame_after {dependencies program block start count roles}
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (before : RuntimeOwnerMap.Checked roles interval.before)
    (source : RuntimeOwnerTransition.Checked interval before.bindings)
    (available : Nonempty (OwnerCodes before.bindings)) : Nonempty (Frame source.after) :=
  Qleisli.RuntimeForestFrameEvidence.of_ownerCodes source.after
    (ownerCodes_after interval before source available)

#print axioms binding_origins
#print axioms ownerCodes_after
#print axioms frame_after

end Qleisli.RuntimeOwnerTransitionFrameEvidence
