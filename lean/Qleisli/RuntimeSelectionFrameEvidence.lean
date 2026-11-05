import Qleisli.RuntimeForestFrameEvidence
import Qleisli.RuntimeSelectionCodes
import QleisliKernel.Raw.Ownership

/-! Propagation of original owner-code evidence through one actual selection.
The same sector read preserves the complete ordered owner/wire map. Original
Raw state validity supplies the port shapes at both ends. These facts preserve
the executable per-owner read, without a Literal or a supplied final code.
Availability is derived; no readFrame invocation or remaining-work bound is
claimed, and no arbitrary intermediate source map is covered by this lemma.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeSelectionFrameEvidence
open QleisliKernel QleisliKernel.Qirf
open RuntimeOwnerMap (Binding Map)
open RuntimeForestCode (OwnerCodes Frame)

private theorem binding_shape {roles state} (checked : RuntimeOwnerMap.Checked roles state)
    (valid : Raw.stateValid state.quantum = true) (binding : Binding)
    (present : binding ∈ checked.bindings) : binding.port.bits = binding.port.wires.length := by
  have live : binding.port ∈ state.quantum.live :=
    checked.complete.mem_iff.mp (List.mem_map.mpr ⟨binding,present,rfl⟩)
  exact ((Raw.Ownership.valid state.quantum valid).ports binding.port live).1

private theorem readOwner_equal (old current : Binding)
    (owner : current.owner = old.owner) (wires : current.port.wires = old.port.wires)
    (bits : current.port.bits = old.port.bits) :
    Carrier.readOwner ⟨current.port,current.owner.basis⟩ =
      Carrier.readOwner ⟨old.port,old.owner.basis⟩ := by
  unfold Carrier.readOwner
  rw [owner,bits,wires]

private theorem transport {before : Map} (owners : OwnerCodes before) :
    ∀ after : Map,
      after.map (fun binding => (binding.owner,binding.port.wires)) =
        before.map (fun binding => (binding.owner,binding.port.wires)) →
      (∀ binding ∈ before,binding.port.bits = binding.port.wires.length) →
      (∀ binding ∈ after,binding.port.bits = binding.port.wires.length) →
      Nonempty (OwnerCodes after) := by
  induction owners with
  | nil =>
    intro after ordered _beforeShape _afterShape
    cases after with
    | nil => exact ⟨.nil⟩
    | cons binding rest => simp at ordered
  | @cons old before first rest ih =>
    intro after ordered beforeShape afterShape
    cases after with
    | nil => simp at ordered
    | cons current after =>
      have related : (current.owner,current.port.wires) = (old.owner,old.port.wires) ∧
          after.map (fun binding => (binding.owner,binding.port.wires)) =
            before.map (fun binding => (binding.owner,binding.port.wires)) := by
        simpa only [List.map_cons,List.cons.injEq] using ordered
      have owner : current.owner = old.owner := congrArg Prod.fst related.1
      have wires : current.port.wires = old.port.wires := congrArg Prod.snd related.1
      have bits : current.port.bits = old.port.bits :=
        (afterShape current List.mem_cons_self).trans
          ((congrArg List.length wires).trans (beforeShape old List.mem_cons_self).symm)
      have sameRead := readOwner_equal old current owner wires bits
      have original : RuntimeInterval.Computed
          (Carrier.readOwner ⟨current.port,current.owner.basis⟩) first.layout := by
        rw [sameRead]
        exact first.original
      have beforeTail : ∀ binding ∈ before,binding.port.bits = binding.port.wires.length :=
        fun binding present => beforeShape binding (List.mem_cons_of_mem _ present)
      have afterTail : ∀ binding ∈ after,binding.port.bits = binding.port.wires.length :=
        fun binding present => afterShape binding (List.mem_cons_of_mem _ present)
      obtain ⟨tail⟩ := ih after related.2 beforeTail afterTail
      exact ⟨.cons ⟨first.layout,original⟩ tail⟩

/-- The same actual source selection propagates all complete original owner
receipts, including unchanged spectators and separate zero-width owners.
No Literal, final code, or arbitrary intermediate availability is assumed. -/
theorem ownerCodes_after
    {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles)
    {selectorBits targetBits : Nat} {retained : Raw.Sector.Retained}
    (restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits selectorBits] [.bits targetBits]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained)
    (available : Nonempty (OwnerCodes source.before.bindings)) :
    Nonempty (OwnerCodes source.transport.after.bindings) := by
  obtain ⟨owners⟩ := available
  exact transport owners source.transport.after.bindings
    (RuntimeSelectionCodes.selection_wires_of_read frame source restricted)
    (binding_shape source.before frame.interval.history.1)
    (binding_shape source.transport.after frame.interval.history.2.2.1)

/-- This selection's actual returned map consequently has a mathematical
sparse Frame. This is not a claim that readFrame ran or fits a caller budget. -/
theorem frame_after
    {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles)
    {selectorBits targetBits : Nat} {retained : Raw.Sector.Retained}
    (restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits selectorBits] [.bits targetBits]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained)
    (available : Nonempty (OwnerCodes source.before.bindings)) :
    Nonempty (Frame source.transport.after) :=
  RuntimeForestFrameEvidence.of_ownerCodes source.transport.after
    (ownerCodes_after frame source restricted available)

#print axioms ownerCodes_after
#print axioms frame_after

end Qleisli.RuntimeSelectionFrameEvidence
