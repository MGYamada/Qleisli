import QleisliKernel.Qirf.RuntimeForestCode

/-! Prop-level owner-code evidence and derived per-owner availability.
Existing carrier invocations expose their original readOwner sub-runs. A
separate basis-read lemma explicitly proves derived availability. No runtime
choice, new check, or availability for an arbitrary intermediate forest follows.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeOwnerCodeEvidence
open QleisliKernel QleisliKernel.Finite QleisliKernel.Qirf
open RuntimeOwnerMap (Map)
open RuntimeForestCode (OwnerCodes carrierOwners)

private theorem readOwners_nonempty (bindings : Map) (work left : Nat)
    (ran : (Carrier.readOwners (carrierOwners bindings)).run work = (.ok (),left)) :
    Nonempty (OwnerCodes bindings) := by
  induction bindings generalizing work with
  | nil => exact ⟨.nil⟩
  | cons binding rest ih =>
    simp only [Carrier.readOwners,carrierOwners,List.map_cons,List.foldlM_cons] at ran
    obtain ⟨done,middle,head,tail⟩ := bind_success _ _ _ _ _ ran
    cases done
    obtain ⟨layout,after,original,_returned⟩ := bind_success _ _ _ _ _ head
    obtain ⟨owners⟩ := ih middle tail
    exact ⟨.cons ⟨layout,⟨work,after,original⟩⟩ owners⟩

/-- A successful actual full-owner read supplies every original readOwner
receipt in binding order. Nonempty permits no runtime extraction from Prop. -/
theorem of_readOwners (bindings : Map)
    (read : RuntimeInterval.Computed (Carrier.readOwners (carrierOwners bindings)) ()) :
    Nonempty (OwnerCodes bindings) := by
  obtain ⟨work,left,ran⟩ := read
  exact readOwners_nonempty bindings work left ran

/-- Extract only the inner readOwners sub-run of this same successful ownerCode
invocation. No old run is inferred from matching source/type/layout metadata. -/
theorem ownerCode_readOwners {owners : List Semantics.CarrierInterface.Owner} {code : Semantics.Exact.Matrix}
    (read : RuntimeInterval.Computed (Carrier.ownerCode owners) code) :
    RuntimeInterval.Computed (Carrier.readOwners owners) () := by
  obtain ⟨work,left,ran⟩ := read
  unfold Carrier.ownerCode at ran
  obtain ⟨_unit,afterGuard,_guard,tail⟩ := bind_success _ _ _ _ _ ran
  obtain ⟨_code,afterCode,_codeRead,tail⟩ := bind_success _ _ _ _ _ tail
  obtain ⟨done,afterOwners,ownersRead,_returned⟩ := bind_success _ _ _ _ _ tail
  cases done
  exact ⟨afterCode,afterOwners,ownersRead⟩

/-- The actual complete ownerCode read supplies the same ordered per-owner
evidence, without a new read or an availability converse. -/
theorem of_ownerCode (bindings : Map) {code : Semantics.Exact.Matrix}
    (read : RuntimeInterval.Computed (Carrier.ownerCode (carrierOwners bindings)) code) :
    Nonempty (OwnerCodes bindings) :=
  of_readOwners bindings (ownerCode_readOwners read)

/-- Derived reader availability from the same successful basis read and its
actual port equalities. This is not an observed Carrier invocation or a claim
that the public caller's remaining work suffices for an intermediate frame. -/
theorem of_basis_read (binding : RuntimeOwnerMap.Binding) (layout : Semantics.FiniteCarrier.Layout)
    (read : RuntimeInterval.Computed (FiniteCarrier.read binding.owner.basis) layout)
    (bits : binding.port.bits = layout.bits) (wires : binding.port.wires.length = layout.bits) :
    RuntimeInterval.Computed (Carrier.readOwner ⟨binding.port,binding.owner.basis⟩) layout := by
  obtain ⟨work,left,ran⟩ := read
  have ports : (binding.port.bits == layout.bits && binding.port.wires.length == layout.bits) = true := by
    simp only [Bool.and_eq_true,beq_iff_eq]
    exact ⟨bits,wires⟩
  have guarded : (guard (binding.port.bits == layout.bits && binding.port.wires.length == layout.bits)
      .request).run left = (.ok (),left) :=
    congrArg (fun condition => (guard condition .request).run left) ports
  refine ⟨work,left,?_⟩
  calc
    (Carrier.readOwner ⟨binding.port,binding.owner.basis⟩).run work =
        ((guard (binding.port.bits == layout.bits && binding.port.wires.length == layout.bits) .request
          >>= fun _ => pure layout) : WorkM Semantics.FiniteCarrier.Layout).run left := by
      unfold Carrier.readOwner
      rw [bind_run,ran]
    _ = (pure layout : WorkM Semantics.FiniteCarrier.Layout).run left := by
      rw [bind_run,guarded]
    _ = (.ok layout,left) := rfl

#print axioms of_readOwners
#print axioms ownerCode_readOwners
#print axioms of_ownerCode
#print axioms of_basis_read

end Qleisli.RuntimeOwnerCodeEvidence
