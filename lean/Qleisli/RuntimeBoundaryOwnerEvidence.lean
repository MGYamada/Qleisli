import Qleisli.RuntimeStorageOwnerEvidence
import QleisliKernel.Qirf.RuntimeSourceBoundary

/-! Owner-code evidence for the actual complete source input/output maps.
The input construction preserves the full carrier list by its original length
and basis checks; outputs retain that exact list directly. These proofs derive
per-owner availability, not an observed joined code/frame read or intermediate
body availability, and introduce no runtime checks.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeBoundaryOwnerEvidence
open QleisliKernel QleisliKernel.Finite QleisliKernel.Qirf
open RuntimeOwnerMap (Map Binding)
open RuntimeForestCode (OwnerCodes carrierOwners)
open Semantics.RuntimeStorage

private theorem mapped_carriers (roles : List Semantics.SourceOwners.Owner)
    (owners : List Semantics.CarrierInterface.Owner) (lengths : roles.length = owners.length)
    (assigned : Map) (work left : Nat)
    (ran : (((roles.zip owners).mapM fun pair =>
      if _same : pair.1.basis = pair.2.basis then
        pure (⟨pair.1,pair.2.port⟩ : Binding)
      else throw .request) : WorkM Map).run work = (.ok assigned,left)) :
    carrierOwners assigned = owners := by
  induction roles generalizing owners assigned work left with
  | nil =>
    have empty : owners = [] := List.eq_nil_of_length_eq_zero lengths.symm
    subst owners
    have same : assigned = [] := (pure_success _ _ _ _ ran).1
    subst assigned
    rfl
  | cons role roles ih =>
    cases owners with
    | nil => cases lengths
    | cons owner owners =>
      have tailLengths : roles.length = owners.length := Nat.succ.inj lengths
      simp only [List.zip_cons_cons,List.mapM_cons] at ran
      obtain ⟨first,middle,head,rest⟩ := bind_success _ _ _ _ _ ran
      obtain ⟨tail,last,tailRead,returned⟩ := bind_success _ _ _ _ _ rest
      have same : assigned = first::tail := (pure_success _ _ _ _ returned).1
      subst assigned
      have firstCarrier : (⟨first.port,first.owner.basis⟩ : Semantics.CarrierInterface.Owner) = owner := by
        split at head
        next sameBasis =>
          have sameFirst : first = ⟨role,owner.port⟩ := (pure_success _ _ _ _ head).1
          rw [sameFirst]
          cases owner with
          | mk port basis =>
            exact congrArg (fun basis => (⟨port,basis⟩ : Semantics.CarrierInterface.Owner)) sameBasis
        next _different => cases head
      have tailCarriers := ih owners tailLengths tail middle last tailRead
      change (⟨first.port,first.owner.basis⟩ : Semantics.CarrierInterface.Owner) ::
        carrierOwners tail = owner :: owners
      rw [firstCarrier,tailCarriers]

/-- The successful actual binding construction preserves every input carrier
in order. Its original length guard rules out zip truncation, and its original
basis equality is used for each complete carrier, not just its width. -/
theorem bindings_carriers {roles owners assigned}
    (read : RuntimeInterval.Computed (RuntimeSourceBoundary.bindings roles owners) assigned) :
    carrierOwners assigned = owners := by
  obtain ⟨work,left,ran⟩ := read
  unfold RuntimeSourceBoundary.bindings at ran
  obtain ⟨_charged,afterCharge,_charge,rest⟩ := bind_success _ _ _ _ _ ran
  obtain ⟨done,afterGuard,lengthRead,mapped⟩ := bind_success _ _ _ _ _ rest
  cases done
  have lengths : roles.length = owners.length := beq_iff_eq.mp (guard_success _ _ _ _ lengthRead).1
  exact mapped_carriers roles owners lengths assigned afterGuard left mapped

/-- The same check invocation returns exactly its assigned map. All existing
owner/token/complete-frame checks are still premises of that invocation. -/
theorem check_bindings {roles state assigned} (checked : RuntimeOwnerMap.Checked roles state)
    (read : RuntimeInterval.Computed (RuntimeOwnerMap.check roles state assigned) checked) :
    checked.bindings = assigned := by
  obtain ⟨work,left,ran⟩ := read
  unfold RuntimeOwnerMap.check at ran
  obtain ⟨result,middle,_original,returned⟩ := bind_success _ _ _ _ _ ran
  have same : checked = result.val := (pure_success _ _ _ _ returned).1
  rw [same]
  exact result.property

private theorem codes_of_carrier_reads (bindings : Map) :
    (∀ owner ∈ carrierOwners bindings,
      ∃ layout, RuntimeInterval.Computed (Carrier.readOwner owner) layout) →
      Nonempty (OwnerCodes bindings) := by
  induction bindings with
  | nil => intro _reads; exact ⟨.nil⟩
  | cons binding rest ih =>
    intro reads
    obtain ⟨layout,read⟩ := reads ⟨binding.port,binding.owner.basis⟩ List.mem_cons_self
    have tailReads : ∀ owner ∈ carrierOwners rest,
        ∃ layout, RuntimeInterval.Computed (Carrier.readOwner owner) layout := by
      intro owner present
      exact reads owner (List.mem_cons_of_mem _ present)
    obtain ⟨tail⟩ := ih tailReads
    exact ⟨.cons ⟨layout,read⟩ tail⟩

private theorem stores_readOwner {types stores}
    (reads : RuntimeSourceBoundary.StorageReads types stores) :
    ∀ owner ∈ stores.flatMap quantum,
      ∃ layout, RuntimeInterval.Computed (Carrier.readOwner owner) layout := by
  induction reads with
  | nil => intro owner present; cases present
  | cons head tail ih =>
    intro owner present
    simp only [List.flatMap_cons] at present
    rcases List.mem_append.mp present with first | later
    · exact RuntimeStorageOwnerEvidence.quantum_readOwner head owner first
    · exact ih owner later

/-- The complete original input map has the exact retained storage carrier
order, derived from that input boundary's own actual two reader sub-runs. -/
theorem inputs_carriers {sources owner name signature dependencies program}
    {body : @SourceTypes.SourceRuntimeTrace.Body sources owner name signature}
    {root : RuntimeInterval.Prepared dependencies program}
    {stores : List Semantics.RuntimeStorage.Value}
    (inputs : RuntimeSourceBoundary.Inputs body root stores) :
    carrierOwners inputs.owners.bindings = stores.flatMap quantum := by
  obtain ⟨work,left,ran⟩ := inputs.derived
  obtain ⟨assigned,middle,assignment,checked⟩ := bind_success _ _ _ _ _ ran
  have same := check_bindings inputs.owners ⟨middle,left,checked⟩
  have carriers : carrierOwners assigned = stores.flatMap quantum :=
    bindings_carriers ⟨work,middle,assignment⟩
  exact (congrArg carrierOwners same).trans carriers

/-- Actual input storage and its exact derived binding map provide all original
per-owner receipts. Nonempty does not choose a runtime owner-code object. -/
theorem inputs_ownerCodes {sources owner name signature dependencies program}
    {body : @SourceTypes.SourceRuntimeTrace.Body sources owner name signature}
    {root : RuntimeInterval.Prepared dependencies program}
    {stores : List Semantics.RuntimeStorage.Value}
    (inputs : RuntimeSourceBoundary.Inputs body root stores) :
    Nonempty (OwnerCodes inputs.owners.bindings) := by
  apply codes_of_carrier_reads
  intro carrier present
  rw [inputs_carriers inputs] at present
  exact stores_readOwner inputs.types carrier present

/-- Actual output storage retains the complete returned carrier list, including
separate zero-width ports. This supplies per-owner evidence for that exact map. -/
theorem outputs_ownerCodes {value state owners stored tokens}
    (outputs : RuntimeSourceBoundary.Outputs value state owners stored tokens) :
    Nonempty (OwnerCodes owners.bindings) := by
  apply codes_of_carrier_reads
  intro carrier present
  have carriers : carrierOwners owners.bindings = quantum stored := outputs.originalOwners.symm
  rw [carriers] at present
  exact RuntimeStorageOwnerEvidence.quantum_readOwner outputs.types carrier present

#print axioms bindings_carriers
#print axioms check_bindings
#print axioms inputs_carriers
#print axioms inputs_ownerCodes
#print axioms outputs_ownerCodes

end Qleisli.RuntimeBoundaryOwnerEvidence
