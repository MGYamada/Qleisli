import Qleisli.RuntimeOwnerCodeEvidence
import QleisliKernel.RuntimeStorage

/-! Per-owner evidence from the same checked complete runtime storage.
These are derived availability statements at some work counter, not observed
Carrier calls or a bound on the caller's remaining work. Full forest/code and
intermediate-body availability do not follow from these statements.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeStorageOwnerEvidence
open QleisliKernel QleisliKernel.Qirf
open Semantics.RuntimeStorage

/-- Every quantum owner's complete basis is one of the bases checked for this
same stored prefix. Tuple markers and ordinary leaves cannot supply its port. -/
theorem quantum_basis_mem {stored : Value} {owner : Semantics.CarrierInterface.Owner}
    (present : owner ∈ quantum stored) : owner.basis ∈ bases stored := by
  unfold quantum at present
  obtain ⟨atom,member,selected⟩ := List.mem_filterMap.mp present
  unfold bases
  apply List.mem_filterMap.mpr
  cases atom with
  | ordinary basis value => cases selected
  | tuple arity => cases selected
  | quantum actual =>
    have same : actual = owner := Option.some.inj selected
    subst owner
    exact ⟨.quantum actual,member,rfl⟩

/-- The actual successful basis read and checked port widths refer to the same
independent layout. They therefore prove readOwner availability for this full
carrier owner, including its original wires, token and zero-width identity. -/
theorem quantum_readOwner {expected stored}
    (checked : QleisliKernel.RuntimeStorage.Checked expected stored)
    (owner : Semantics.CarrierInterface.Owner) (present : owner ∈ quantum stored) :
    ∃ layout, RuntimeInterval.Computed (Carrier.readOwner owner) layout := by
  obtain ⟨layout,before,after,ran⟩ := checked.basisReads owner.basis (quantum_basis_mem present)
  obtain ⟨portLayout,portReference,bits,wires⟩ := checked.quantumWidths owner present
  have reference := FiniteCarrier.read_reference owner.basis layout before after ran
  have same : layout = portLayout := Option.some.inj (reference.symm.trans portReference)
  subst portLayout
  exact ⟨layout,RuntimeOwnerCodeEvidence.carrier_of_basis_read owner layout
    ⟨before,after,ran⟩ bits wires⟩

#print axioms quantum_basis_mem
#print axioms quantum_readOwner

end Qleisli.RuntimeStorageOwnerEvidence
