import Qleisli.RuntimeForestFrameEvidence
import QleisliKernel.Qirf.RuntimeOwnerCodeReindex
import QleisliKernel.Qirf.RuntimeStructuralAction

/-! Mathematical layouts at the actual explicit source join boundary.
The original selected owner reads supply the independent input forest layout.
The checked original coordinates and returned widths determine the joined
layout, even when a joined scalar read exceeds its existing policy. No output
readOwner, Frame, work availability, code action or new runtime gate follows.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeStructuralLayoutEvidence
open QleisliKernel QleisliKernel.Finite QleisliKernel.Qirf
open RuntimeOwnerMap (Binding Map)
open RuntimeForestCode (OwnerCodes carrierOwners forestBasis)

/-- An independent full source layout and its actual port shape. This proof
record contains no successful bounded carrier-reader receipt. -/
structure SemanticOwnerLayout (binding : Binding) : Type where
  layout : Semantics.FiniteCarrier.Layout
  reference : Semantics.FiniteCarrier.layout binding.owner.basis = some layout
  bits : binding.port.bits = layout.bits
  wires : binding.port.wires.length = layout.bits

private theorem input_layout {dependencies program sources caller block start count event before}
    (action : @RuntimeStructuralAction.Checked dependencies program sources caller block start count event before)
    (available : Nonempty (OwnerCodes before.bindings)) :
    ∃ layout, Semantics.FiniteCarrier.layout
      (Semantics.CarrierInterface.forest (RuntimeStructuralAction.owners action.inputs action.inputRoles)) =
        some layout := by
  obtain ⟨owners⟩ := available
  obtain ⟨work,left,ran⟩ := action.inputRead
  obtain ⟨bound,middle,ordered,returned⟩ := bind_success _ _ _ _ _ ran
  have inputs : action.inputs = bound.map (·.port) := (pure_success _ _ _ _ returned).1
  have facts := RuntimeSelectionPartition.order_values before.bindings action.inputRoles bound
    ⟨work,middle,ordered⟩
  obtain ⟨selected,_retained⟩ := RuntimeOwnerCodeReindex.reindex_exists owners bound facts.1
  obtain ⟨layout,reference⟩ := RuntimeForestFrameEvidence.forest_layout selected
  have sameOwners : RuntimeStructuralAction.owners action.inputs action.inputRoles = carrierOwners bound := by
    rw [inputs,← facts.2]
    simp only [RuntimeStructuralAction.owners,carrierOwners,List.zip_map',List.map_map,Function.comp_def]
  refine ⟨layout,?_⟩
  rw [sameOwners]
  exact reference

private theorem join_role {dependencies program sources caller block start count event before}
    (action : @RuntimeStructuralAction.Checked dependencies program sources caller block start count event before)
    (joined : action.kind = .join) : ∃ role, action.outputRoles = [role] := by
  have value : ∃ role, event.value = [.owner role] := by
    have shape := action.source
    rw [joined] at shape
    unfold RuntimeStructuralAction.sourceShape at shape
    split at shape <;> simp_all
  obtain ⟨role,same⟩ := value
  refine ⟨role,?_⟩
  rw [action.originalOutputs,same]
  rfl

/-- The actual join creates one original owner whose independent layout is
derived from the same selected input reads and checked coordinate equation.
Both real port widths are taken from the checked outputWidths receipt. -/
theorem join_output_layout {dependencies program sources caller block start count event before}
    (action : @RuntimeStructuralAction.Checked dependencies program sources caller block start count event before)
    (joined : action.kind = .join) (available : Nonempty (OwnerCodes before.bindings)) :
    ∃ role port, action.outputRoles = [role] ∧ action.outputs = [port] ∧
      Nonempty (SemanticOwnerLayout (⟨role,port⟩ : Binding)) := by
  obtain ⟨role,roles⟩ := join_role action joined
  have lengths : action.outputs.length = action.outputRoles.length :=
    beq_iff_eq.mp (Bool.and_eq_true_iff.mp action.outputWidths).1
  have lengthOne : action.outputs.length = 1 := by
    simpa only [roles,List.length_cons,List.length_nil] using lengths
  obtain ⟨port,ports⟩ := List.length_eq_one_iff.mp lengthOne
  obtain ⟨layout,inputReference⟩ := input_layout action available
  have outputBasis : Semantics.CarrierInterface.forest
      (RuntimeStructuralAction.owners action.outputs action.outputRoles) = role.basis := by
    rw [ports,roles]
    rfl
  have reference : Semantics.FiniteCarrier.layout role.basis = some layout := by
    rw [← outputBasis,← action.coordinates]
    exact inputReference
  have member : (port,role) ∈ action.outputs.zip action.outputRoles := by
    rw [ports,roles]
    exact List.mem_cons_self
  have widths := RuntimeStructuralAction.widths_reference action.outputs action.outputRoles
    action.outputWidths port role member layout reference
  exact ⟨role,port,roles,ports,⟨⟨layout,reference,widths.1,widths.2⟩⟩⟩

/-- Every complete returned binding has its original semantic layout after
this checked join. Unconsumed bindings reuse their original receipts; the new
joined owner uses the exact result above. No output bounded read is asserted. -/
theorem join_after_layouts {dependencies program sources caller block start count event before}
    (action : @RuntimeStructuralAction.Checked dependencies program sources caller block start count event before)
    (joined : action.kind = .join) (available : Nonempty (OwnerCodes before.bindings)) :
    ∀ binding ∈ action.after.bindings, Nonempty (SemanticOwnerLayout binding) := by
  obtain ⟨role,port,roles,ports,layout⟩ := join_output_layout action joined available
  obtain ⟨owners⟩ := available
  intro binding member
  rw [action.afterBindings] at member
  rcases List.mem_append.mp member with previous | created
  · have oldMember : binding ∈ before.bindings := (List.mem_filter.mp previous).1
    obtain ⟨original,_read⟩ := RuntimeOwnerCodeReindex.lookup_exists owners binding oldMember
    exact ⟨⟨original.layout,original.reference.1,original.reference.2.1,original.reference.2.2⟩⟩
  · have same : binding = (⟨role,port⟩ : Binding) := by
      simpa only [roles,ports,List.zip_cons_cons,List.zip_nil_left,List.map_cons,List.map_nil,
        List.mem_singleton] using created
    subst binding
    exact layout

#print axioms join_output_layout
#print axioms join_after_layouts

end Qleisli.RuntimeStructuralLayoutEvidence
