import Qleisli.RuntimePrimitiveSemanticLayouts
import Qleisli.RuntimeStructuralLayoutEvidence

/-! Semantic layout preservation at actual source join/split boundaries.
Inputs come from the same checked owner lookup; result trees come from the
event's retained evaluator equation and, for split, its actual pair parser.
Native output widths supply port shape, while spectators keep exact bindings.
No bounded readOwner, output code, Frame availability, phase/action equation,
whole-body preservation theorem or runtime acceptance condition follows.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeStructuralSemanticLayouts
open QleisliKernel QleisliKernel.Finite QleisliKernel.Qirf QleisliKernel.SourceTypes
open SourceRuntimeValues (valueOwners)
open RuntimeOwnerMap (Binding Map)
open Qleisli.RuntimeStructuralLayoutEvidence (SemanticOwnerLayout)

private theorem primitive_eq {first second : CallName.Primitive}
    (same : (first == second) = true) : first = second := by
  cases first <;> cases second <;> cases same <;> rfl

private theorem arguments_layout {dependencies program sources caller block start count event before}
    (action : @RuntimeStructuralAction.Checked dependencies program sources caller block start count event before)
    (available : ∀ binding ∈ before.bindings, Nonempty (SemanticOwnerLayout binding)) :
    ∀ owner ∈ event.arguments.flatMap valueOwners,
      ∃ layout, Semantics.FiniteCarrier.layout owner.basis = some layout := by
  obtain ⟨work,left,ran⟩ := action.inputRead
  obtain ⟨bound,middle,ordered,_returned⟩ := bind_success _ _ _ _ _ ran
  have facts := RuntimeSelectionPartition.order_values before.bindings action.inputRoles bound ⟨work,middle,ordered⟩
  intro owner member
  have inputMember : owner ∈ action.inputRoles := by
    rw [action.originalInputs]
    exact member
  rw [← facts.2] at inputMember
  obtain ⟨binding,present,same⟩ := List.mem_map.mp inputMember
  obtain ⟨original⟩ := available binding (facts.1 present)
  refine ⟨original.layout,?_⟩
  rw [← same]
  exact original.reference

private theorem swap_zip {α β : Type} (first : List α) (second : List β) :
    (first.zip second).map Prod.swap = second.zip first := by
  induction first generalizing second with
  | nil => cases second <;> rfl
  | cons head rest ih =>
    cases second with
    | nil => rfl
    | cons other remaining => exact congrArg (List.cons (other,head)) (ih remaining)

/-- The same actual source event supplies every newly returned basis. The
complete original map retains all untouched bindings, including empty owners;
the checked native output-width receipt binds each new layout to its real port.
Only BEFORE semantic layouts are premises, with no successful after reader. -/
theorem join_split_after_layouts {dependencies program sources caller block start count event before}
    (action : @RuntimeStructuralAction.Checked dependencies program sources caller block start count event before)
    (selected : action.kind = .join ∨ action.kind = .split)
    (available : ∀ binding ∈ before.bindings, Nonempty (SemanticOwnerLayout binding)) :
    ∀ binding ∈ action.after.bindings, Nonempty (SemanticOwnerLayout binding) := by
  have eventKind : event.kind = action.kind.primitive :=
    primitive_eq (Bool.and_eq_true_iff.mp action.source).1
  have resultLayouts : ∀ owner ∈ valueOwners event.value,
      ∃ layout, Semantics.FiniteCarrier.layout owner.basis = some layout := by
    rcases selected with joined | split
    · have selected : event.kind = .join := by
        simpa only [joined,RuntimeStructuralAction.Kind.primitive] using eventKind
      exact Qleisli.RuntimePrimitiveSemanticLayouts.join_result_layout event selected (arguments_layout action available)
    · have selected : event.kind = .split := by
        simpa only [split,RuntimeStructuralAction.Kind.primitive] using eventKind
      exact Qleisli.RuntimePrimitiveSemanticLayouts.split_result_layout event selected (arguments_layout action available)
  intro binding member
  rw [action.afterBindings] at member
  rcases List.mem_append.mp member with previous | created
  · exact available binding (List.mem_filter.mp previous).1
  · obtain ⟨⟨owner,port⟩,paired,same⟩ := List.mem_map.mp created
    subst binding
    have outputMember : owner ∈ valueOwners event.value := by
      have member := (List.of_mem_zip paired).1
      simpa only [action.originalOutputs] using member
    obtain ⟨layout,reference⟩ := resultLayouts owner outputMember
    have reversed : (port,owner) ∈ action.outputs.zip action.outputRoles := by
      have mapped : (port,owner) ∈ (action.outputRoles.zip action.outputs).map Prod.swap :=
        List.mem_map.mpr ⟨(owner,port),paired,rfl⟩
      simpa only [swap_zip] using mapped
    have widths := RuntimeStructuralAction.widths_reference action.outputs action.outputRoles
      action.outputWidths port owner reversed layout reference
    exact ⟨⟨layout,reference,widths.1,widths.2⟩⟩

theorem join_after_layouts {dependencies program sources caller block start count event before}
    (action : @RuntimeStructuralAction.Checked dependencies program sources caller block start count event before)
    (selected : action.kind = .join)
    (available : ∀ binding ∈ before.bindings, Nonempty (SemanticOwnerLayout binding)) :
    ∀ binding ∈ action.after.bindings, Nonempty (SemanticOwnerLayout binding) :=
  join_split_after_layouts action (.inl selected) available

theorem split_after_layouts {dependencies program sources caller block start count event before}
    (action : @RuntimeStructuralAction.Checked dependencies program sources caller block start count event before)
    (selected : action.kind = .split)
    (available : ∀ binding ∈ before.bindings, Nonempty (SemanticOwnerLayout binding)) :
    ∀ binding ∈ action.after.bindings, Nonempty (SemanticOwnerLayout binding) :=
  join_split_after_layouts action (.inr selected) available

#print axioms join_split_after_layouts
#print axioms join_after_layouts
#print axioms split_after_layouts

end Qleisli.RuntimeStructuralSemanticLayouts
