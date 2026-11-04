import Qleisli.RuntimeOwnerBindingFacts
import Qleisli.RuntimeSelectionSpectators
import Qleisli.RuntimeLiteralFrame
import QleisliKernel.Qirf.RuntimeSelectionWires

/-! Shape-independent code coordinates of the same literal source selection.
Actual spectator identities, original owner order and the circuit trace supply
the complete before/after code equality. Every nominal tree and separate empty
owner remains in its original position. This is not identity of the quantum
action, bounded arithmetic availability, Gram or a new native acceptance rule.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeSelectionCodes
open QleisliKernel QleisliKernel.Qirf
open RuntimeOwnerMap (Binding Map)
open RuntimeForestCode
open Qleisli.RuntimeOwnerTransitionAction (map_unique)

private theorem owner_ordinals {roles state} (checked : RuntimeOwnerMap.Checked roles state) :
    (checked.bindings.map (fun binding => binding.owner.ordinal)).Nodup := by
  have ordered := congrArg (List.map (fun owner : RuntimeOwnerMap.Owner => owner.ordinal)) checked.ordered
  simp only [List.map_map,Function.comp_def] at ordered
  rw [ordered]
  exact checked.ownersDistinct

private theorem wire_map_eq (before : Map) : ∀ after : Map,
    after.map (·.owner) = before.map (·.owner) →
    (∀ old ∈ before,∀ current ∈ after,old.owner = current.owner → old.port.wires = current.port.wires) →
    after.map (fun binding => (binding.owner,binding.port.wires)) =
      before.map (fun binding => (binding.owner,binding.port.wires)) := by
  induction before with
  | nil =>
    intro after ordered _wires
    cases after with
    | nil => rfl
    | cons first rest => simp at ordered
  | cons old before ih =>
    intro after ordered wires
    cases after with
    | nil => simp at ordered
    | cons current after =>
      have equal : current.owner = old.owner ∧ after.map (·.owner) = before.map (·.owner) := by
        simpa only [List.map_cons,List.cons.injEq] using ordered
      have headWire := wires old (List.mem_cons_self) current (List.mem_cons_self) equal.1.symm
      have tail := ih after equal.2 (fun a member b present same =>
        wires a (List.mem_cons_of_mem _ member) b (List.mem_cons_of_mem _ present) same)
      simp only [List.map_cons,equal.1,headWire,tail]

/-- The actual selected boundary and same original spectator bindings preserve
the complete ordered source owner/wire map, without a lowering-shape premise. -/
theorem selection_wires
    {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles)
    {selectorBits targetBits retained restricted}
    (literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
      source.before source.transport.after) :
    source.transport.after.bindings.map (fun binding => (binding.owner,binding.port.wires)) =
      source.before.bindings.map (fun binding => (binding.owner,binding.port.wires)) := by
  have spectators := Qleisli.RuntimeSelectionSpectators.selection_spectators frame source
  have selected := (RuntimeSelectionPartition.order_values _ _ _ source.selected.ordered).1
  have returned := (RuntimeSelectionPartition.order_values _ _ _ source.returned.ordered).1
  have boundary := (RuntimeSelectionWires.source_boundary frame source literal).1
  have pair : (source.returned.first.owner,source.returned.first.port.wires) =
        (source.selected.first.owner,source.selected.first.port.wires) ∧
      (source.returned.second.owner,source.returned.second.port.wires) =
        (source.selected.second.owner,source.selected.second.port.wires) := by
    simpa only [List.map_cons,List.map_nil,List.cons.injEq,and_true] using boundary
  apply wire_map_eq source.before.bindings source.transport.after.bindings source.transport.after.ordered
  intro old oldMember current currentMember sameOwner
  by_cases first : current.owner = source.selected.first.owner
  · have currentEq := map_unique (fun binding : Binding => binding.owner.ordinal) _
      (owner_ordinals source.transport.after) current currentMember
      source.returned.first (returned (by simp))
      (congrArg (·.ordinal) (first.trans (congrArg Prod.fst pair.1).symm))
    have oldEq := map_unique (fun binding : Binding => binding.owner.ordinal) _
      (owner_ordinals source.before) old oldMember source.selected.first (selected (by simp))
      (congrArg (·.ordinal) (sameOwner.trans first))
    rw [currentEq,oldEq]
    exact (congrArg Prod.snd pair.1).symm
  · by_cases second : current.owner = source.selected.second.owner
    · have currentEq := map_unique (fun binding : Binding => binding.owner.ordinal) _
        (owner_ordinals source.transport.after) current currentMember
        source.returned.second (returned (by simp))
        (congrArg (·.ordinal) (second.trans (congrArg Prod.fst pair.2).symm))
      have oldEq := map_unique (fun binding : Binding => binding.owner.ordinal) _
        (owner_ordinals source.before) old oldMember source.selected.second (selected (by simp))
        (congrArg (·.ordinal) (sameOwner.trans second))
      rw [currentEq,oldEq]
      exact (congrArg Prod.snd pair.2).symm
    · have present := spectators current currentMember first second
      have equal := map_unique (fun binding : Binding => binding.owner.ordinal) _
        (owner_ordinals source.before) old oldMember current present (congrArg (·.ordinal) sameOwner)
      exact congrArg (fun binding : Binding => binding.port.wires) equal

private theorem forest_by_bases (owners : List Semantics.CarrierInterface.Owner) :
    Semantics.CarrierInterface.forest owners =
      match owners.map (·.basis) with
      | [] => [.unit]
      | [basis] => basis
      | [first,second] => .pair :: first ++ second
      | bases => .tuple bases.length :: bases.flatMap id := by
  cases owners with
  | nil => rfl
  | cons first rest => cases rest with
    | nil => rfl
    | cons second rest => cases rest with
      | nil => rfl
      | cons third rest =>
        simp only [Semantics.CarrierInterface.forest,List.map_cons,List.length_cons,List.flatMap_cons]
        rw [List.length_map,List.flatMap_map]
        rfl

/-- The same actual literal selection preserves its full sparse code at every
coordinate, including padding, arbitrary axis order and every zero-width owner.
Only frame/source/literal receipts are inputs; no final code equality is supplied. -/
theorem selection_codes {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles)
    {selectorBits targetBits retained restricted}
    (literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
      source.before source.transport.after) :
    literal.inputCode.code.dimension = literal.outputCode.code.dimension ∧
      ∀ physical logical,literal.inputCode.embedding physical logical = literal.outputCode.embedding physical logical := by
  have wiresMap := selection_wires frame source literal
  have actualFrame := Qleisli.RuntimeLiteralFrame.literal_frame literal
  have owners := source.transport.after.ordered
  have bases := congrArg (List.map (fun owner : RuntimeOwnerMap.Owner => owner.basis)) owners
  have sameForest : forestBasis source.transport.after.bindings = forestBasis source.before.bindings := by
    unfold forestBasis
    rw [forest_by_bases,forest_by_bases]
    have same : (carrierOwners source.transport.after.bindings).map (·.basis) =
        (carrierOwners source.before.bindings).map (·.basis) := by
      simpa only [carrierOwners,List.map_map,Function.comp_def] using bases
    rw [same]
  have wires := congrArg (List.flatMap (fun pair : RuntimeOwnerMap.Owner × List Nat => pair.2)) wiresMap
  simp only [List.flatMap_map] at wires
  obtain ⟨left,leftRead,leftSame⟩ := literal.inputCode.originalCode
  obtain ⟨right,rightRead,rightSame⟩ := literal.outputCode.originalCode
  rw [sameForest] at rightRead
  have same : left = right := Option.some.inj (leftRead.symm.trans rightRead)
  subst right
  refine ⟨leftSame.dimension.trans rightSame.dimension.symm,?_⟩
  intro physical logical
  change sparseEntry literal.inputCode.code
      (Semantics.Finite.gather physical (forestAxes frame.interval.before.quantum.frame source.before.bindings)) logical =
    sparseEntry literal.outputCode.code
      (Semantics.Finite.gather physical (forestAxes frame.interval.after.quantum.frame source.transport.after.bindings)) logical
  unfold forestAxes
  rw [actualFrame,wires]
  unfold sparseEntry
  rw [leftSame.labels logical,rightSame.labels logical]

/-- The same original ordered selected axes are the actual returned axes.
This is coordinate transport, not an assertion that the operation is identity. -/
theorem selection_axes {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles)
    {selectorBits targetBits retained restricted}
    (literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
      source.before source.transport.after) :
    forestAxes frame.interval.before.quantum.frame literal.selection.selected =
      forestAxes frame.interval.after.quantum.frame source.returned.toList := by
  have selectedPorts := literal.selectedPorts.trans (RuntimeSelectionPartition.source_ports frame source).1
  have selectedWires := congrArg (List.flatMap (fun port : Semantics.Raw.Port => port.wires)) selectedPorts
  have returnedWires := congrArg (List.flatMap (fun pair : RuntimeOwnerMap.Owner × List Nat => pair.2))
    (RuntimeSelectionWires.source_boundary frame source literal).1
  simp only [List.flatMap_map] at selectedWires returnedWires
  unfold forestAxes
  rw [Qleisli.RuntimeLiteralFrame.literal_frame literal,returnedWires,selectedWires]
  rfl

#print axioms selection_wires
#print axioms selection_codes
#print axioms selection_axes

end Qleisli.RuntimeSelectionCodes
