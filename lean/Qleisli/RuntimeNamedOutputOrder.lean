import Qleisli.RuntimeNamedInputAction

/-! Exact laws for output-code order and actual source-owner wire maps.
Only total complex sums are reindexed. No bounded read, work allowance,
source-call correspondence or accepted handle follows from code equality.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeNamedOutputOrder
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Semantics.Exact
open RuntimeOwnerMap (Binding Map)
open RuntimeForestCode RuntimeOwnerCodeReindex
open Qleisli.Semantics.Exact Qleisli.RuntimeForestProduct
open Qleisli.RuntimeForestOrderedProduct Qleisli.RuntimeForestRegroup

theorem bijection_range (size : Nat) (forward backward : Nat → Nat)
    (forwardBound : ∀ value < size,forward value < size)
    (backwardBound : ∀ value < size,backward value < size)
    (left : ∀ value < size,backward (forward value) = value)
    (right : ∀ value < size,forward (backward value) = value) :
    ((List.range size).map forward).Perm (List.range size) := by
  have unique : ((List.range size).map forward).Nodup :=
    List.Nodup.map_on (fun a aMember b bMember equal => by
      have same := congrArg backward equal
      rw [left a (List.mem_range.mp aMember),left b (List.mem_range.mp bMember)] at same
      exact same) List.nodup_range
  apply (List.perm_ext_iff_of_nodup unique List.nodup_range).mpr
  intro value
  constructor
  · intro member
    obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
    exact List.mem_range.mpr (forwardBound original (List.mem_range.mp present))
  · intro member
    have small := List.mem_range.mp member
    exact List.mem_map.mpr ⟨backward value,List.mem_range.mpr (backwardBound value small),right value small⟩

/-- The dense coordinate domain is reindexed using the same retained owners'
actual logical cardinalities. Physical padding and every dimension-one owner
keep their existing positions in the original binding lists. -/
theorem regroup_range {roles state checked} (frame : @Frame roles state checked)
    (wanted : Map) (retained : Retained frame.owners wanted) (permutation : wanted.Perm checked.bindings) :
    ((List.range frame.code.dimension).map (regroupIndex frame wanted)).Perm
      (List.range frame.code.dimension) := by
  have size := regroup_volume frame wanted retained permutation
  apply bijection_range frame.code.dimension (regroupIndex frame wanted)
    (Qleisli.MixedRadix.recode wanted checked.bindings (dimensionAt frame.owners))
  · intro logical small
    simpa only [← size] using regroup_bound frame wanted retained permutation logical small
  · intro logical small
    have positive := cards_positive frame.owners
    have result := Qleisli.MixedRadix.recode_bound wanted checked.bindings (dimensionAt frame.owners)
      permutation (fun binding member => positive binding (permutation.subset member)) logical
      (by rw [owner_volume frame.owners retained.codes permutation.subset,← size]; exact small)
    rw [frame_volume frame] at result
    exact result
  · exact regroup_inverse frame wanted permutation
  · intro logical small
    exact regroup_reverse frame wanted retained permutation logical (by rwa [← size])

/-- Unlike the coefficient-only regrouping law, this equation also transports
the arbitrary logical/reference family into the actual reordered dense domain.
The inverse is the same exact owner/cardinality recoding, not a width shuffle. -/
theorem regroup_dense_action {Reference : Type} {roles state checked} (frame : @Frame roles state checked)
    (wanted : Map) (retained : Retained frame.owners wanted) (permutation : wanted.Perm checked.bindings)
    (joint : Nat → Reference → ℂ) (physical : Nat) (reference : Reference) :
    referenceAction frame joint physical reference =
      ((List.range (sparseProduct retained.codes).dimension).map fun logical =>
        coefficients state.quantum.frame retained.codes physical logical *
          joint (Qleisli.MixedRadix.recode wanted checked.bindings (dimensionAt frame.owners) logical) reference).sum := by
  let term := fun logical => coefficients state.quantum.frame retained.codes physical logical *
    joint (Qleisli.MixedRadix.recode wanted checked.bindings (dimensionAt frame.owners) logical) reference
  have indices := regroup_range frame wanted retained permutation
  have terms :
      ((List.range frame.code.dimension).map fun logical =>
        coefficients state.quantum.frame retained.codes physical (regroupIndex frame wanted logical) * joint logical reference).sum =
        ((List.range frame.code.dimension).map fun logical => term (regroupIndex frame wanted logical)).sum := by
    apply Qleisli.Exact.sum_map_congr
    intro logical present
    dsimp only [term]
    rw [regroup_inverse frame wanted permutation logical (List.mem_range.mp present)]
  calc
    _ = _ := regroup_action frame wanted retained permutation joint physical reference
    _ = _ := terms
    _ = ((List.range frame.code.dimension).map term).sum := by
      simpa only [List.map_map,Function.comp_def] using (indices.map term).sum_eq
    _ = _ := by rw [regroup_volume frame wanted retained permutation]

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

/-- Full original source owners and ordered Raw wires remain equal, although
Raw port tokens may change. Empty-wire owners are retained separately. The
source-owner equality is a premise in its own right; code equality cannot
establish it, and no width-only correspondence is admitted. -/
theorem owner_wire_codes {inputRoles outputRoles before after inputChecked outputChecked}
    (input : @Frame inputRoles before inputChecked) (output : @Frame outputRoles after outputChecked)
    (owners : outputChecked.bindings.map (fun binding => (binding.owner,binding.port.wires)) =
      inputChecked.bindings.map (fun binding => (binding.owner,binding.port.wires)))
    (actualFrame : after.quantum.frame = before.quantum.frame) :
    input.code.dimension = output.code.dimension ∧
      ∀ physical logical,input.embedding physical logical = output.embedding physical logical := by
  have sameOwners := congrArg (List.map (fun pair : RuntimeOwnerMap.Owner × List Nat => pair.1)) owners
  have sameBases := congrArg (List.map (fun owner : RuntimeOwnerMap.Owner => owner.basis)) sameOwners
  have sameForest : forestBasis outputChecked.bindings = forestBasis inputChecked.bindings := by
    unfold forestBasis
    rw [forest_by_bases,forest_by_bases]
    have bases : (carrierOwners outputChecked.bindings).map (·.basis) =
        (carrierOwners inputChecked.bindings).map (·.basis) := by
      simpa only [carrierOwners,List.map_map,Function.comp_def] using sameBases
    rw [bases]
  have wires := congrArg (List.flatMap (fun pair : RuntimeOwnerMap.Owner × List Nat => pair.2)) owners
  simp only [List.flatMap_map] at wires
  obtain ⟨left,leftRead,leftSame⟩ := input.originalCode
  obtain ⟨right,rightRead,rightSame⟩ := output.originalCode
  rw [sameForest] at rightRead
  have same : left = right := Option.some.inj (leftRead.symm.trans rightRead)
  subst right
  refine ⟨leftSame.dimension.trans rightSame.dimension.symm,?_⟩
  intro physical logical
  change sparseEntry input.code
      (Semantics.Finite.gather physical (forestAxes before.quantum.frame inputChecked.bindings)) logical =
    sparseEntry output.code
      (Semantics.Finite.gather physical (forestAxes after.quantum.frame outputChecked.bindings)) logical
  unfold forestAxes
  rw [actualFrame,wires]
  unfold sparseEntry
  rw [leftSame.labels logical,rightSame.labels logical]

theorem owner_wire_action {Reference : Type}
    {inputRoles outputRoles before after inputChecked outputChecked}
    (input : @Frame inputRoles before inputChecked) (output : @Frame outputRoles after outputChecked)
    (owners : outputChecked.bindings.map (fun binding => (binding.owner,binding.port.wires)) =
      inputChecked.bindings.map (fun binding => (binding.owner,binding.port.wires)))
    (actualFrame : after.quantum.frame = before.quantum.frame)
    (joint : Nat → Reference → ℂ) (physical : Nat) (reference : Reference) :
    referenceAction input joint physical reference = referenceAction output joint physical reference := by
  obtain ⟨dimension,entries⟩ := owner_wire_codes input output owners actualFrame
  unfold referenceAction
  rw [dimension]
  apply Qleisli.Exact.sum_map_congr
  intro logical _present
  rw [entries physical logical]

#print axioms owner_wire_action
#print axioms regroup_range
#print axioms regroup_dense_action
end Qleisli.RuntimeNamedOutputOrder
