import Qleisli.RuntimeTargetScatter
import Qleisli.RuntimeNamedHeadCoefficients
import Qleisli.RuntimeNamedSelectionFrames
import Qleisli.RuntimeNamedCallerAction

/-! Exact selected-block/spectator factorization in the original owner order.
The arbitrary logical/reference family need not factor. No joined matrix,
code-read availability, bounded arithmetic reassociation or handle is supplied.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeNamedBlockEncoding
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Semantics.Exact
open RuntimeOwnerMap (Map Binding)
open RuntimeForestCode RuntimeOwnerCodeReindex
open Qleisli.Semantics.Exact Qleisli.RuntimeForestProduct
open Qleisli.RuntimeForestOrderedProduct Qleisli.RuntimeForestRegroup
open Qleisli.RuntimeNamedHeadCoefficients

def append {left right : Map} (first : OwnerCodes left) (second : OwnerCodes right) :
    OwnerCodes (left++right) :=
  match first with
  | .nil => second
  | .cons head tail => .cons head (append tail second)

theorem dimension_append {left right : Map} (first : OwnerCodes left) (second : OwnerCodes right) :
    (sparseProduct (append first second)).dimension =
      (sparseProduct first).dimension * (sparseProduct second).dimension := by
  induction first with
  | nil =>
    change (sparseProduct second).dimension = 1 * (sparseProduct second).dimension
    exact (Nat.one_mul _).symm
  | cons head tail ih =>
    simp only [append,sparseProduct,Sparse.tensor]
    rw [ih,Nat.mul_assoc]

/-- The two blocks retain their exact ordered owner digits. This is a
coefficient identity, not a separability premise on the input state. -/
theorem coefficients_append {left right : Map} (first : OwnerCodes left) (second : OwnerCodes right)
    (frame : List Nat) (physical logical : Nat) :
    coefficients frame (append first second) physical logical =
      coefficients frame first physical (logical % (sparseProduct first).dimension) *
        coefficients frame second physical (logical / (sparseProduct first).dimension) := by
  induction first generalizing logical with
  | nil =>
    change coefficients frame second physical logical =
      (if logical%1 = 0 then 1 else 0) * coefficients frame second physical (logical/1)
    rw [Nat.mod_one,Nat.div_one,if_pos rfl,one_mul]
  | cons head tail ih =>
    simp only [append,coefficients,sparseProduct,Sparse.tensor,Sparse.ofLayout]
    rw [ih,Nat.mod_mul_right_mod,Nat.mod_mul_right_div_self,Nat.div_div_eq_div_mul,mul_assoc]

/-- Reindex the full finite sum into a selected block and its untouched
spectator fibre. The original joint/reference coefficients remain arbitrary. -/
theorem group_sum {Reference : Type} (low high : Nat) (positive : 0 < low)
    (selected spectator : Nat → Complex) (joint : Nat → Reference → Complex) (reference : Reference) :
    ((List.range (low*high)).map fun logical =>
      selected (logical%low) * spectator (logical/low) * joint logical reference).sum =
      ((List.range low).map fun digit =>
        selected digit * fibre low high spectator joint digit reference).sum := by
  rw [sum_blocks]
  calc
    _ = ((List.range high).map fun block =>
      ((List.range low).map fun digit =>
        selected digit * (spectator block * joint (digit+low*block) reference)).sum).sum := by
      apply Qleisli.Exact.sum_map_congr
      intro block _member
      apply Qleisli.Exact.sum_map_congr
      intro digit member
      have bound := List.mem_range.mp member
      rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt bound,
        Nat.add_mul_div_left _ _ positive,Nat.div_eq_of_lt bound,Nat.zero_add,mul_assoc]
    _ = ((List.range low).map fun digit =>
      ((List.range high).map fun block =>
        selected digit * (spectator block * joint (digit+low*block) reference)).sum).sum :=
      Qleisli.Exact.sum_swap _ _ _
    _ = _ := by simp only [fibre,List.sum_map_mul_left]

theorem dimension_positive {bindings : Map} (owners : OwnerCodes bindings) :
    0 < (sparseProduct owners).dimension := by
  induction owners with
  | nil => exact Nat.zero_lt_one
  | cons first rest ih => exact Nat.mul_pos (owner_bounds first).1 ih

/-- The real complete frame is decomposed using the original selected
bindings, exact cardinalities and the same retained code receipts. Every
spectator amplitude may depend on every selected and reference coordinate. -/
theorem frame_block_encoding {Reference : Type} {roles state checked}
    (frame : @Frame roles state checked) (selected spectators : Map)
    (selectedCodes : OwnerCodes selected) (spectatorCodes : OwnerCodes spectators)
    (kept : reindex frame.owners (selected++spectators) = some (append selectedCodes spectatorCodes))
    (permutation : (selected++spectators).Perm checked.bindings)
    (joint : Nat → Reference → Complex) (physical : Nat) (reference : Reference) :
    referenceAction frame joint physical reference =
      ((List.range (sparseProduct selectedCodes).dimension).map fun digit =>
        coefficients state.quantum.frame selectedCodes physical digit *
          fibre (sparseProduct selectedCodes).dimension (sparseProduct spectatorCodes).dimension
            (fun high => coefficients state.quantum.frame spectatorCodes physical high)
            (fun logical ref => joint (Qleisli.MixedRadix.recode (selected++spectators)
              checked.bindings (dimensionAt frame.owners) logical) ref) digit reference).sum := by
  have law := RuntimeNamedOutputOrder.regroup_dense_action frame (selected++spectators)
    ⟨append selectedCodes spectatorCodes,kept⟩ permutation joint physical reference
  rw [dimension_append] at law
  simp only [coefficients_append] at law
  exact law.trans (group_sum _ _ (dimension_positive selectedCodes) _ _ _ reference)

#print axioms coefficients_append
#print axioms group_sum
#print axioms frame_block_encoding
theorem append_exists (left right : Map) (all : OwnerCodes (left++right)) :
    ∃ first : OwnerCodes left, ∃ second : OwnerCodes right, all = append first second := by
  induction left with
  | nil => exact ⟨.nil,all,rfl⟩
  | cons binding rest ih =>
    cases all with
    | cons first remaining =>
      obtain ⟨front,back,same⟩ := ih remaining
      rw [same]
      exact ⟨.cons first front,back,rfl⟩

private theorem partition_perm (all selected : Map) (allUnique : all.Nodup)
    (selectedUnique : selected.Nodup) (subset : selected ⊆ all) :
    (selected++RuntimeSelectionPartition.complement all selected).Perm all := by
  let chosen : Binding → Bool := fun binding => decide (binding ∈ selected)
  have ordered : selected.Perm (all.filter chosen) := by
    apply (List.perm_ext_iff_of_nodup selectedUnique (List.Pairwise.filter chosen allUnique)).mpr
    intro binding
    simp only [List.mem_filter,chosen,decide_eq_true_eq]
    exact ⟨fun member => ⟨subset member,member⟩,fun member => member.2⟩
  exact (ordered.append_right _).trans (List.filter_append_perm chosen all)

/-- Full input-token uniqueness is derived from the real call input gate,
including empty-wire owners. Wire-axis uniqueness alone is not used for it. -/
theorem original_named_partition
    {dependencies program block callStart callCount inputs ordinary effect sources caller before returned retired value}
    {event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller}
    (scope : @RuntimeCallScope.Checked dependencies program block callStart callCount inputs ordinary effect)
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before returned retired value)
    {roles} (checked : RuntimeOwnerMap.Checked roles scope.interval.before) (frame : Frame checked)
    (sameBindings : checked.bindings = before.bindings) :
    let selected := boundary.input.ordered
    let spectators := RuntimeSelectionPartition.complement checked.bindings selected
    ∃ selectedCodes : OwnerCodes selected, ∃ spectatorCodes : OwnerCodes spectators,
      reindex frame.owners (selected++spectators) = some (append selectedCodes spectatorCodes) ∧
      (selected++spectators).Perm checked.bindings := by
  intro selected spectators
  have opening := RuntimeNamedFrameAxes.initialized scope.entryRead
  have live : scope.localEntry.quantum.live = scope.selected :=
    congrArg Semantics.RawTrace.Interface.live opening.1
  have tokens : (scope.selected.map (·.token)).Nodup := by
    have valid := (Raw.Ownership.valid _ opening.2.1).owners
    change (scope.localEntry.quantum.live.map (·.token)).Nodup at valid
    rw [live] at valid
    exact valid
  have orderedTokens : (selected.map (fun binding => binding.port.token)).Nodup := by
    simpa only [RuntimeNamedFrameAxes.mixed_bound_ports scope boundary,List.map_map,Function.comp_def]
      using tokens
  have unique : selected.Nodup := List.Pairwise.of_map (fun binding : Binding => binding.port.token)
    (fun _ _ different equal => different (congrArg (fun binding : Binding => binding.port.token) equal)) orderedTokens
  have allUnique : checked.bindings.Nodup := List.Pairwise.of_map (fun binding : Binding => binding.port.token)
    (fun _ _ different equal => different (congrArg (fun binding : Binding => binding.port.token) equal)) checked.tokensDistinct
  have subset : selected ⊆ checked.bindings := by
    rw [sameBindings]
    exact (RuntimeSelectionPartition.order_values before.bindings event.inputOwners selected boundary.input.orderRead).1
  have permutation := partition_perm checked.bindings selected allUnique unique subset
  obtain ⟨all,kept⟩ := reindex_exists frame.owners (selected++spectators) permutation.subset
  obtain ⟨front,back,parts⟩ := append_exists selected spectators all
  rw [parts] at kept
  exact ⟨front,back,kept,permutation⟩

#print axioms original_named_partition

end Qleisli.RuntimeNamedBlockEncoding
