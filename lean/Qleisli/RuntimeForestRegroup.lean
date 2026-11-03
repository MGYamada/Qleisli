import Qleisli.MixedRadix
import Qleisli.RuntimeForestOrderedProduct
import QleisliKernel.Qirf.RuntimeOwnerCodeReindex

/-! Exact logical regrouping of the same retained runtime forest codes.
Bindings retain source identity, nominal trees, port tokens, wire order and all
zero-width positions. Cardinalities are read from the actual retained carrier
receipts. Logical reindexing changes no global physical coordinate or phase.
No joined matrix, bounded arithmetic equivalence, separability, Gram theorem,
Raw-program theorem or accepted handle is introduced here.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeForestRegroup
open QleisliKernel QleisliKernel.Semantics.Exact
open QleisliKernel.Semantics.Finite (gather)
open QleisliKernel.Qirf QleisliKernel.Qirf.RuntimeForestCode
open QleisliKernel.Qirf.RuntimeOwnerCodeReindex
open Qleisli.Semantics.Exact Qleisli.RuntimeForestProduct Qleisli.RuntimeForestOrderedProduct
open Qleisli.MixedRadix

theorem cards_positive {bindings} (original : OwnerCodes bindings) (binding : RuntimeOwnerMap.Binding)
    (member : binding ∈ bindings) : 0 < dimensionAt original binding := by
  obtain ⟨actual,_ran⟩ := lookup_exists original binding member
  rw [dimensionAt_eq original binding member actual]
  exact (owner_bounds actual).1

/-- Missing identity has coefficient zero, never a fabricated owner encoding.
All following source-bound uses prove the lookup exists in the original map. -/
noncomputable def factorAt (frame : List Nat) {bindings} (original : OwnerCodes bindings)
    (physical : Nat) (binding : RuntimeOwnerMap.Binding) (digit : Nat) : ℂ :=
  match lookup original binding with
  | none => 0
  | some actual => entry (QleisliKernel.Semantics.FiniteCarrier.encoding actual.layout)
      (gather physical (binding.port.wires.map frame.idxOf)) digit

theorem factorAt_eq (frame : List Nat) {bindings} (original : OwnerCodes bindings)
    (physical : Nat) (binding : RuntimeOwnerMap.Binding) (member : binding ∈ bindings)
    (actual : OwnerCode binding) (digit : Nat) :
    factorAt frame original physical binding digit =
      entry (QleisliKernel.Semantics.FiniteCarrier.encoding actual.layout)
        (gather physical (binding.port.wires.map frame.idxOf)) digit := by
  obtain ⟨retained,ran⟩ := lookup_exists original binding member
  simp only [factorAt,ran,layout_unique retained actual]

theorem owner_volume {originalBindings} (original : OwnerCodes originalBindings)
    {bindings} (owners : OwnerCodes bindings) : bindings ⊆ originalBindings →
      volume bindings (dimensionAt original) = (sparseProduct owners).dimension := by
  induction owners with
  | nil => intro _subset; rfl
  | @cons binding bindings first rest ih =>
    intro subset
    change dimensionAt original binding*volume bindings (dimensionAt original) =
      first.layout.labels.length*(sparseProduct rest).dimension
    rw [dimensionAt_eq original binding (subset (List.mem_cons_self)) first,
      ih (fun member => subset (List.mem_cons_of_mem _ member))]

theorem coefficients_factors {originalBindings} (original : OwnerCodes originalBindings) (frame : List Nat)
    {bindings} (owners : OwnerCodes bindings) (physical : Nat) : ∀ logical,
    bindings ⊆ originalBindings → bindings.Nodup → logical < volume bindings (dimensionAt original) →
      coefficients frame owners physical logical =
        (bindings.map fun binding => factorAt frame original physical binding
          (decode bindings (dimensionAt original) logical binding)).prod := by
  induction owners with
  | nil =>
    intro logical _subset _unique bound
    change logical < 1 at bound
    have zero : logical = 0 := by omega
    subst logical
    simp [coefficients]
  | @cons binding bindings first rest ih =>
    intro logical subset unique bound
    have separate := List.nodup_cons.mp unique
    have headCard := dimensionAt_eq original binding (subset (List.mem_cons_self)) first
    have tailBound : logical / dimensionAt original binding < volume bindings (dimensionAt original) :=
      Nat.div_lt_of_lt_mul bound
    have firstEqual : entry (QleisliKernel.Semantics.FiniteCarrier.encoding first.layout)
        (gather physical (binding.port.wires.map frame.idxOf)) (logical % dimensionAt original binding) =
          factorAt frame original physical binding
            (decode (binding::bindings) (dimensionAt original) logical binding) := by
      rw [decode_head]
      exact (factorAt_eq frame original physical binding (subset (List.mem_cons_self)) first _).symm
    have tailFactors :
        (bindings.map fun value => factorAt frame original physical value
          (decode bindings (dimensionAt original) (logical / dimensionAt original binding) value)).prod =
        (bindings.map fun value => factorAt frame original physical value
          (decode (binding::bindings) (dimensionAt original) logical value)).prod := by
      apply congrArg List.prod
      apply List.map_congr_left
      intro value member
      have different : binding ≠ value := by
        intro equal
        exact separate.1 (equal.symm ▸ member)
      have digitEqual : decode (binding::bindings) (dimensionAt original) logical value =
          decode bindings (dimensionAt original) (logical / dimensionAt original binding) value := by
        rw [decode,if_neg different]
      rw [digitEqual]
    have tailEqual := (ih _ (fun member => subset (List.mem_cons_of_mem _ member)) separate.2 tailBound).trans tailFactors
    change entry (QleisliKernel.Semantics.FiniteCarrier.encoding first.layout)
      (gather physical (binding.port.wires.map frame.idxOf)) (logical % first.layout.labels.length) *
        coefficients frame rest physical (logical / first.layout.labels.length) = _
    rw [← headCard]
    exact congrArg₂ (fun a b : ℂ => a*b) firstEqual tailEqual

theorem frame_volume {roles state checked} (frame : @Frame roles state checked) :
    volume checked.bindings (dimensionAt frame.owners) = frame.code.dimension :=
  (owner_volume frame.owners frame.owners (fun member => member)).trans
    ((product_agrees frame.owners).dimension.trans (frame_product_agrees frame).dimension.symm)

private theorem frame_unique {roles state checked} (_frame : @Frame roles state checked) : checked.bindings.Nodup :=
  List.Pairwise.of_map (fun binding : RuntimeOwnerMap.Binding => binding.port.token)
    (fun _ _ different equal => different (congrArg (fun binding : RuntimeOwnerMap.Binding => binding.port.token) equal))
    checked.tokensDistinct

def regroupIndex {roles state checked} (frame : @Frame roles state checked)
    (wanted : RuntimeOwnerMap.Map) (logical : Nat) : Nat :=
  recode checked.bindings wanted (dimensionAt frame.owners) logical

theorem regroup_volume {roles state checked} (frame : @Frame roles state checked) (wanted : RuntimeOwnerMap.Map)
    (retained : Retained frame.owners wanted) (permutation : wanted.Perm checked.bindings) :
    frame.code.dimension = (sparseProduct retained.codes).dimension :=
  (frame_volume frame).symm.trans
    ((volume_perm checked.bindings wanted (dimensionAt frame.owners) permutation.symm).trans
      (owner_volume frame.owners retained.codes permutation.subset))

theorem regroup_bound {roles state checked} (frame : @Frame roles state checked) (wanted : RuntimeOwnerMap.Map)
    (retained : Retained frame.owners wanted) (permutation : wanted.Perm checked.bindings)
    (logical : Nat) (bound : logical < frame.code.dimension) :
    regroupIndex frame wanted logical < (sparseProduct retained.codes).dimension := by
  have originalBound : logical < volume checked.bindings (dimensionAt frame.owners) := by
    rw [frame_volume frame]
    exact bound
  have result := recode_bound checked.bindings wanted (dimensionAt frame.owners) permutation.symm
    (cards_positive frame.owners) logical originalBound
  rw [owner_volume frame.owners retained.codes permutation.subset] at result
  exact result

/-- Both dense directions use the same exact cardinalities, including every
dimension-one owner, rather than a physical bit-width permutation. -/
theorem regroup_inverse {roles state checked} (frame : @Frame roles state checked) (wanted : RuntimeOwnerMap.Map)
    (permutation : wanted.Perm checked.bindings) (logical : Nat) (bound : logical < frame.code.dimension) :
    recode wanted checked.bindings (dimensionAt frame.owners) (regroupIndex frame wanted logical) = logical := by
  apply recode_inverse checked.bindings wanted (dimensionAt frame.owners) permutation.symm (frame_unique frame)
    (cards_positive frame.owners) logical
  rw [frame_volume frame]
  exact bound

theorem regroup_reverse {roles state checked} (frame : @Frame roles state checked) (wanted : RuntimeOwnerMap.Map)
    (retained : Retained frame.owners wanted) (permutation : wanted.Perm checked.bindings)
    (logical : Nat) (bound : logical < (sparseProduct retained.codes).dimension) :
    regroupIndex frame wanted (recode wanted checked.bindings (dimensionAt frame.owners) logical) = logical := by
  apply recode_inverse wanted checked.bindings (dimensionAt frame.owners) permutation
    (permutation.symm.nodup (frame_unique frame))
    (fun binding member => cards_positive frame.owners binding (permutation.mem_iff.mp member)) logical
  rw [owner_volume frame.owners retained.codes permutation.subset]
  exact bound

theorem regroup_coefficient {roles state checked} (frame : @Frame roles state checked) (wanted : RuntimeOwnerMap.Map)
    (retained : Retained frame.owners wanted) (permutation : wanted.Perm checked.bindings)
    (physical logical : Nat) (bound : logical < frame.code.dimension) :
    scalar (frame.embedding physical logical) =
      coefficients state.quantum.frame retained.codes physical (regroupIndex frame wanted logical) := by
  have originalBound : logical < volume checked.bindings (dimensionAt frame.owners) := by
    rw [frame_volume frame]
    exact bound
  have positive := cards_positive frame.owners
  have newBound := recode_bound checked.bindings wanted (dimensionAt frame.owners) permutation.symm positive logical originalBound
  have digits : ∀ binding ∈ wanted,
      decode checked.bindings (dimensionAt frame.owners) logical binding < dimensionAt frame.owners binding :=
    fun binding member => decode_bound checked.bindings _ logical positive originalBound binding (permutation.mem_iff.mp member)
  have indices : ∀ binding ∈ wanted,
      decode wanted (dimensionAt frame.owners) (regroupIndex frame wanted logical) binding =
        decode checked.bindings (dimensionAt frame.owners) logical binding :=
    decode_encode wanted _ _ digits
  have originalFactors := coefficients_factors frame.owners state.quantum.frame frame.owners physical logical
    (fun member => member) (frame_unique frame) originalBound
  have newFactors := coefficients_factors frame.owners state.quantum.frame retained.codes physical _
    permutation.subset (permutation.symm.nodup (frame_unique frame)) newBound
  calc
    _ = coefficients state.quantum.frame frame.owners physical logical := ordered_product_entry frame physical logical bound
    _ = _ := originalFactors
    _ = (wanted.map fun binding => factorAt state.quantum.frame frame.owners physical binding
        (decode checked.bindings (dimensionAt frame.owners) logical binding)).prod :=
      (permutation.symm.map (fun binding => factorAt state.quantum.frame frame.owners physical binding
        (decode checked.bindings (dimensionAt frame.owners) logical binding))).prod_eq
    _ = (wanted.map fun binding => factorAt state.quantum.frame frame.owners physical binding
        (decode wanted (dimensionAt frame.owners) (regroupIndex frame wanted logical) binding)).prod := by
      apply congrArg List.prod
      apply List.map_congr_left
      intro binding member
      rw [indices binding member]
    _ = _ := newFactors.symm

/-- The same global Raw coordinate is evaluated in the actual lazy reordered
code. Logical recoding preserves code padding and the entire complex scalar. -/
theorem regroup_sparse_entry {roles state checked} (frame : @Frame roles state checked) (wanted : RuntimeOwnerMap.Map)
    (retained : Retained frame.owners wanted) (permutation : wanted.Perm checked.bindings)
    (physical logical : Nat) (bound : logical < frame.code.dimension) :
    scalar (frame.embedding physical logical) = scalar (sparseEntry (sparseProduct retained.codes)
      (gather physical (forestAxes state.quantum.frame wanted)) (regroupIndex frame wanted logical)) := by
  have same := congrArg (fun coordinate : Option Nat =>
      if coordinate == some (gather physical (forestAxes state.quantum.frame wanted)) then Scalar.one else Scalar.zero)
    ((product_agrees retained.codes).labels (regroupIndex frame wanted logical))
  have lifted := product_coefficient state.quantum.frame retained.codes physical _
    (regroup_bound frame wanted retained permutation logical bound)
  exact (regroup_coefficient frame wanted retained permutation physical logical bound).trans
    (lifted.symm.trans (congrArg scalar same).symm)

/-- All original logical/reference amplitudes remain arbitrary; this keeps
their original summation order and does not reassociate bounded arithmetic. -/
theorem regroup_action {Reference : Type} {roles state checked} (frame : @Frame roles state checked)
    (wanted : RuntimeOwnerMap.Map) (retained : Retained frame.owners wanted) (permutation : wanted.Perm checked.bindings)
    (joint : Nat → Reference → ℂ) (physical : Nat) (reference : Reference) :
    referenceAction frame joint physical reference =
      ((List.range frame.code.dimension).map fun logical =>
        coefficients state.quantum.frame retained.codes physical (regroupIndex frame wanted logical)*joint logical reference).sum := by
  unfold referenceAction
  apply Qleisli.Exact.sum_map_congr
  intro logical member
  rw [regroup_coefficient frame wanted retained permutation physical logical (List.mem_range.mp member)]

/-- The actual selected/spectator order, original code receipts and interval
uniqueness proof instantiate the correspondence; no partition is supplied. -/
theorem literal_correspondence
    {dependencies program block start count inputs outputs roles frame selectorBits targetBits retained restricted
      beforeRoles afterRoles before after}
    (checked : @RuntimeLocalEvents.Literal dependencies program block start count inputs outputs roles frame selectorBits
      targetBits retained restricted beforeRoles afterRoles before after)
    (codes : Retained checked.inputCode.owners
      (checked.selection.selected ++ RuntimeSelectionPartition.complement before.bindings checked.selection.selected))
    (physical logical : Nat) (bound : logical < checked.inputCode.code.dimension) :
    let wanted := checked.selection.selected ++ RuntimeSelectionPartition.complement before.bindings checked.selection.selected
    regroupIndex checked.inputCode wanted logical < (sparseProduct codes.codes).dimension ∧
      recode wanted before.bindings (dimensionAt checked.inputCode.owners)
        (regroupIndex checked.inputCode wanted logical) = logical ∧
      scalar (checked.inputCode.embedding physical logical) = scalar (sparseEntry (sparseProduct codes.codes)
        (gather physical (forestAxes frame.interval.before.quantum.frame wanted))
        (regroupIndex checked.inputCode wanted logical)) := by
  obtain ⟨_tokens,_unique,_subset,_roles,_spectators,partition⟩ := RuntimeSelectionPartition.literal_partition checked
  exact ⟨regroup_bound checked.inputCode _ codes partition logical bound,
    regroup_inverse checked.inputCode _ partition logical bound,
    regroup_sparse_entry checked.inputCode _ codes partition physical logical bound⟩

#print axioms regroup_inverse
#print axioms regroup_reverse
#print axioms regroup_sparse_entry
#print axioms regroup_action
#print axioms literal_correspondence

end Qleisli.RuntimeForestRegroup
