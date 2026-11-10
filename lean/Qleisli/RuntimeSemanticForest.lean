import Qleisli.RuntimeNamedOutputOrder
import Qleisli.RuntimeStructuralLayoutEvidence

/-! Exact sparse reference frames for original source owners. Every owner
retains its independent layout and actual wires. Mixed-radix regrouping uses
the original logical cardinalities and arbitrary joint reference amplitudes.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeSemanticForest
open QleisliKernel QleisliKernel.Qirf
open Semantics.FiniteCarrier (Layout layout tensor singleton)
open Semantics.Finite (gather)
open RuntimeOwnerMap (Binding Map)
open RuntimeForestCode (Sparse forestBasis forestAxes sparseLayout sparseLayout_complete
  sparseLayout_reference sparseEntry embed tensor_agrees ofLayout_agrees)
open Qleisli.RuntimeStructuralLayoutEvidence (SemanticOwnerLayout)
open Qleisli.RuntimeForestOrderedProduct
  (ownerLayouts forest_from_layouts agrees_entry layout_tensor_coefficient)
open Qleisli.RuntimeForestProduct (layout_bounds gather_append gather_bound)
open Qleisli.RuntimeForestRegroup (sourceDimension)
open Qleisli.MixedRadix
open Qleisli.Semantics.Exact (scalar)

def Available (bindings : Map) : Prop :=
  ∀ binding ∈ bindings, Nonempty (SemanticOwnerLayout binding)

structure Frame (bindings : Map) where
  code : Sparse
  original : sparseLayout (forestBasis bindings) = some code
  available : Available bindings

/-- Use the independent layout for this binding's entire original basis. -/
def ownerLayout (binding : Binding) : Layout := (layout binding.owner.basis).getD singleton

def product (bindings : Map) : Layout := (bindings.map ownerLayout).foldr tensor singleton

theorem owner_layout {binding : Binding} (available : Nonempty (SemanticOwnerLayout binding)) :
    layout binding.owner.basis = some (ownerLayout binding) ∧
      binding.port.wires.length = (ownerLayout binding).bits := by
  obtain ⟨shape⟩ := available
  have same : ownerLayout binding = shape.layout := by simp [ownerLayout,shape.reference]
  rw [same]
  exact ⟨shape.reference,shape.wires⟩

theorem owner_reads (bindings : Map) (available : Available bindings) :
    ownerLayouts bindings = some (bindings.map ownerLayout) := by
  induction bindings with
  | nil => rfl
  | cons binding rest ih =>
    have head := (owner_layout (available binding List.mem_cons_self)).1
    have tail := ih (fun b member => available b (List.mem_cons_of_mem _ member))
    unfold ownerLayouts at tail ⊢
    simp only [List.mapM_cons,List.map_cons,head,tail,bind,Option.bind,pure]

theorem forest_read {bindings : Map} (available : Available bindings) :
    layout (forestBasis bindings) = some (product bindings) :=
  forest_from_layouts (owner_reads bindings available)

theorem frame_exists {bindings : Map} (available : Available bindings) :
    Nonempty (Frame bindings) := by
  obtain ⟨code,original,_⟩ := sparseLayout_complete _ _ (forest_read available)
  exact ⟨⟨code,original,available⟩⟩

def ofNative {roles state checked} (frame : @RuntimeForestCode.Frame roles state checked) :
    Frame checked.bindings :=
  ⟨frame.code,frame.original,fun binding member => by
    obtain ⟨code,_⟩ := RuntimeOwnerCodeReindex.lookup_exists frame.owners binding member
    exact ⟨⟨code.layout,code.reference.1,code.reference.2.1,code.reference.2.2⟩⟩⟩

noncomputable def action {bindings : Map} (frame : Frame bindings) (physicalFrame : List Nat)
    {Reference : Type} (joint : Nat → Reference → ℂ) (row : Nat) (reference : Reference) : ℂ :=
  ((List.range frame.code.dimension).map fun logical =>
    scalar (embed physicalFrame bindings frame.code row logical)*joint logical reference).sum

theorem ofNative_action {roles state checked Reference}
    (frame : @RuntimeForestCode.Frame roles state checked) (joint : Nat → Reference → ℂ)
    (row : Nat) (reference : Reference) :
    action (ofNative frame) state.quantum.frame joint row reference =
      Qleisli.RuntimeForestProduct.referenceAction frame joint row reference := rfl

theorem product_agrees {bindings : Map} (frame : Frame bindings) :
    RuntimeForestCode.Agrees frame.code (product bindings) := by
  obtain ⟨actual,found,related⟩ := sparseLayout_reference _ _ frame.original
  have same := Option.some.inj (found.symm.trans (forest_read frame.available))
  exact same ▸ related

private theorem card_eq (original : Map) (binding : Binding) (member : binding ∈ original)
    (available : Nonempty (SemanticOwnerLayout binding)) :
    sourceDimension original binding = (ownerLayout binding).labels.length := by
  simp only [sourceDimension,if_pos member,Semantics.FiniteCarrier.dimension,
    (owner_layout available).1,Option.map_some,Option.getD_some]

private theorem cards_positive {original : Map} (available : Available original)
    (binding : Binding) (member : binding ∈ original) :
    0 < sourceDimension original binding := by
  rw [card_eq original binding member (available binding member)]
  exact (layout_bounds _ _ (owner_layout (available binding member)).1).1

private theorem product_volume {original bindings : Map} (available : Available original)
    (subset : bindings ⊆ original) :
    (product bindings).labels.length = volume bindings (sourceDimension original) := by
  induction bindings with
  | nil => rfl
  | cons binding rest ih =>
    have head := card_eq original binding (subset List.mem_cons_self) (available binding (subset List.mem_cons_self))
    have tail := ih (fun {_} member => subset (List.mem_cons_of_mem _ member))
    have size := (tensor_agrees (ofLayout_agrees (ownerLayout binding)) (ofLayout_agrees (product rest))).dimension
    change (ownerLayout binding).labels.length * (product rest).labels.length =
      (tensor (ownerLayout binding) (product rest)).labels.length at size
    change (tensor (ownerLayout binding) (product rest)).labels.length =
      sourceDimension original binding * volume rest (sourceDimension original)
    rw [← size,head,tail]

private noncomputable def factor (physicalFrame : List Nat) (row : Nat) (binding : Binding) (digit : Nat) : ℂ :=
  scalar (sparseEntry (.ofLayout (ownerLayout binding))
    (gather row (binding.port.wires.map physicalFrame.idxOf)) digit)

private theorem product_entry {original bindings : Map} (available : Available original)
    (subset : bindings ⊆ original) (unique : bindings.Nodup) (physicalFrame : List Nat)
    (row logical : Nat) (bound : logical < volume bindings (sourceDimension original)) :
    scalar (sparseEntry (.ofLayout (product bindings))
      (gather row (forestAxes physicalFrame bindings)) logical) =
      (bindings.map fun binding => factor physicalFrame row binding
        (decode bindings (sourceDimension original) logical binding)).prod := by
  induction bindings generalizing logical with
  | nil =>
    have zero : logical = 0 := by change logical < 1 at bound; omega
    subst logical
    simp [product,forestAxes,gather,sparseEntry,Sparse.ofLayout,Semantics.FiniteCarrier.singleton,Qleisli.Exact.scalar_one_meaning]
  | cons binding rest ih =>
    let cards := sourceDimension original
    have head := available binding (subset List.mem_cons_self)
    have width := (owner_layout head).2
    have card := card_eq original binding (subset List.mem_cons_self) head
    have layoutBound := layout_bounds _ _ (owner_layout head).1
    have small : gather row (binding.port.wires.map physicalFrame.idxOf) < 2^(ownerLayout binding).bits := by
      simpa only [List.length_map,width] using gather_bound row (binding.port.wires.map physicalFrame.idxOf)
    have separate := List.nodup_cons.mp unique
    have tailBound : logical / cards binding < volume rest cards := Nat.div_lt_of_lt_mul bound
    have tail := ih (fun {_} member => subset (List.mem_cons_of_mem _ member)) separate.2 _ tailBound
    have axes : forestAxes physicalFrame (binding::rest) =
        binding.port.wires.map physicalFrame.idxOf ++ forestAxes physicalFrame rest := by
      simp only [forestAxes,List.flatMap_cons,List.map_append]
    change scalar (sparseEntry (.ofLayout (tensor (ownerLayout binding) (product rest)))
        (gather row (forestAxes physicalFrame (binding::rest))) logical) = _
    rw [axes,gather_append,List.length_map,width,layout_tensor_coefficient _ _ layoutBound _ _ _ small,
      ← card,tail]
    simp only [List.map_cons,List.prod_cons,decode_head]
    apply congrArg (fun value => factor physicalFrame row binding (logical % cards binding) * value)
    apply congrArg List.prod
    apply List.map_congr_left
    intro other member
    have different : binding ≠ other := fun same => separate.1 (same.symm ▸ member)
    rw [decode_cons,if_neg different]

theorem frame_dimension {bindings : Map} (frame : Frame bindings) :
    frame.code.dimension = volume bindings (sourceDimension bindings) :=
  (product_agrees frame).dimension.trans (product_volume frame.available (fun {_} member => member))

/-- A nonzero coefficient fixes the physical label of the exact original
owner. Its logical digit is independent of the label, including for padding. -/
theorem owner_support {bindings : Map} (frame : Frame bindings) (unique : bindings.Nodup)
    (owner : Binding) (member : owner ∈ bindings) (physicalFrame : List Nat)
    (row logical : Nat) (bound : logical < frame.code.dimension)
    (nonzero : scalar (embed physicalFrame bindings frame.code row logical) ≠ 0) :
    let digit := decode bindings (sourceDimension bindings) logical owner
    digit < (ownerLayout owner).labels.length ∧
      (ownerLayout owner).labels[digit]? = some (gather row (owner.port.wires.map physicalFrame.idxOf)) := by
  intro digit
  have inside : logical < volume bindings (sourceDimension bindings) := frame_dimension frame ▸ bound
  have small := decode_bound bindings (sourceDimension bindings) logical (cards_positive frame.available)
    inside owner member
  rw [card_eq bindings owner member (frame.available owner member)] at small
  refine ⟨small,?_⟩
  by_contra missing
  apply nonzero
  unfold embed
  rw [agrees_entry (product_agrees frame),product_entry frame.available (fun {_} h => h) unique
    physicalFrame row logical inside]
  have zero : factor physicalFrame row owner digit = 0 := by
    unfold factor sparseEntry
    change scalar (if (ownerLayout owner).labels[digit]? == some (gather row (owner.port.wires.map physicalFrame.idxOf))
      then _ else _) = 0
    simp [missing,Qleisli.Exact.scalar_zero_meaning]
  exact List.prod_eq_zero (List.mem_map.mpr ⟨owner,member,zero⟩)

/-- Reorder a complete reference frame in the original owner coordinates. -/
theorem regroup_action {before after : Map} (input : Frame before) (output : Frame after)
    (permutation : before.Perm after) (unique : before.Nodup) (physicalFrame : List Nat)
    {Reference : Type} (joint : Nat → Reference → ℂ) (row : Nat) (reference : Reference) :
    action input physicalFrame joint row reference =
      action output physicalFrame
        (fun logical ref => joint (recode after before (sourceDimension before) logical) ref) row reference := by
  let cards := sourceDimension before
  let forward := recode before after cards
  let backward := recode after before cards
  have inSize : input.code.dimension = volume before cards :=
    (product_agrees input).dimension.trans (product_volume input.available (fun {_} member => member))
  have outSize : output.code.dimension = volume after cards :=
    (product_agrees output).dimension.trans (product_volume input.available permutation.symm.subset)
  have volumeSame := volume_perm before after cards permutation
  have positive := cards_positive input.available
  have outputPositive : ∀ b ∈ after,0 < cards b := fun b member => positive b (permutation.symm.subset member)
  have forwardBound (value : Nat) (small : value < volume before cards) :
      forward value < volume after cards := recode_bound _ _ _ permutation positive value small
  have backBound (value : Nat) (small : value < volume after cards) :
      backward value < volume before cards := recode_bound _ _ _ permutation.symm outputPositive value small
  have left (value : Nat) (small : value < volume before cards) : backward (forward value) = value :=
    recode_inverse _ _ _ permutation unique positive value small
  have right (value : Nat) (small : value < volume after cards) : forward (backward value) = value :=
    recode_inverse _ _ _ permutation.symm (permutation.nodup unique) outputPositive value small
  have indices := Qleisli.RuntimeNamedOutputOrder.bijection_range (volume before cards) forward backward
    (fun i small => volumeSame.symm ▸ forwardBound i small) (fun i small => backBound i (volumeSame ▸ small))
    left (fun i small => right i (volumeSame ▸ small))
  let term := fun logical => scalar (embed physicalFrame after output.code row logical) * joint (backward logical) reference
  unfold action
  rw [inSize,outSize,← volumeSame]
  calc
    _ = ((List.range (volume before cards)).map fun logical => term (forward logical)).sum := by
      apply Qleisli.Exact.sum_map_congr
      intro logical member
      have small := List.mem_range.mp member
      dsimp only [term]
      rw [left logical small]
      apply congrArg (fun coefficient => coefficient * joint logical reference)
      unfold embed
      rw [agrees_entry (product_agrees input),agrees_entry (product_agrees output)]
      rw [product_entry input.available (fun {_} present => present) unique physicalFrame row logical small,
        product_entry input.available permutation.symm.subset (permutation.nodup unique) physicalFrame row _
          (forwardBound logical small)]
      rw [(permutation.map (fun binding => factor physicalFrame row binding (decode before cards logical binding))).prod_eq]
      apply congrArg List.prod
      apply List.map_congr_left
      intro binding present
      have digits (b : Binding) (member : b ∈ after) : decode before cards logical b < cards b :=
        decode_bound before cards logical positive small b (permutation.symm.subset member)
      rw [show decode after cards (forward logical) binding = decode before cards logical binding from
        decode_encode after cards (decode before cards logical) digits binding present]
    _ = ((List.range (volume before cards)).map term).sum := by
      simpa only [List.map_map,Function.comp_def] using (indices.map term).sum_eq

#print axioms owner_support
#print axioms regroup_action
end Qleisli.RuntimeSemanticForest
