import Qleisli.RuntimeSemanticForest
import Qleisli.RuntimeNamedBlockEncoding
import Qleisli.RuntimeNamedBlockSpectators
import Qleisli.RuntimeNamedCarrierEncoding

/-! The exact sparse caller encoding decomposes around the entire selected
owner block. Its spectator fibre retains arbitrary correlated amplitudes.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeSparseBlockEncoding
open QleisliKernel QleisliKernel.Qirf
open Semantics.Finite (gather scatter)
open Semantics.FiniteCarrier (layout tensor)
open RuntimeOwnerMap (Binding Map)
open RuntimeForestCode (forestBasis forestAxes carrierOwners sparseEntry embed ofLayout_agrees tensor_agrees)
open Qleisli.RuntimeSemanticForest
  (Available Frame action ownerLayout owner_layout owner_reads product forest_read frame_exists product_agrees
    regroup_action ofNative ofNative_action)
open Qleisli.RuntimeForestOrderedProduct (forest_append agrees_entry layout_tensor_coefficient)
open Qleisli.RuntimeForestProduct (layout_bounds gather_append gather_bound)
open Qleisli.RuntimeNamedBlockEncoding (group_sum)
open Qleisli.RuntimeNamedHeadCoefficients (fibre)
open Qleisli.RuntimeForestRegroup (sourceDimension)
open Qleisli.MixedRadix (recode)
open Qleisli.Semantics.Exact (scalar)

noncomputable def coefficient (bindings : Map) (physicalFrame : List Nat)
    (physical logical : Nat) : ℂ :=
  scalar (sparseEntry (.ofLayout (product bindings)) (gather physical (forestAxes physicalFrame bindings)) logical)

theorem product_width {bindings : Map} (available : Available bindings) :
    (product bindings).bits = (bindings.flatMap (·.port.wires)).length := by
  induction bindings with
  | nil => rfl
  | cons binding rest ih =>
    have head := (owner_layout (available binding List.mem_cons_self)).2
    have tail := ih (fun b member => available b (List.mem_cons_of_mem _ member))
    change (ownerLayout binding).bits + (product rest).bits =
      (binding.port.wires ++ rest.flatMap (·.port.wires)).length
    rw [List.length_append,← head,tail]

theorem product_append {selected spectators : Map} (available : Available (selected++spectators)) :
    product (selected++spectators) = tensor (product selected) (product spectators) := by
  have first := owner_reads selected (fun b member => available b (List.mem_append_left _ member))
  have second := owner_reads spectators (fun b member => available b (List.mem_append_right _ member))
  exact Option.some.inj ((forest_read available).symm.trans (forest_append first second))

/-- Factor the actual ordered sparse code before summing its correlated joint
amplitudes. Selection may contain multiple or zero-width original owners. -/
theorem block_action {selected spectators : Map} (frame : Frame (selected++spectators))
    (physicalFrame : List Nat) {Reference : Type} (joint : Nat → Reference → ℂ)
    (physical : Nat) (reference : Reference) :
    action frame physicalFrame joint physical reference =
      ((List.range (product selected).labels.length).map fun digit =>
        coefficient selected physicalFrame physical digit *
          fibre (product selected).labels.length (product spectators).labels.length
            (coefficient spectators physicalFrame physical) joint digit reference).sum := by
  let low := product selected
  let high := product spectators
  let selectedAxes := forestAxes physicalFrame selected
  let spectatorAxes := forestAxes physicalFrame spectators
  have available : Available selected := fun b member => frame.available b (List.mem_append_left _ member)
  have valid := layout_bounds _ _ (forest_read available)
  have width : selectedAxes.length = low.bits := by
    simpa only [selectedAxes,forestAxes,List.length_map,low] using (product_width available).symm
  have small : gather physical selectedAxes < 2^low.bits := by
    rw [← width]
    exact gather_bound _ _
  have productRead := product_agrees frame
  rw [product_append frame.available] at productRead
  have dimension : frame.code.dimension = low.labels.length*high.labels.length :=
    productRead.dimension.trans (tensor_agrees (ofLayout_agrees low) (ofLayout_agrees high)).dimension.symm
  have axes : forestAxes physicalFrame (selected++spectators) = selectedAxes++spectatorAxes := by
    simp only [selectedAxes,spectatorAxes,forestAxes,List.flatMap_append,List.map_append]
  unfold action
  rw [dimension,← group_sum _ _ valid.1]
  apply Qleisli.Exact.sum_map_congr
  intro logical _
  unfold embed
  rw [agrees_entry productRead,axes,gather_append,width,
    layout_tensor_coefficient low high valid _ _ _ small]
  rfl

theorem coefficient_scatter (bindings : Map) (physicalFrame : List Nat) (selectedAxes : List Nat)
    (disjoint : (forestAxes physicalFrame bindings).Disjoint selectedAxes)
    (physical replacement logical : Nat) :
    coefficient bindings physicalFrame (scatter physical selectedAxes replacement) logical =
      coefficient bindings physicalFrame physical logical := by
  unfold coefficient
  rw [Qleisli.RuntimeTargetScatter.gather_disjoint physical replacement _ _ disjoint]

/-- Transport complete layouts across an exact ordered carrier alias. -/
theorem available_carriers {original mapped : Map}
    (same : carrierOwners mapped = carrierOwners original) (available : Available original) :
    Available mapped := by
  intro binding member
  have carrier : (⟨binding.port,binding.owner.basis⟩ : Semantics.CarrierInterface.Owner) ∈ carrierOwners original :=
    same ▸ List.mem_map_of_mem member
  obtain ⟨source,present,matching⟩ := List.mem_map.mp carrier
  obtain ⟨layout⟩ := available source present
  have basis : source.owner.basis = binding.owner.basis :=
    congrArg Semantics.CarrierInterface.Owner.basis matching
  have bits : source.port.bits = binding.port.bits :=
    congrArg (fun owner : Semantics.CarrierInterface.Owner => owner.port.bits) matching
  have wires : source.port.wires.length = binding.port.wires.length :=
    congrArg (fun owner : Semantics.CarrierInterface.Owner => owner.port.wires.length) matching
  exact ⟨⟨layout.layout,basis ▸ layout.reference,bits ▸ layout.bits,wires ▸ layout.wires⟩⟩

theorem product_carriers {original mapped : Map}
    (same : carrierOwners mapped = carrierOwners original)
    (originalAvailable : Available original) (mappedAvailable : Available mapped) :
    product mapped = product original := by
  have basis : forestBasis mapped = forestBasis original := congrArg Semantics.CarrierInterface.forest same
  have read := forest_read mappedAvailable
  rw [basis] at read
  exact Option.some.inj (read.symm.trans (forest_read originalAvailable))

/-- Local and parent selected codes have the same coefficients because their
ordered full carriers coincide and the child frame uses the original wires. -/
theorem child_encoding {childBindings selected}
    (child : Frame childBindings) (available : Available selected)
    (same : carrierOwners childBindings = carrierOwners selected)
    (childFrame : List Nat) (localFrame : childFrame = selected.flatMap (·.port.wires))
    (unique : childFrame.Nodup) (parentFrame : List Nat) {Reference : Type}
    (joint : Nat → Reference → ℂ) (physical : Nat) (reference : Reference) :
    action child childFrame joint (gather physical (forestAxes parentFrame selected)) reference =
      ((List.range (product selected).labels.length).map fun digit =>
        coefficient selected parentFrame physical digit * joint digit reference).sum := by
  have sameLayout := product_carriers same available child.available
  have wires := Qleisli.RuntimeNamedCarrierEncoding.carrier_wires same
  have axes : forestAxes childFrame childBindings = List.range childFrame.length := by
    unfold forestAxes
    rw [wires,← localFrame]
    exact RuntimeNamedCallerAction.self_indices _ unique
  have bounded : gather physical (forestAxes parentFrame selected) < 2^childFrame.length := by
    simpa only [forestAxes,List.length_map,localFrame] using gather_bound physical (forestAxes parentFrame selected)
  have agrees := product_agrees child
  rw [sameLayout] at agrees
  unfold action
  rw [agrees.dimension]
  apply Qleisli.Exact.sum_map_congr
  intro logical _
  change scalar (sparseEntry child.code
      (gather (gather physical (forestAxes parentFrame selected)) (forestAxes childFrame childBindings))
      logical) * joint logical reference = _
  rw [axes,Raw.Sector.gather_identity _ _ bounded,agrees_entry agrees]
  rfl

/-- Lift the genuine selected child input to the original complete caller,
with its unmodified spectator encoding and independent source coordinates. -/
theorem sparse_caller_input {parentRoles parentState} (checked : RuntimeOwnerMap.Checked parentRoles parentState)
    (input : Frame checked.bindings) (valid : Raw.stateValid parentState.quantum = true)
    {selected spectators : Map} (permutation : (selected++spectators).Perm checked.bindings)
    {childBindings} (child : Frame childBindings)
    (same : carrierOwners childBindings = carrierOwners selected)
    (childFrame : List Nat) (localFrame : childFrame = selected.flatMap (·.port.wires))
    (unique : childFrame.Nodup) :
    ∀ {Reference : Type} (joint : Nat → Reference → ℂ) physical reference,
      action input parentState.quantum.frame joint physical reference =
        action child childFrame
          (fibre (product selected).labels.length (product spectators).labels.length
            (coefficient spectators parentState.quantum.frame
              (scatter physical (forestAxes parentState.quantum.frame selected) 0))
            (fun logical column => joint (recode (selected++spectators)
              checked.bindings (sourceDimension checked.bindings) logical) column))
          (gather physical (forestAxes parentState.quantum.frame selected)) reference := by
  have distinct : checked.bindings.Nodup := List.Pairwise.of_map (fun binding : Binding => binding.port.token)
    (fun _ _ different equal => different (congrArg (fun binding : Binding => binding.port.token) equal))
    checked.tokensDistinct
  obtain ⟨ordered⟩ := frame_exists (fun b member => input.available b (permutation.subset member))
  have available : Available selected := fun b member => ordered.available b (List.mem_append_left _ member)
  have disjoint := Qleisli.RuntimeNamedBlockSpectators.partition_axes_disjoint checked valid selected spectators permutation
  intro Reference joint physical reference
  rw [regroup_action input ordered permutation.symm distinct,block_action ordered]
  rw [child_encoding child available same childFrame localFrame unique]
  apply Qleisli.Exact.sum_map_congr
  intro digit _
  unfold fibre
  simp only [coefficient_scatter spectators _ _ disjoint]

/-- The retained native code is the same sparse representation used for a
general child's input. -/
theorem caller_input {parentRoles parentState} (checked : RuntimeOwnerMap.Checked parentRoles parentState)
    (input : Frame checked.bindings) (valid : Raw.stateValid parentState.quantum = true)
    {selected spectators : Map} (permutation : (selected++spectators).Perm checked.bindings)
    {childRoles childState childChecked} (child : @RuntimeForestCode.Frame childRoles childState childChecked)
    (same : carrierOwners childChecked.bindings = carrierOwners selected)
    (localFrame : childState.quantum.frame = selected.flatMap (·.port.wires))
    (unique : childState.quantum.frame.Nodup)
    {Reference : Type} (joint : Nat → Reference → ℂ) physical reference :
    action input parentState.quantum.frame joint physical reference =
      RuntimeNamedSelectionAction.encodedParent child (forestAxes parentState.quantum.frame selected)
        (fun digit environment ref =>
          fibre (product selected).labels.length (product spectators).labels.length
            (coefficient spectators parentState.quantum.frame environment)
            (fun logical column => joint (recode (selected++spectators)
              checked.bindings (sourceDimension checked.bindings) logical) column) digit ref) physical reference := by
  unfold RuntimeNamedSelectionAction.encodedParent
  rw [← ofNative_action]
  exact sparse_caller_input checked input valid permutation (ofNative child) same _ localFrame unique joint physical reference

/-- Assemble a selected result for each spectator coordinate. Modulo and
quotient use the original selected block's logical cardinality. -/
noncomputable def blockJoint {Reference : Type} (low : Nat) (joint : Nat → Nat → Reference → ℂ)
    (logical : Nat) (reference : Reference) : ℂ :=
  joint (logical%low) (logical/low) reference

theorem block_result {selected spectators : Map} (frame : Frame (selected++spectators))
    (physicalFrame : List Nat) {Reference : Type} (joint : Nat → Nat → Reference → ℂ)
    (physical : Nat) (reference : Reference) :
    action frame physicalFrame (blockJoint (product selected).labels.length joint) physical reference =
      ((List.range (product selected).labels.length).map fun digit =>
        coefficient selected physicalFrame physical digit *
          ((List.range (product spectators).labels.length).map fun high =>
            coefficient spectators physicalFrame physical high * joint digit high reference).sum).sum := by
  have available : Available selected := fun b member => frame.available b (List.mem_append_left _ member)
  have positive := (layout_bounds _ _ (forest_read available)).1
  rw [block_action frame]
  apply Qleisli.Exact.sum_map_congr
  intro digit member
  have bounded := List.mem_range.mp member
  unfold fibre blockJoint
  simp only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt bounded,
    Nat.add_mul_div_left _ _ positive,Nat.div_eq_of_lt bounded,Nat.zero_add]

private theorem full_block_coefficient (selected : Map) (physicalFrame : List Nat)
    (full : (product selected).labels = List.range (2^(forestAxes physicalFrame selected).length))
    (physical digit : Nat) (bound : digit < 2^(forestAxes physicalFrame selected).length) :
    coefficient selected physicalFrame physical digit =
      if gather physical (forestAxes physicalFrame selected) = digit then 1 else 0 := by
  unfold coefficient sparseEntry
  simp only [RuntimeForestCode.Sparse.ofLayout, full, List.getElem?_range bound,
    beq_iff_eq, Option.some.injEq]
  by_cases same : gather physical (forestAxes physicalFrame selected) = digit
  · simp [same, Qleisli.Exact.scalar_one_meaning]
  · have different := Ne.symm same
    simp [same, different, Qleisli.Exact.scalar_zero_meaning]

private theorem gather_repartition (physical : Nat) {before after : List Nat}
    (wires : before.Perm after) (unique : after.Nodup) :
    gather (scatter 0 after (gather physical after)) before = gather physical before := by
  unfold gather
  apply congrArg List.sum
  apply List.map_congr_left
  intro entry member
  have inBefore : entry.1 ∈ before := List.fst_mem_of_mem_zipIdx member
  obtain ⟨index, bound, same⟩ := List.getElem_of_mem (wires.mem_iff.mp inBefore)
  change Semantics.Finite.bit (scatter 0 after (gather physical after)) entry.1 * 2^entry.2 =
    Semantics.Finite.bit physical entry.1 * 2^entry.2
  have transported := RuntimeScatterTransport.scatter_at 0 (gather physical after) after unique index bound
  rw [RuntimeScatterTransport.gather_at _ after index bound, same] at transported
  rw [transported]

/-- Repartition an ordered full register block with the same physical wires.
The prior digit is read in the old order, while the spectator digit and
arbitrary reference amplitude pass through the same joint operator. -/
theorem full_block_repartition {before after spectators : Map}
    (input : Frame (before ++ spectators)) (output : Frame (after ++ spectators))
    (physicalFrame : List Nat)
    (wires : (forestAxes physicalFrame before).Perm (forestAxes physicalFrame after))
    (unique : (forestAxes physicalFrame after).Nodup)
    (inputFull : (product before).labels = List.range (2^(forestAxes physicalFrame before).length))
    (outputFull : (product after).labels = List.range (2^(forestAxes physicalFrame after).length))
    {Reference : Type} (joint : Nat → Nat → Reference → ℂ) (physical : Nat) (reference : Reference) :
    action input physicalFrame (blockJoint (product before).labels.length joint) physical reference =
      action output physicalFrame (blockJoint (product after).labels.length
        (fun digit spectator ref =>
          joint (gather (scatter 0 (forestAxes physicalFrame after) digit)
            (forestAxes physicalFrame before)) spectator ref)) physical reference := by
  have eval (selected : Map) (full : (product selected).labels =
      List.range (2^(forestAxes physicalFrame selected).length))
      (f : Nat → ℂ) :
      ((List.range (product selected).labels.length).map fun digit =>
        coefficient selected physicalFrame physical digit * f digit).sum =
        f (gather physical (forestAxes physicalFrame selected)) := by
    rw [full, List.length_range]
    calc
      _ = ((List.range (2^(forestAxes physicalFrame selected).length)).map fun digit =>
          if gather physical (forestAxes physicalFrame selected) = digit then f digit else 0).sum := by
        apply Qleisli.Exact.sum_map_congr
        intro digit member
        rw [full_block_coefficient selected physicalFrame full physical digit (List.mem_range.mp member)]
        split <;> simp
      _ = _ := Qleisli.Exact.range_delta_sum _ _ _ (gather_bound _ _)
  rw [block_result input, block_result output, eval _ inputFull, eval _ outputFull]
  rw [gather_repartition physical wires unique]

#print axioms block_action
#print axioms full_block_repartition
#print axioms sparse_caller_input
#print axioms caller_input
end Qleisli.RuntimeSparseBlockEncoding
