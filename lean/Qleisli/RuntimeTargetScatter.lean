import Qleisli.RuntimeTargetDigit
import Qleisli.RuntimeOwnerTransitionAction
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Basic
import Mathlib.Algebra.BigOperators.Ring.List

/-! Physical target scatter and the same source target's logical digit.
Geometry is derived from the authentic interval's Raw validity and complete
owner map. Every retained nominal and zero-width spectator remains present.
The coefficient and action statements use only total complex arithmetic; no
joined matrix, bounded-availability converse or new acceptance gate is built.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeTargetScatter
open QleisliKernel QleisliKernel.Qirf
open QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite
open RuntimeOwnerMap (Binding Map)
open RuntimeForestCode RuntimeOwnerCodeReindex
open Qleisli.Semantics.Exact Qleisli.RuntimeForestProduct
open Qleisli.MixedRadix Qleisli.RuntimeForestRegroup Qleisli.RuntimeForestOrderedProduct

/-- The complete returned forest uses distinct real Raw axes. This is derived
from the same interval read; separate empty owners are not identified by it. -/
theorem output_axes_unique {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles) :
    (forestAxes frame.interval.after.quantum.frame source.transport.after.bindings).Nodup := by
  obtain ⟨work,left,ran⟩ := frame.interval.intervalRead
  have valid := Raw.Ownership.valid _ (Raw.Observation.checkOps_invariants _ _ _ _ _ work left ran).1
  have ports := List.Perm.flatMap_right (fun port : Semantics.Raw.Port => port.wires)
    source.transport.after.complete
  have unique : (source.transport.after.bindings.flatMap (fun binding => binding.port.wires)).Nodup := by
    simpa only [List.flatMap_map] using ports.symm.nodup valid.exclusive
  have covered (wire : Nat) (member : wire ∈ source.transport.after.bindings.flatMap (fun binding => binding.port.wires)) :
      wire ∈ frame.interval.after.quantum.frame :=
    valid.covered wire (ports.mem_iff.mp (by simpa only [List.flatMap_map] using member))
  unfold forestAxes
  exact List.Nodup.map_on (fun wire member _ _ equal => (List.idxOf_inj (covered wire member)).mp equal) unique

/-- Each untouched owner has axes disjoint from the authentic target owner.
Original binding identity, rather than a width comparison, selects the owner. -/
theorem output_owner_axes_disjoint {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles)
    (first second : Binding) (firstMember : first ∈ source.transport.after.bindings)
    (secondMember : second ∈ source.transport.after.bindings) (different : first ≠ second) :
    (first.port.wires.map frame.interval.after.quantum.frame.idxOf).Disjoint
      (second.port.wires.map frame.interval.after.quantum.frame.idxOf) := by
  have unique : (source.transport.after.bindings.flatMap
      (fun binding => binding.port.wires.map frame.interval.after.quantum.frame.idxOf)).Nodup := by
    simpa only [forestAxes,List.map_flatMap] using output_axes_unique frame source
  exact List.Pairwise.forall (fun _ _ disjoint => disjoint.symm)
    (List.nodup_flatMap.mp unique).2 firstMember secondMember different

theorem gather_disjoint (physical replacement : Nat) (selected untouched : List Nat)
    (disjoint : untouched.Disjoint selected) :
    gather (scatter physical selected replacement) untouched = gather physical untouched := by
  unfold gather
  apply congrArg List.sum
  apply List.map_congr_left
  intro pair member
  have axisMember : pair.1 ∈ untouched := by
    have projected : pair.1 ∈ untouched.zipIdx.map (fun pair : Nat × Nat => pair.1) :=
      List.mem_map.mpr ⟨pair,member,rfl⟩
    simpa only [List.zipIdx_map_fst] using projected
  have outside := List.disjoint_left.mp disjoint axisMember
  rcases pair with ⟨axis,place⟩
  change bit (scatter physical selected replacement) axis * 2 ^ place = bit physical axis * 2 ^ place
  rw [RuntimeScatterTransport.scatter_outside physical replacement axis selected outside]

private theorem bit_layout {binding} (actual : OwnerCode binding) (basis : binding.owner.basis = [.bit]) :
    actual.layout = (⟨1,[0,1]⟩ : Semantics.FiniteCarrier.Layout) := by
  have original := actual.reference.1
  rw [basis] at original
  change some (⟨1,[0,1]⟩ : Semantics.FiniteCarrier.Layout) = some actual.layout at original
  exact (Option.some.inj original).symm

private theorem bit_delta {binding} (actual : OwnerCode binding) (basis : binding.owner.basis = [.bit])
    (row col : Nat) (rowBound : row < 2) (colBound : col < 2) :
    entry (Semantics.FiniteCarrier.encoding actual.layout) row col = if row = col then 1 else 0 := by
  rw [bit_layout actual basis]
  have original : QleisliKernel.Exact.Matrix.identity 2 =
      .ok (Semantics.FiniteCarrier.encoding ⟨1,[0,1]⟩) := rfl
  exact (Qleisli.Exact.identity_meaning _ _ original).2.2.2 row col rowBound colBound

private theorem gather_one (physical axis : Nat) : gather physical [axis] = bit physical axis := by
  simp [gather]

private theorem gather_scatter_one (physical replacement : Nat) (axes : List Nat)
    (length : axes.length = 1) (small : replacement < 2) :
    gather (scatter physical axes replacement) axes = replacement := by
  cases axes with
  | nil => simp at length
  | cons axis rest =>
    cases rest with
    | nil =>
      rw [gather_one]
      have actual := RuntimeScatterTransport.scatter_at physical replacement [axis] (by simp) 0 (by simp)
      have low : bit replacement 0 = replacement := by simp [bit,Nat.mod_eq_of_lt small]
      simpa only [List.getElem_cons_zero,low] using actual
    | cons second rest =>
      simp only [List.length_cons] at length
      omega

/-- Flipping the actual returned Bit wire flips exactly the same original
logical target digit in every sparse coefficient. Nominal spectator factors
and separate empty-owner factors are retained in their original order. -/
theorem target_flip_entry
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {inputCode outputCode}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (selectorBasis : selector.basis = [.bit]) (targetBasis : target.basis = [.bit])
    {selectorBits targetBits retained restricted}
    (literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
      codes.owners.before codes.owners.transport.after)
    (physical logical : Nat) (bound : logical < literal.outputCode.code.dimension) :
    let targetBinding := codes.owners.returned.second
    let axes := targetBinding.port.wires.map frame.interval.after.quantum.frame.idxOf
    let digit := decode codes.owners.transport.after.bindings (dimensionAt literal.outputCode.owners) logical targetBinding
    scalar (literal.outputCode.embedding (scatter physical axes (1-gather physical axes)) logical) =
      scalar (literal.outputCode.embedding physical (RuntimeTargetDigit.update literal.outputCode targetBinding logical (1-digit))) := by
  let output := literal.outputCode
  let order := codes.owners.transport.after.bindings
  let targetBinding := codes.owners.returned.second
  let axes := targetBinding.port.wires.map frame.interval.after.quantum.frame.idxOf
  let cards := dimensionAt output.owners
  let digit := decode order cards logical targetBinding
  let flipped := RuntimeTargetDigit.update output targetBinding logical (1-digit)
  have selected := RuntimeSelectionPartition.order_values _ _ _ codes.owners.returned.ordered
  have member : targetBinding ∈ order := selected.1 (by simp [targetBinding])
  have sameOwners : codes.owners.returned.first.owner = selector ∧ targetBinding.owner = target := by
    simpa only [List.map_cons,List.map_nil,List.cons.injEq,and_true] using selected.2
  have basis : targetBinding.owner.basis = [.bit] := by rw [sameOwners.2,targetBasis]
  obtain ⟨actual,_lookup⟩ := lookup_exists output.owners targetBinding member
  have actualLayout := bit_layout actual basis
  have card : cards targetBinding = 2 := by
    change dimensionAt output.owners targetBinding = 2
    rw [dimensionAt_eq output.owners targetBinding member actual,actualLayout]
    rfl
  have length : axes.length = 1 := by
    have shape := actual.reference.2.2
    rw [actualLayout] at shape
    simpa only [axes,List.length_map] using shape
  have rowBound : gather physical axes < 2 := by simpa only [length] using gather_bound physical axes
  have unique : order.Nodup :=
    List.Pairwise.of_map (fun binding : Binding => binding.port.token)
      (fun _ _ different same => different (congrArg (fun binding : Binding => binding.port.token) same))
      codes.owners.transport.after.tokensDistinct
  have logicalBound : logical < volume order cards := by rw [frame_volume output]; exact bound
  have digitBound : digit < 2 := by
    rw [← card]
    exact decode_bound order cards logical (cards_positive output.owners) logicalBound targetBinding member
  have small : 1-digit < 2 := by omega
  have updated := RuntimeTargetDigit.source_target_update frame codes selectorBasis targetBasis literal logical (1-digit) bound small
  have flippedBound : flipped < output.code.dimension := updated.1
  have flippedVolume : flipped < volume order cards := by rw [frame_volume output]; exact flippedBound
  have originalFactors := coefficients_factors output.owners frame.interval.after.quantum.frame output.owners
    (scatter physical axes (1-gather physical axes)) logical (fun {_} present => present) unique logicalBound
  have flippedFactors := coefficients_factors output.owners frame.interval.after.quantum.frame output.owners physical
    flipped (fun {_} present => present) unique flippedVolume
  calc
    _ = coefficients frame.interval.after.quantum.frame output.owners
        (scatter physical axes (1-gather physical axes)) logical :=
      ordered_product_entry output _ logical bound
    _ = _ := originalFactors
    _ = (order.map fun binding => factorAt frame.interval.after.quantum.frame output.owners physical binding
        (decode order cards flipped binding)).prod := by
      apply congrArg List.prod
      apply List.map_congr_left
      intro binding present
      by_cases same : binding = targetBinding
      · subst binding
        have changed : decode order cards flipped targetBinding = 1-digit := by
          have original := updated.2.1 targetBinding member
          change decode order cards flipped targetBinding = (if targetBinding = targetBinding then 1-digit else digit) at original
          simpa only [if_pos rfl] using original
        have smallRow : 1-gather physical axes < 2 := by omega
        rw [factorAt_eq _ _ _ _ member actual,factorAt_eq _ _ _ _ member actual,changed,
          gather_scatter_one physical _ axes length smallRow,
          bit_delta actual basis _ _ smallRow digitBound,bit_delta actual basis _ _ rowBound small]
        have condition : 1-gather physical axes = digit ↔ gather physical axes = 1-digit := by omega
        simp only [condition]
      · have changed : decode order cards flipped binding = decode order cards logical binding := by
          have original := updated.2.1 binding present
          change decode order cards flipped binding =
            (if binding = targetBinding then 1-digit else decode order cards logical binding) at original
          simpa only [if_neg same] using original
        rw [changed]
        obtain ⟨spectator,_read⟩ := lookup_exists output.owners binding present
        have disjoint := output_owner_axes_disjoint frame codes.owners binding targetBinding present member same
        rw [factorAt_eq _ _ _ _ present spectator,factorAt_eq _ _ _ _ present spectator,
          gather_disjoint physical _ axes _ disjoint]
    _ = _ := flippedFactors.symm
    _ = _ := (ordered_product_entry output physical flipped flippedBound).symm

/-- Flip the actual target's dense logical digit, using its retained carrier
cardinality and original position rather than a physical bit stride. -/
def targetFlip {roles state checked} (output : @Frame roles state checked) (target : Binding)
    (logical : Nat) : Nat :=
  RuntimeTargetDigit.update output target logical
    (1-decode checked.bindings (dimensionAt output.owners) logical target)

theorem target_flip_domain
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {inputCode outputCode}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (selectorBasis : selector.basis = [.bit]) (targetBasis : target.basis = [.bit])
    {selectorBits targetBits retained restricted}
    (literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
      codes.owners.before codes.owners.transport.after)
    (logical : Nat) (bound : logical < literal.outputCode.code.dimension) :
    targetFlip literal.outputCode codes.owners.returned.second logical < literal.outputCode.code.dimension ∧
      targetFlip literal.outputCode codes.owners.returned.second
        (targetFlip literal.outputCode codes.owners.returned.second logical) = logical := by
  let output := literal.outputCode
  let order := codes.owners.transport.after.bindings
  let wanted := codes.owners.returned.second
  let cards := dimensionAt output.owners
  let digit := decode order cards logical wanted
  have selected := RuntimeSelectionPartition.order_values _ _ _ codes.owners.returned.ordered
  have member : wanted ∈ order := selected.1 (by simp [wanted])
  have originalOwners : codes.owners.returned.first.owner = selector ∧ wanted.owner = target := by
    simpa only [List.map_cons,List.map_nil,List.cons.injEq,and_true] using selected.2
  obtain ⟨actual,_read⟩ := lookup_exists output.owners wanted member
  have card : cards wanted = 2 := by
    change dimensionAt output.owners wanted = 2
    rw [dimensionAt_eq output.owners wanted member actual,
      bit_layout actual (by rw [originalOwners.2,targetBasis])]
    rfl
  have logicalBound : logical < volume order cards := by rw [frame_volume output]; exact bound
  have digitBound : digit < 2 := by
    rw [← card]
    exact decode_bound order cards logical (cards_positive output.owners) logicalBound wanted member
  have small : 1-digit < 2 := by omega
  have changed := RuntimeTargetDigit.source_target_update frame codes selectorBasis targetBasis literal
    logical (1-digit) bound small
  have flipBound : targetFlip output wanted logical < output.code.dimension := changed.1
  have unique : order.Nodup :=
    List.Pairwise.of_map (fun binding : Binding => binding.port.token)
      (fun _ _ different same => different (congrArg (fun binding : Binding => binding.port.token) same))
      codes.owners.transport.after.tokensDistinct
  refine ⟨flipBound,?_⟩
  change encode order cards (fun binding => if binding = wanted then
    1-decode order cards (targetFlip output wanted logical) wanted else
    decode order cards (targetFlip output wanted logical) binding) = logical
  calc
    _ = encode order cards (decode order cards logical) := by
      apply encode_congr
      intro binding present
      have read := changed.2.1 binding present
      change decode order cards (targetFlip output wanted logical) binding =
        (if binding = wanted then 1-digit else decode order cards logical binding) at read
      by_cases same : binding = wanted
      · subst binding
        rw [if_pos rfl] at read ⊢
        rw [read]
        omega
      · rw [if_neg same,read,if_neg same]
    _ = logical := encode_decode order cards logical unique (cards_positive output.owners) logicalBound

private theorem involution_range (size : Nat) (flip : Nat → Nat)
    (bounded : ∀ logical < size,flip logical < size)
    (inverse : ∀ logical < size,flip (flip logical) = logical) :
    ((List.range size).map flip).Perm (List.range size) := by
  have unique : ((List.range size).map flip).Nodup :=
    List.Nodup.map_on (fun left leftMember right rightMember equal => by
      have same := congrArg flip equal
      rw [inverse left (List.mem_range.mp leftMember),inverse right (List.mem_range.mp rightMember)] at same
      exact same) List.nodup_range
  apply (List.perm_ext_iff_of_nodup unique List.nodup_range).mpr
  intro logical
  constructor
  · intro member
    obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
    exact List.mem_range.mpr (bounded original (List.mem_range.mp originalMember))
  · intro member
    have bound := List.mem_range.mp member
    exact List.mem_map.mpr ⟨flip logical,List.mem_range.mpr (bounded logical bound),inverse logical bound⟩

/-- Literal target-wire flipping acts on the same original target digit in
an arbitrary entangled logical/reference family. This only reindexes a finite
total-complex sum; no successful bounded arithmetic is inferred from it. -/
theorem target_flip_references
    {Reference : Type} {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {inputCode outputCode}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (selectorBasis : selector.basis = [.bit]) (targetBasis : target.basis = [.bit])
    {selectorBits targetBits retained restricted}
    (literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
      codes.owners.before codes.owners.transport.after)
    (joint : Nat → Reference → ℂ) (physical : Nat) (reference : Reference) :
    let axes := codes.owners.returned.second.port.wires.map frame.interval.after.quantum.frame.idxOf
    referenceAction literal.outputCode joint (scatter physical axes (1-gather physical axes)) reference =
      referenceAction literal.outputCode
        (fun logical ref => joint (targetFlip literal.outputCode codes.owners.returned.second logical) ref)
        physical reference := by
  let output := literal.outputCode
  let flip := targetFlip output codes.owners.returned.second
  let axes := codes.owners.returned.second.port.wires.map frame.interval.after.quantum.frame.idxOf
  have domain := target_flip_domain frame codes selectorBasis targetBasis literal
  have permutation := involution_range output.code.dimension flip
    (fun logical bound => (domain logical bound).1) (fun logical bound => (domain logical bound).2)
  change ((List.range output.code.dimension).map fun logical =>
      scalar (output.embedding (scatter physical axes (1-gather physical axes)) logical)*joint logical reference).sum =
    ((List.range output.code.dimension).map fun logical => scalar (output.embedding physical logical)*joint (flip logical) reference).sum
  calc
    _ = ((List.range output.code.dimension).map fun logical =>
        scalar (output.embedding physical (flip logical))*joint (flip (flip logical)) reference).sum := by
      apply Qleisli.Exact.sum_map_congr
      intro logical member
      have inverse : flip (flip logical) = logical := (domain logical (List.mem_range.mp member)).2
      rw [inverse]
      exact congrArg (fun coefficient : ℂ => coefficient*joint logical reference)
        (target_flip_entry frame codes selectorBasis targetBasis literal physical logical (List.mem_range.mp member))
    _ = (((List.range output.code.dimension).map flip).map fun logical =>
        scalar (output.embedding physical logical)*joint (flip logical) reference).sum := by
      rw [List.map_map]
      rfl
    _ = _ := (permutation.map (fun logical => scalar (output.embedding physical logical)*joint (flip logical) reference)).sum_eq

#print axioms output_axes_unique
#print axioms output_owner_axes_disjoint
#print axioms gather_disjoint
#print axioms target_flip_entry
#print axioms target_flip_domain
#print axioms target_flip_references

end Qleisli.RuntimeTargetScatter
