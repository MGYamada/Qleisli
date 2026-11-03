import Qleisli.RuntimeSelectionAction

/-! Gram preservation for the two actually verified logical arms on the full
ordered caller code, including spectators and external references.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeSelectionGram
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Semantics.Exact
open Qleisli.Semantics.Exact Qleisli.RuntimeForestProduct Qleisli.MixedRadix
open Qleisli.RuntimeTargetScatter Qleisli.RuntimeSelectionAction
open RuntimeForestCode RuntimeOwnerCodeReindex

/-- Sum the same local conservation law over both orientations of each pair,
on an explicit finite domain. It also applies to typed logical ordinals. -/
theorem sum_pairs_of_perm {α : Type} (indices : List α) (flip : α → α) (f g : α → ℂ)
    (perm : (indices.map flip).Perm indices)
    (pair : ∀ i ∈ indices, f i + f (flip i) = g i + g (flip i)) :
    (indices.map f).sum = (indices.map g).sum := by
  have same (h : α → ℂ) : (indices.map (fun i => h (flip i))).sum =
      (indices.map h).sum := by
    simpa only [List.map_map,Function.comp_def] using (perm.map h).sum_eq
  have both := Qleisli.Exact.sum_map_congr indices _ _ pair
  rw [List.sum_map_add,List.sum_map_add,same f,same g] at both
  linear_combination (norm := ring) (1/2 : ℂ) * both

/-- Sum a local conservation law over both orientations of each target pair. -/
theorem sum_pairs (size : Nat) (flip : Nat → Nat) (f g : Nat → ℂ)
    (perm : ((List.range size).map flip).Perm (List.range size))
    (pair : ∀ i < size, f i + f (flip i) = g i + g (flip i)) :
    ((List.range size).map f).sum = ((List.range size).map g).sum :=
  sum_pairs_of_perm (List.range size) flip f g perm (fun i member => pair i (List.mem_range.mp member))

/-- The actual native logical-binding receipt supplies both the Gram check and
the product dimensions for this two-row action. -/
theorem arm_pair {inputCode outputCode physical label required logical}
    (binding : QleisliKernel.Qirf.NominalSector.LogicalBinding inputCode outputCode physical (label,required) logical)
    (columns : required.cols = 2) {R S : Type}
    (left : Nat → R → ℂ) (right : Nat → S → ℂ) (r : R) (s : S) :
    star (action required left 0 r)*action required right 0 s +
      star (action required left 1 r)*action required right 1 s =
    star (left 0 r)*right 0 s + star (left 1 r)*right 1 s := by
  have original : logical = required := binding.1
  obtain ⟨a,b,checked⟩ := binding.2.2.2.1
  obtain ⟨shape,c,d,gram⟩ := Finite.wholeSpace_conditions _ a b checked
  rw [original] at gram shape
  have preservation := Qleisli.Exact.isometry_inner_product required c d gram left right r s
  rw [shape,columns] at preservation
  change _ + (_ + 0) = _ + (_ + 0) at preservation
  simpa only [add_zero] using preservation

theorem logical_gram {R S : Type}
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {retained : Raw.Sector.Retained}
    {restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits 1] [.bits 1]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained}
    {inputCode outputCode : Matrix}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (selectorBasis : selector.basis = [.bit]) (targetBasis : target.basis = [.bit])
    (literal : RuntimeLocalEvents.Literal frame 1 1 retained restricted codes.owners.before codes.owners.transport.after)
    {zero one zeroLogical oneLogical}
    (zeroChecked : QleisliKernel.Qirf.NominalSector.LogicalBinding inputCode outputCode retained.sectors (0,zero) zeroLogical)
    (oneChecked : QleisliKernel.Qirf.NominalSector.LogicalBinding inputCode outputCode retained.sectors (1,one) oneLogical)
    (joint : Nat → R → ℂ) (other : Nat → S → ℂ) (r : R) (s : S) :
    let output := literal.outputCode
    let first := codes.owners.returned.first
    let second := codes.owners.returned.second
    ((List.range output.code.dimension).map (fun i =>
      star (logicalAction output first second zero one joint i r) *
        logicalAction output first second zero one other i s)).sum =
    ((List.range output.code.dimension).map (fun i => star (joint i r)*other i s)).sum := by
  let output := literal.outputCode
  let order := codes.owners.transport.after.bindings
  let first := codes.owners.returned.first
  let second := codes.owners.returned.second
  let cards := dimensionAt output.owners
  let digit := decode order cards
  let put := RuntimeTargetDigit.update output second
  let flip := targetFlip output second
  let size := output.code.dimension
  have selected := RuntimeSelectionPartition.order_values _ _ _ codes.owners.returned.ordered
  have members : first ∈ order ∧ second ∈ order := ⟨selected.1 (by simp [first]),selected.1 (by simp [second])⟩
  have owners : first.owner = selector ∧ second.owner = target := by
    simpa only [List.map_cons,List.map_nil,List.cons.injEq,and_true] using selected.2
  obtain ⟨firstAxis,secondAxis,firstAxes,secondAxes,_axes,disjoint⟩ :=
    returned_bit_axes frame codes selectorBasis targetBasis literal
  have different : first ≠ second := by
    intro same
    have equality := congrArg (fun b : RuntimeOwnerMap.Binding => b.port.wires.map frame.interval.after.quantum.frame.idxOf) same
    change first.port.wires.map _ = second.port.wires.map _ at equality
    change first.port.wires.map _ = [firstAxis] at firstAxes
    change second.port.wires.map _ = [secondAxis] at secondAxes
    exact disjoint (List.cons.inj (firstAxes.symm.trans (equality.trans secondAxes))).1
  have flipDomain := target_flip_domain frame codes selectorBasis targetBasis literal
  apply sum_pairs size flip _ _ (involution_range size flip (fun i hi => (flipDomain i hi).1) (fun i hi => (flipDomain i hi).2))
  intro i hi
  let b := digit i second
  have bBound : b < 2 := bit_digit_lt output second members.2 (by rw [owners.2,targetBasis]) i hi
  have same : put i b = i := update_self output second i hi
  have opposite : put i (1-b) = flip i := rfl
  let matrix := if digit i first = 0 then zero else one
  have atRow {Ref : Type} (v : Nat → Ref → ℂ) (ref : Ref) (row : Nat) (hr : row < 2) :
      logicalAction output first second zero one v (put i row) ref =
        action matrix (fun col => v (put i col)) row ref := by
    have changed := RuntimeTargetDigit.source_target_update frame codes selectorBasis targetBasis literal i row hi hr
    have sel : digit (put i row) first = digit i first := (changed.2.1 first members.1).trans (if_neg different)
    have tgt : digit (put i row) second = row := (changed.2.1 second members.2).trans (if_pos rfl)
    have twice (col : Nat) : put (put i row) col = put i col := by
      apply encode_congr
      intro owner member
      by_cases eq : owner = second
      · rw [if_pos eq,if_pos eq]
      · simp only [if_neg eq]
        exact (changed.2.1 owner member).trans (if_neg eq)
    change action (if digit (put i row) first = 0 then zero else one)
      (fun col => v (put (put i row) col)) (digit (put i row) second) ref = _
    simp only [sel,tgt,twice,matrix]
  let f := fun j => star (logicalAction output first second zero one joint j r) *
    logicalAction output first second zero one other j s
  let g := fun j => star (joint j r)*other j s
  have pair : f (put i 0) + f (put i 1) = g (put i 0) + g (put i 1) := by
    dsimp only [f,g]
    rw [atRow joint r 0 (by decide),atRow other s 0 (by decide),
      atRow joint r 1 (by decide),atRow other s 1 (by decide)]
    by_cases low : digit i first = 0
    · rw [show matrix = zero from if_pos low]
      exact arm_pair zeroChecked (Qleisli.RuntimeBitSectorAction.binding_bounds frame codes targetBasis literal zeroChecked).2 _ _ r s
    · rw [show matrix = one from if_neg low]
      exact arm_pair oneChecked (Qleisli.RuntimeBitSectorAction.binding_bounds frame codes targetBasis literal oneChecked).2 _ _ r s
  change f i + f (flip i) = g i + g (flip i)
  rcases (show b = 0 ∨ b = 1 by omega) with h | h
  · rw [h] at same opposite
    change put i 1 = flip i at opposite
    simpa only [same,opposite] using pair
  · rw [h] at same opposite
    change put i 0 = flip i at opposite
    simpa only [same,opposite,add_comm] using pair

/-- Consume the widths, source labels, checked equations and owner codes
retained by a native selection node. Both source-ordered matrices and their
Gram law come from that one node. -/
theorem checked_selection {R S : Type}
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {selectorBits targetBits retained}
    {restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits selectorBits] [.bits targetBits]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained}
    {inputCode outputCode expected logical labels}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (layouts : RuntimePureBody.SelectionLayouts selector.basis target.basis selectorBits targetBits labels)
    (equations : RuntimeInterval.Computed (QleisliKernel.Qirf.NominalSector.checkLogicals
      inputCode outputCode retained.sectors labels expected) logical)
    (selectorBasis : selector.basis = [.bit]) (targetBasis : target.basis = [.bit])
    (literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted codes.owners.before codes.owners.transport.after)
    (form : Qleisli.RuntimeOwnerTransitionAction.SelectionForm frame codes.owners)
    (joint : Nat → R → ℂ) (other : Nat → S → ℂ) (r : R) (s : S) :
    ∃ zero one, labels = [0,1] ∧ expected = [zero,one] ∧ logical = [zero,one] ∧
      let first := codes.owners.returned.first
      let second := codes.owners.returned.second
      let output := literal.outputCode
      (∀ physical, Qleisli.Semantics.RawAction.events dependencies literal.traceResult.events
        (fun input => referenceAction literal.inputCode joint input r) physical =
        referenceAction output (logicalAction output first second zero one joint) physical r) ∧
      ((List.range output.code.dimension).map (fun i =>
        star (logicalAction output first second zero one joint i r) *
        logicalAction output first second zero one other i s)).sum =
      ((List.range output.code.dimension).map (fun i => star (joint i r)*other i s)).sum := by
  obtain ⟨sw,tw,labelOrder,zero,one,armOrder,actual,zeroChecked,oneChecked⟩ :=
    layouts.bit_bindings selectorBasis targetBasis equations
  subst selectorBits targetBits
  exact ⟨zero,one,labelOrder,armOrder,actual,
    fun physical => caller_action frame codes selectorBasis targetBasis literal form
      zeroChecked oneChecked joint physical r,
    logical_gram frame codes selectorBasis targetBasis literal zeroChecked oneChecked joint other r s⟩

#print axioms checked_selection
#print axioms logical_gram
end Qleisli.RuntimeSelectionGram
