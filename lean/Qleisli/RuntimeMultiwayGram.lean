import Mathlib.Data.List.FinRange
import Qleisli.RuntimeSelectionGram
import Qleisli.RuntimeNominalSupport
import Mathlib.Data.List.FinRange

/-! Original-ordinal arm tables and logical Gram transport for actual finite
selectors with a Bit target. Logical ordinals index the complete native arm
table; actual selector code labels index its physical-sector receipts. No
missing arm is replaced by identity, no joined matrix is allocated and no
bounded availability, native gate or accepted-handle claim is introduced.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeMultiwayGram
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Semantics.Exact
open RuntimeOwnerMap (Binding Map)
open RuntimeForestCode RuntimeOwnerCodeReindex
open Qleisli.Semantics.Exact Qleisli.RuntimeForestProduct Qleisli.MixedRadix
open Qleisli.RuntimeForestRegroup Qleisli.RuntimeTargetScatter

/-- Every original ordinal has its actual matrix and physical-sector receipt.
The labels list is retained in its native layout order, not sorted or deduped. -/
structure OrdinalTable (inputCode outputCode : Matrix) (sectors : List Matrix)
    (labels : List Nat) (arms : List Matrix) : Prop where
  count : arms.length = labels.length
  checked : ∀ ordinal : Fin labels.length,
    QleisliKernel.Qirf.NominalSector.LogicalBinding inputCode outputCode sectors
      (labels[ordinal.val],arms[ordinal.val]'(by rw [count]; exact ordinal.isLt))
      (arms[ordinal.val]'(by rw [count]; exact ordinal.isLt))

def OrdinalTable.arm {inputCode outputCode sectors labels arms}
    (table : OrdinalTable inputCode outputCode sectors labels arms) (ordinal : Fin labels.length) : Matrix :=
  arms[ordinal.val]'(by rw [table.count]; exact ordinal.isLt)

theorem OrdinalTable.arm_checked {inputCode outputCode sectors labels arms}
    (table : OrdinalTable inputCode outputCode sectors labels arms) (ordinal : Fin labels.length) :
    QleisliKernel.Qirf.NominalSector.LogicalBinding inputCode outputCode sectors
      (labels[ordinal.val],table.arm ordinal) (table.arm ordinal) := table.checked ordinal

/-- The same successful native check supplies complete original table order
and binds every logical result to its requested arm, including unused labels. -/
theorem ordinal_table {inputCode outputCode sectors labels expected logical}
    (equations : RuntimeInterval.Computed
      (QleisliKernel.Qirf.NominalSector.checkLogicals inputCode outputCode sectors labels expected) logical) :
    logical = expected ∧ OrdinalTable inputCode outputCode sectors labels expected := by
  obtain ⟨work,left,ran⟩ := equations
  obtain ⟨count,each⟩ := QleisliKernel.Qirf.NominalSector.checkLogicals_bound _ _ _ _ _ _ work left ran
  have zippedLength : (labels.zip expected).length = labels.length := by
    rw [List.length_zip,count,Nat.min_self]
  have actualCount : logical.length = labels.length :=
    (QleisliKernel.Exact.listRel_length _ _ _ each).trans zippedLength
  have checkedAt (index : Nat) (bound : index < labels.length) :
      QleisliKernel.Qirf.NominalSector.LogicalBinding inputCode outputCode sectors
        (labels[index],expected[index]'(by rw [count]; exact bound))
        (logical[index]'(by rw [actualCount]; exact bound)) := by
    have binding := QleisliKernel.Exact.listRel_getElem _ _ _ each index (by rw [zippedLength]; exact bound)
    simpa only [List.getElem_zip] using binding
  have same : logical = expected := by
    apply List.ext_getElem (actualCount.trans count.symm)
    intro index _inside actual
    exact (checkedAt index (by rw [← count]; exact actual)).1
  refine ⟨same,⟨count,?_⟩⟩
  intro ordinal
  have binding := checkedAt ordinal.val ordinal.isLt
  simpa only [same] using binding

/-- The original source selector read and the exact returned owner read
describe the same layout, including its padded physical-label table. -/
theorem returned_selector_layout
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {inputCode outputCode selectorBits targetBits retained restricted labels}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (layouts : RuntimePureBody.SelectionLayouts selector.basis target.basis selectorBits targetBits labels)
    (literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
      codes.owners.before codes.owners.transport.after) :
    ∃ actual : OwnerCode codes.owners.returned.first,
      lookup literal.outputCode.owners codes.owners.returned.first = some actual ∧
      actual.layout = (⟨selectorBits,labels⟩ : Semantics.FiniteCarrier.Layout) := by
  have selected := RuntimeSelectionPartition.order_values _ _ _ codes.owners.returned.ordered
  have member : codes.owners.returned.first ∈ codes.owners.transport.after.bindings := selected.1 (by simp)
  have owners : codes.owners.returned.first.owner = selector ∧ codes.owners.returned.second.owner = target := by
    simpa only [List.map_cons,List.map_nil,List.cons.injEq,and_true] using selected.2
  obtain ⟨actual,found⟩ := lookup_exists literal.outputCode.owners codes.owners.returned.first member
  have original := actual.reference.1
  rw [owners.1] at original
  obtain ⟨work,left,ran⟩ := layouts.selectorRead
  have layout := QleisliKernel.FiniteCarrier.read_reference _ _ work left ran
  exact ⟨actual,found,Option.some.inj (original.symm.trans layout)⟩

theorem selector_card
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {inputCode outputCode selectorBits targetBits retained restricted labels}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (layouts : RuntimePureBody.SelectionLayouts selector.basis target.basis selectorBits targetBits labels)
    (literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
      codes.owners.before codes.owners.transport.after) :
    dimensionAt literal.outputCode.owners codes.owners.returned.first = labels.length := by
  obtain ⟨actual,_found,layout⟩ := returned_selector_layout frame codes layouts literal
  have selected := RuntimeSelectionPartition.order_values _ _ _ codes.owners.returned.ordered
  have member : codes.owners.returned.first ∈ codes.owners.transport.after.bindings := selected.1 (by simp)
  rw [dimensionAt_eq literal.outputCode.owners codes.owners.returned.first member actual,layout]

/-- A second target write replaces the first one while every other original
digit retains its value. Only the first write must be in the actual domain. -/
theorem update_twice {roles state checked} (code : @Frame roles state checked)
    (target : Binding) (logical row col : Nat) (bound : logical < code.code.dimension)
    (small : row < dimensionAt code.owners target) :
    RuntimeTargetDigit.update code target (RuntimeTargetDigit.update code target logical row) col =
      RuntimeTargetDigit.update code target logical col := by
  have changed := RuntimeTargetDigit.update_digits code target logical row bound small
  unfold RuntimeTargetDigit.update
  apply encode_congr
  intro binding member
  by_cases same : binding = target
  · rw [if_pos same,if_pos same]
  · rw [if_neg same,if_neg same]
    exact (changed.2 binding member).trans (if_neg same)

/-- Flip the actual Bit target in any complete caller code. No property of
the selector's type, padding, width or ordinal is needed for this bijection. -/
theorem bit_flip_domain {roles state checked} (code : @Frame roles state checked)
    (target : Binding) (member : target ∈ checked.bindings) (basis : target.owner.basis = [.bit])
    (logical : Nat) (bound : logical < code.code.dimension) :
    targetFlip code target logical < code.code.dimension ∧
      targetFlip code target (targetFlip code target logical) = logical := by
  obtain ⟨actual,_found⟩ := lookup_exists code.owners target member
  have original := actual.reference.1
  rw [basis] at original
  change some (⟨1,[0,1]⟩ : Semantics.FiniteCarrier.Layout) = some actual.layout at original
  have layout := Option.some.inj original
  have card : dimensionAt code.owners target = 2 := by
    rw [dimensionAt_eq code.owners target member actual,← layout]
    rfl
  let digit := decode checked.bindings (dimensionAt code.owners) logical target
  let flipped := targetFlip code target logical
  have digitBound : digit < 2 := bit_digit_lt code target member basis logical bound
  have small : 1-digit < dimensionAt code.owners target := by rw [card]; omega
  have changed := RuntimeTargetDigit.update_digits code target logical (1-digit) bound small
  have read : decode checked.bindings (dimensionAt code.owners) flipped target = 1-digit := by
    have value := changed.2 target member
    change decode checked.bindings (dimensionAt code.owners) flipped target =
      (if target = target then 1-digit else digit) at value
    simpa only [if_pos rfl] using value
  refine ⟨changed.1,?_⟩
  change RuntimeTargetDigit.update code target flipped
    (1-decode checked.bindings (dimensionAt code.owners) flipped target) = logical
  rw [read]
  have restored : 1-(1-digit) = digit := by omega
  rw [restored]
  exact (update_twice code target logical (1-digit) digit bound small).trans (update_self code target logical bound)

/-- The original selector digit, bounded by the cardinality of its actual
retained carrier. Its value is an ordinal, not a physical code label. -/
def selectorIndex {roles state checked labels} (code : @Frame roles state checked)
    (selector : Binding) (member : selector ∈ checked.bindings)
    (card : dimensionAt code.owners selector = (labels : List Nat).length)
    (index : Fin code.code.dimension) : Fin labels.length :=
  ⟨decode checked.bindings (dimensionAt code.owners) index.val selector,by
    rw [← card]
    apply decode_bound _ _ _ (cards_positive code.owners) _ _ member
    rw [frame_volume code]
    exact index.isLt⟩

/-- A complete original-ordinal table acts only at the same target digit.
Both the table index and caller index are finite, so no missing-arm or
out-of-domain identity fallback is defined. -/
noncomputable def ordinalAction {roles state checked labels arms inputCode outputCode sectors}
    (code : @Frame roles state checked) (selector target : Binding)
    (member : selector ∈ checked.bindings)
    (table : OrdinalTable inputCode outputCode sectors labels arms)
    (card : dimensionAt code.owners selector = labels.length)
    {Reference : Type} (joint : Nat → Reference → ℂ) (index : Fin code.code.dimension) (ref : Reference) : ℂ :=
  action (table.arm (selectorIndex code selector member card index))
    (fun col => joint (RuntimeTargetDigit.update code target index.val col))
    (decode checked.bindings (dimensionAt code.owners) index.val target) ref

/-- Native Gram receipts for every original selector ordinal preserve the
complete caller logical inner product. Target pairing leaves the selector and
all nominal/zero-width spectators fixed; references remain arbitrary. -/
theorem table_gram {roles state checked labels arms inputCode outputCode sectors}
    (code : @Frame roles state checked) (selector target : Binding)
    (selectorMember : selector ∈ checked.bindings) (targetMember : target ∈ checked.bindings)
    (different : selector ≠ target) (targetBasis : target.owner.basis = [.bit])
    (table : OrdinalTable inputCode outputCode sectors labels arms)
    (card : dimensionAt code.owners selector = labels.length) (columns : inputCode.cols = 2)
    {R S : Type} (joint : Nat → R → ℂ) (other : Nat → S → ℂ) (r : R) (s : S) :
    ((List.finRange code.code.dimension).map fun index =>
      star (ordinalAction code selector target selectorMember table card joint index r) *
        ordinalAction code selector target selectorMember table card other index s).sum =
    ((List.finRange code.code.dimension).map fun index => star (joint index.val r)*other index.val s).sum := by
  let order := checked.bindings
  let cards := dimensionAt code.owners
  let digit := decode order cards
  let put := RuntimeTargetDigit.update code target
  have domain := bit_flip_domain code target targetMember targetBasis
  let flip : Fin code.code.dimension → Fin code.code.dimension :=
    fun index => ⟨targetFlip code target index.val,(domain index.val index.isLt).1⟩
  have inverse : Function.Involutive flip := by
    intro index
    apply Fin.ext
    exact (domain index.val index.isLt).2
  let involution : Equiv.Perm (Fin code.code.dimension) := ⟨flip,flip,inverse,inverse⟩
  have permutation := involution.map_finRange_perm
  let f := fun index : Fin code.code.dimension =>
    star (ordinalAction code selector target selectorMember table card joint index r) *
      ordinalAction code selector target selectorMember table card other index s
  let g := fun index : Fin code.code.dimension => star (joint index.val r)*other index.val s
  change ((List.finRange code.code.dimension).map f).sum = ((List.finRange code.code.dimension).map g).sum
  apply Qleisli.RuntimeSelectionGram.sum_pairs_of_perm _ flip f g permutation
  intro index _present
  have targetCard : cards target = 2 := by
    obtain ⟨actual,_found⟩ := lookup_exists code.owners target targetMember
    have original := actual.reference.1
    rw [targetBasis] at original
    change some (⟨1,[0,1]⟩ : Semantics.FiniteCarrier.Layout) = some actual.layout at original
    have layout := Option.some.inj original
    change dimensionAt code.owners target = 2
    rw [dimensionAt_eq code.owners target targetMember actual,← layout]
    rfl
  let b := digit index.val target
  have bBound : b < 2 := bit_digit_lt code target targetMember targetBasis index.val index.isLt
  have same : put index.val b = index.val := update_self code target index.val index.isLt
  have opposite : put index.val (1-b) = targetFlip code target index.val := rfl
  let atIndex (row : Nat) (small : row < 2) : Fin code.code.dimension :=
    ⟨put index.val row,(RuntimeTargetDigit.update_digits code target index.val row index.isLt
      (by change row < cards target; rwa [targetCard])).1⟩
  let ordinal := selectorIndex code selector selectorMember card index
  have atRow {Ref : Type} (values : Nat → Ref → ℂ) (ref : Ref) (row : Nat) (small : row < 2) :
      ordinalAction code selector target selectorMember table card values (atIndex row small) ref =
        action (table.arm ordinal) (fun col => values (put index.val col)) row ref := by
    have changed := RuntimeTargetDigit.update_digits code target index.val row index.isLt
      (by change row < cards target; rwa [targetCard])
    have sel : digit (put index.val row) selector = digit index.val selector :=
      (changed.2 selector selectorMember).trans (if_neg different)
    have tgt : digit (put index.val row) target = row :=
      (changed.2 target targetMember).trans (if_pos rfl)
    have sameOrdinal : selectorIndex code selector selectorMember card (atIndex row small) = ordinal := Fin.ext sel
    have twice (col : Nat) : put (put index.val row) col = put index.val col :=
      update_twice code target index.val row col index.isLt (by change row < cards target; rwa [targetCard])
    change action (table.arm (selectorIndex code selector selectorMember card (atIndex row small)))
      (fun col => values (put (put index.val row) col)) (digit (put index.val row) target) ref = _
    rw [sameOrdinal,tgt]
    simp only [twice]
  have pair : f (atIndex 0 (by decide)) + f (atIndex 1 (by decide)) =
      g (atIndex 0 (by decide)) + g (atIndex 1 (by decide)) := by
    dsimp only [f,g]
    rw [atRow joint r 0 (by decide),atRow other s 0 (by decide),
      atRow joint r 1 (by decide),atRow other s 1 (by decide)]
    exact Qleisli.RuntimeSelectionGram.arm_pair (table.arm_checked ordinal)
      ((table.arm_checked ordinal).2.1.trans columns) _ _ r s
  rcases (show b = 0 ∨ b = 1 by omega) with low | high
  · rw [low] at same opposite
    change put index.val 1 = targetFlip code target index.val at opposite
    have first : atIndex 0 (by decide) = index := Fin.ext same
    have second : atIndex 1 (by decide) = flip index := Fin.ext opposite
    simpa only [first,second] using pair
  · rw [high] at same opposite
    change put index.val 0 = targetFlip code target index.val at opposite
    have first : atIndex 0 (by decide) = flip index := Fin.ext opposite
    have second : atIndex 1 (by decide) = index := Fin.ext same
    simpa only [first,second,add_comm] using pair

/-- The complete original caller action associated with a native selection's
source-ordinal arm table. The table proof and all code/layout reads belong to
that same node; the finite logical index supplies its actual digit bound. -/
noncomputable def sourceAction
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {inputCode outputCode selectorBits targetBits retained restricted labels arms}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (layouts : RuntimePureBody.SelectionLayouts selector.basis target.basis selectorBits targetBits labels)
    (literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
      codes.owners.before codes.owners.transport.after)
    (table : OrdinalTable inputCode outputCode retained.sectors labels arms)
    {Reference : Type} (joint : Nat → Reference → ℂ) (index : Fin literal.outputCode.code.dimension) (ref : Reference) : ℂ :=
  ordinalAction literal.outputCode codes.owners.returned.first codes.owners.returned.second
    ((RuntimeSelectionPartition.order_values _ _ _ codes.owners.returned.ordered).1 (by simp))
    table (selector_card frame codes layouts literal) joint index ref

/-- The actual source layouts, target code and ordered native matrix equations
supply every hypothesis of the multiway caller Gram law. The selector may be
nominal, padded, a product or zero width; only its original ordinal indexes
the complete arm table. This is not a physical-action or acceptance theorem. -/
theorem checked_selection {R S : Type}
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {inputCode outputCode : Matrix} {selectorBits targetBits : Nat} {retained : Raw.Sector.Retained}
    {restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits selectorBits] [.bits targetBits]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained}
    {labels : List Nat} {expected logical : List Matrix}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (layouts : RuntimePureBody.SelectionLayouts selector.basis target.basis selectorBits targetBits labels)
    (equations : RuntimeInterval.Computed (QleisliKernel.Qirf.NominalSector.checkLogicals
      inputCode outputCode retained.sectors labels expected) logical)
    (targetBasis : target.basis = [.bit])
    (literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
      codes.owners.before codes.owners.transport.after)
    (joint : Nat → R → ℂ) (other : Nat → S → ℂ) (r : R) (s : S) :
    logical = expected ∧ ∃ table : OrdinalTable inputCode outputCode retained.sectors labels expected,
      ((List.finRange literal.outputCode.code.dimension).map fun index =>
        star (sourceAction frame codes layouts literal table joint index r) *
          sourceAction frame codes layouts literal table other index s).sum =
      ((List.finRange literal.outputCode.code.dimension).map fun index => star (joint index.val r)*other index.val s).sum := by
  obtain ⟨same,table⟩ := ordinal_table equations
  let output := literal.outputCode
  let order := codes.owners.transport.after.bindings
  let first := codes.owners.returned.first
  let second := codes.owners.returned.second
  have selected := RuntimeSelectionPartition.order_values _ _ _ codes.owners.returned.ordered
  have members : first ∈ order ∧ second ∈ order := ⟨selected.1 (by simp [first]),selected.1 (by simp [second])⟩
  have owners : first.owner = selector ∧ second.owner = target := by
    simpa only [List.map_cons,List.map_nil,List.cons.injEq,and_true] using selected.2
  have unique : order.Nodup :=
    List.Pairwise.of_map (fun binding : Binding => binding.port.token)
      (fun _ _ different same => different (congrArg (fun binding : Binding => binding.port.token) same))
      codes.owners.transport.after.tokensDistinct
  have grouped : (first::second::RuntimeSelectionPartition.complement order codes.owners.returned.toList).Nodup :=
    (RuntimeSelectionPartition.source_output_partition frame codes.owners).symm.nodup unique
  have different : first ≠ second := by
    intro equal
    apply (List.nodup_cons.mp grouped).1
    rw [equal]
    exact List.mem_cons_self
  have basis : second.owner.basis = [.bit] := by rw [owners.2,targetBasis]
  have inputRead : RuntimeInterval.Computed
      (Carrier.ownerCode [⟨codes.owners.selected.second.port,[.bit]⟩]) inputCode := by
    simpa only [targetBasis] using codes.inputRead
  have columns : inputCode.cols = 2 := by
    rw [Qleisli.RuntimeBitSectorAction.bit_code inputRead]
    rfl
  exact ⟨same,table,table_gram output first second members.1 members.2 different basis table
    (selector_card frame codes layouts literal) columns joint other r s⟩

#print axioms ordinal_table
#print axioms returned_selector_layout
#print axioms selector_card
#print axioms update_twice
#print axioms bit_flip_domain
#print axioms table_gram
#print axioms checked_selection

end Qleisli.RuntimeMultiwayGram
