import Qleisli.RuntimeFiniteTargetAction

/-! Logical finite-target row sums in the original complete caller domain.
The actual retained cardinality supplies the row set, including cardinality
one for zero-width owners. A target-zero anchor enumerates each spectator
configuration once; no averaging, physical-width cardinality, joined matrix
or separability assumption is used.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeFiniteTargetGram
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Semantics.Exact
open RuntimeOwnerMap (Binding)
open RuntimeForestCode RuntimeOwnerCodeReindex
open Qleisli.Semantics.Exact Qleisli.RuntimeForestProduct Qleisli.MixedRadix
open Qleisli.RuntimeForestRegroup Qleisli.RuntimeFiniteTargetLogical Qleisli.RuntimeMultiwayGram

def putIndex {roles state checked} (code : @Frame roles state checked) (target : Binding)
    (index : Fin code.code.dimension) (row : Fin (dimensionAt code.owners target)) : Fin code.code.dimension :=
  ⟨RuntimeTargetDigit.update code target index.val row.val,
    (RuntimeTargetDigit.update_digits code target index.val row.val index.isLt row.isLt).1⟩

private theorem fin_sum_nat (size : Nat) (values : Nat → ℂ) :
    ((List.finRange size).map fun index => values index.val).sum = ((List.range size).map values).sum := by
  have indices : (List.finRange size).map (fun index : Fin size => index.val) = List.range size := by
    apply List.ext_getElem (by simp only [List.length_map,List.length_finRange,List.length_range])
    intro index _inside _bounded
    simp only [List.getElem_map,List.getElem_finRange,List.getElem_range]
    rfl
  have same := congrArg (fun indices : List Nat => (indices.map values).sum) indices
  simpa only [List.map_map,Function.comp_def] using same

/-- Typed finite caller indices reindex by the same actual target transpose.
The source arm family remains finite; no outside-domain fallback is defined. -/
theorem finite_slice_reindex {roles state checked} (code : @Frame roles state checked)
    (target : Binding) (member : target ∈ checked.bindings)
    (first second : Fin (dimensionAt code.owners target)) (values : Fin code.code.dimension → ℂ) :
    ((List.finRange code.code.dimension).map fun index =>
      if decode checked.bindings (dimensionAt code.owners) index.val target = first.val then
        values (putIndex code target index second) else 0).sum =
      ((List.finRange code.code.dimension).map fun index =>
        if decode checked.bindings (dimensionAt code.owners) index.val target = second.val then values index else 0).sum := by
  let digit := fun index : Fin code.code.dimension => decode checked.bindings (dimensionAt code.owners) index.val target
  have domain := transpose_domain code target member first.val second.val
  let flip : Fin code.code.dimension → Fin code.code.dimension := fun index =>
    ⟨transpose code target first.val second.val index.val,(domain index.val first.isLt second.isLt index.isLt).1⟩
  have inverse : Function.Involutive flip := by
    intro index
    apply Fin.ext
    exact (domain index.val first.isLt second.isLt index.isLt).2.1
  let equivalence : Equiv.Perm (Fin code.code.dimension) := ⟨flip,flip,inverse,inverse⟩
  have permutation := equivalence.map_finRange_perm
  let term := fun index => if digit index = second.val then values index else 0
  calc
    _ = ((List.finRange code.code.dimension).map fun index => term (flip index)).sum := by
      apply Qleisli.Exact.sum_map_congr
      intro index _present
      have changed := domain index.val first.isLt second.isLt index.isLt
      have read : digit (flip index) = swapDigit first.val second.val (digit index) :=
        (changed.2.2 target member).trans (if_pos rfl)
      by_cases selected : digit index = first.val
      · have write : flip index = putIndex code target index second := by
          apply Fin.ext
          change RuntimeTargetDigit.update code target index.val (swapDigit first.val second.val (digit index)) =
            RuntimeTargetDigit.update code target index.val second.val
          rw [selected]
          simp [swapDigit]
        have swapped : digit (flip index) = second.val := by
          rw [read,selected]
          exact if_pos rfl
        change (if digit index = first.val then _ else 0) = if digit (flip index) = second.val then _ else 0
        rw [if_pos selected,if_pos swapped,write]
      · have absent : digit (flip index) ≠ second.val := by
          rw [read]
          exact fun equal => selected ((swapDigit_eq_second first.val second.val (digit index)).mp equal)
        change (if digit index = first.val then _ else 0) = if digit (flip index) = second.val then _ else 0
        rw [if_neg selected,if_neg absent]
    _ = _ := by
      simpa only [List.map_map,Function.comp_def] using (permutation.map term).sum_eq

/-- Each complete logical input occurs once in the valid target rows over
the original target-zero anchor. Distinct zero-width spectators keep their
original positions and cardinalities throughout the construction. -/
theorem sum_target_rows {roles state checked} (code : @Frame roles state checked)
    (target : Binding) (member : target ∈ checked.bindings) (values : Fin code.code.dimension → ℂ) :
    ((List.finRange code.code.dimension).map values).sum =
      ((List.finRange code.code.dimension).map fun index =>
        if decode checked.bindings (dimensionAt code.owners) index.val target = 0 then
          ((List.finRange (dimensionAt code.owners target)).map fun row =>
            values (putIndex code target index row)).sum
        else 0).sum := by
  let digit := fun index : Fin code.code.dimension => decode checked.bindings (dimensionAt code.owners) index.val target
  let zero : Fin (dimensionAt code.owners target) := ⟨0,cards_positive code.owners target member⟩
  have small (index : Fin code.code.dimension) : digit index < dimensionAt code.owners target := by
    apply decode_bound checked.bindings (dimensionAt code.owners) index.val (cards_positive code.owners) _ target member
    rw [frame_volume code]
    exact index.isLt
  have one (index : Fin code.code.dimension) :
      ((List.finRange (dimensionAt code.owners target)).map fun row =>
        if digit index = row.val then values index else 0).sum = values index := by
    exact (fin_sum_nat (dimensionAt code.owners target)
      (fun row : Nat => if digit index = row then values index else 0)).trans
        (Qleisli.Exact.range_delta_sum _ (digit index) (fun _ => values index) (small index))
  calc
    _ = ((List.finRange code.code.dimension).map fun index =>
        ((List.finRange (dimensionAt code.owners target)).map fun row =>
          if digit index = row.val then values index else 0).sum).sum := by
      apply Qleisli.Exact.sum_map_congr
      intro index _present
      exact (one index).symm
    _ = ((List.finRange (dimensionAt code.owners target)).map fun row =>
        ((List.finRange code.code.dimension).map fun index =>
          if digit index = row.val then values index else 0).sum).sum := Qleisli.Exact.sum_swap _ _ _
    _ = ((List.finRange (dimensionAt code.owners target)).map fun row =>
        ((List.finRange code.code.dimension).map fun index =>
          if digit index = 0 then values (putIndex code target index row) else 0).sum).sum := by
      apply Qleisli.Exact.sum_map_congr
      intro row _present
      exact (finite_slice_reindex code target member zero row values).symm
    _ = ((List.finRange code.code.dimension).map fun index =>
        ((List.finRange (dimensionAt code.owners target)).map fun row =>
          if digit index = 0 then values (putIndex code target index row) else 0).sum).sum :=
      Qleisli.Exact.sum_swap _ _ _
    _ = _ := by
      apply Qleisli.Exact.sum_map_congr
      intro index _present
      change ((List.finRange (dimensionAt code.owners target)).map fun row =>
        if digit index = 0 then values (putIndex code target index row) else 0).sum =
          if digit index = 0 then
            ((List.finRange (dimensionAt code.owners target)).map fun row => values (putIndex code target index row)).sum
          else 0
      by_cases selected : digit index = 0 <;> simp [selected]

/-- The same native requested-arm Gram receipt preserves an arbitrary full
finite target row sum. Rectangular physical codes do not replace this receipt. -/
theorem arm_rows {inputCode outputCode sectors label required logical size}
    (binding : QleisliKernel.Qirf.NominalSector.LogicalBinding inputCode outputCode sectors (label,required) logical)
    (columns : required.cols = size) {R S : Type}
    (joint : Nat → R → ℂ) (other : Nat → S → ℂ) (r : R) (s : S) :
    ((List.finRange size).map fun row =>
      star (action required joint row.val r) * action required other row.val s).sum =
      ((List.finRange size).map fun col => star (joint col.val r) * other col.val s).sum := by
  have original : logical = required := binding.1
  obtain ⟨a,b,checked⟩ := binding.2.2.2.1
  obtain ⟨shape,c,d,gram⟩ := Finite.wholeSpace_conditions _ a b checked
  rw [original] at gram shape
  have preservation := Qleisli.Exact.isometry_inner_product required c d gram joint other r s
  rw [shape,columns] at preservation
  exact (fin_sum_nat size _).trans (preservation.trans (fin_sum_nat size _).symm)

/-- Every original arm preserves the complete caller inner product. The
selector ordinal and all spectator digits are unchanged by each genuine
target write, and the row set uses that target's actual retained cardinality. -/
theorem table_gram {roles state checked labels arms inputCode outputCode sectors}
    (code : @Frame roles state checked) (selector target : Binding)
    (selectorMember : selector ∈ checked.bindings) (targetMember : target ∈ checked.bindings)
    (different : selector ≠ target)
    (table : OrdinalTable inputCode outputCode sectors labels arms)
    (card : dimensionAt code.owners selector = labels.length)
    (columns : inputCode.cols = dimensionAt code.owners target)
    {R S : Type} (joint : Nat → R → ℂ) (other : Nat → S → ℂ) (r : R) (s : S) :
    ((List.finRange code.code.dimension).map fun index =>
      star (ordinalAction code selector target selectorMember table card joint index r) *
        ordinalAction code selector target selectorMember table card other index s).sum =
      ((List.finRange code.code.dimension).map fun index => star (joint index.val r) * other index.val s).sum := by
  let digit := decode checked.bindings (dimensionAt code.owners)
  let put := RuntimeTargetDigit.update code target
  let f := fun index : Fin code.code.dimension =>
    star (ordinalAction code selector target selectorMember table card joint index r) *
      ordinalAction code selector target selectorMember table card other index s
  let g := fun index : Fin code.code.dimension => star (joint index.val r) * other index.val s
  change ((List.finRange code.code.dimension).map f).sum = ((List.finRange code.code.dimension).map g).sum
  rw [sum_target_rows code target targetMember f,sum_target_rows code target targetMember g]
  apply Qleisli.Exact.sum_map_congr
  intro index _present
  let ordinal := selectorIndex code selector selectorMember card index
  have atRow {Reference : Type} (values : Nat → Reference → ℂ) (reference : Reference)
      (row : Fin (dimensionAt code.owners target)) :
      ordinalAction code selector target selectorMember table card values (putIndex code target index row) reference =
        action (table.arm ordinal) (fun col => values (put index.val col)) row.val reference := by
    have changed := RuntimeTargetDigit.update_digits code target index.val row.val index.isLt row.isLt
    have sel : digit (put index.val row.val) selector = digit index.val selector :=
      (changed.2 selector selectorMember).trans (if_neg different)
    have tgt : digit (put index.val row.val) target = row.val :=
      (changed.2 target targetMember).trans (if_pos rfl)
    have sameOrdinal : selectorIndex code selector selectorMember card (putIndex code target index row) = ordinal :=
      Fin.ext sel
    have twice (col : Nat) : put (put index.val row.val) col = put index.val col :=
      Qleisli.RuntimeMultiwayGram.update_twice code target index.val row.val col index.isLt row.isLt
    change action (table.arm (selectorIndex code selector selectorMember card (putIndex code target index row)))
      (fun col => values (put (put index.val row.val) col)) (digit (put index.val row.val) target) reference = _
    rw [sameOrdinal,tgt]
    simp only [twice]
  have rows : ((List.finRange (dimensionAt code.owners target)).map fun row => f (putIndex code target index row)).sum =
      ((List.finRange (dimensionAt code.owners target)).map fun row => g (putIndex code target index row)).sum := by
    calc
      _ = ((List.finRange (dimensionAt code.owners target)).map fun row =>
          star (action (table.arm ordinal) (fun col => joint (put index.val col)) row.val r) *
            action (table.arm ordinal) (fun col => other (put index.val col)) row.val s).sum := by
        apply Qleisli.Exact.sum_map_congr
        intro row _present
        exact congrArg₂ (fun a b : ℂ => star a * b) (atRow joint r row) (atRow other s row)
      _ = _ := arm_rows (table.arm_checked ordinal) ((table.arm_checked ordinal).2.1.trans columns)
        (fun col => joint (put index.val col)) (fun col => other (put index.val col)) r s
  exact congrArg (fun value : ℂ => if digit index.val target = 0 then value else 0) rows

/-- Consume the same original source/code/layout/table receipts for complete
physical intertwining and full logical Gram. Every finite target uses its real
cardinality and encoding, including Unit and padded nominal records. This is
a theorem of the retained original node, not a new production acceptance gate. -/
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
    (literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
      codes.owners.before codes.owners.transport.after)
    (joint : Nat → R → ℂ) (other : Nat → S → ℂ) (r : R) (s : S) :
    logical = expected ∧ ∃ table : OrdinalTable inputCode outputCode retained.sectors labels expected,
      (∀ physical, Qleisli.Semantics.RawAction.events dependencies literal.traceResult.events
        (fun input => referenceAction literal.inputCode joint input r) physical =
          Qleisli.RuntimeMultiwayAction.finiteReferenceAction literal.outputCode
            (sourceAction frame codes layouts literal table joint) physical r) ∧
      ((List.finRange literal.outputCode.code.dimension).map fun index =>
        star (sourceAction frame codes layouts literal table joint index r) *
          sourceAction frame codes layouts literal table other index s).sum =
      ((List.finRange literal.outputCode.code.dimension).map fun index => star (joint index.val r) * other index.val s).sum := by
  obtain ⟨same,table⟩ := ordinal_table equations
  have selected := RuntimeSelectionPartition.order_values _ _ _ codes.owners.returned.ordered
  have selectorMember : codes.owners.returned.first ∈ codes.owners.transport.after.bindings := selected.1 (by simp)
  have targetMember : codes.owners.returned.second ∈ codes.owners.transport.after.bindings := selected.1 (by simp)
  have unique : codes.owners.transport.after.bindings.Nodup :=
    List.Pairwise.of_map (fun binding : Binding => binding.port.token)
      (fun _ _ different equal => different (congrArg (fun binding : Binding => binding.port.token) equal))
      codes.owners.transport.after.tokensDistinct
  have partition := RuntimeSelectionPartition.source_output_partition frame codes.owners
  have returnedUnique := (List.nodup_append.mp (partition.symm.nodup unique)).1
  have different : codes.owners.returned.first ≠ codes.owners.returned.second := by
    intro equal
    have member : codes.owners.returned.first ∈ [codes.owners.returned.second] := by rw [equal]; simp
    exact (List.nodup_cons.mp returnedUnique).1 member
  obtain ⟨actual,_found,_bits,inputSame,_outputSame⟩ :=
    Qleisli.RuntimeFiniteSectorAction.returned_target_layout frame codes layouts literal
  have columns : inputCode.cols = dimensionAt literal.outputCode.owners codes.owners.returned.second :=
    (congrArg Matrix.cols inputSame).trans
      (dimensionAt_eq literal.outputCode.owners codes.owners.returned.second targetMember actual).symm
  refine ⟨same,table,fun physical =>
    Qleisli.RuntimeFiniteTargetAction.caller_action frame codes layouts literal table joint physical r,?_⟩
  exact table_gram literal.outputCode codes.owners.returned.first codes.owners.returned.second selectorMember targetMember
    different table (selector_card frame codes layouts literal) columns joint other r s

#print axioms finite_slice_reindex
#print axioms sum_target_rows
#print axioms table_gram
#print axioms checked_selection

end Qleisli.RuntimeFiniteTargetGram
