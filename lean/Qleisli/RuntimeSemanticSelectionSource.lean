import Qleisli.RuntimeSemanticSelectionFibre
import Qleisli.RuntimeSourceOrdinalAction

/-! Relate the source's ordinal choice to an actual retained physical sector,
using the same sparse owner code throughout.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeSemanticSelectionSource
open QleisliKernel QleisliKernel.Qirf
open Semantics.Exact (Matrix)
open Semantics.Finite (gather scatter)
open Semantics.FiniteCarrier (encoding)
open QleisliKernel.FiniteRestriction (pack)
open RuntimeOwnerMap (Binding Map)
open RuntimeForestCode (embed forestAxes)
open RuntimeSemanticForest (Frame ownerLayout owner_layout frame_dimension owner_support)
open RuntimeForestRegroup (sourceDimension)
open RuntimeLiteralHistory (applySourceOwner)
open Qleisli.MixedRadix (decode encode volume recode)
open Qleisli.Semantics.Exact (action scalar)
open Qleisli.Semantics.RawAction (events)
open RuntimeSemanticSelectionFibre
  (native_owner_layout unique_bindings returned_axes target_update logical_sector_action padding_sector_action owner_padding_zero)

/-- Replacing the target digit in original order has the same coefficient
as the canonical target action after regrouping. -/
theorem target_update_at {owners : Map} (frame : Frame owners) (unique : owners.Nodup)
    (target : Binding) (member : target ∈ owners) (matrix : Matrix)
    (cols : matrix.cols = (ownerLayout target).labels.length)
    (rows : matrix.rows = (ownerLayout target).labels.length)
    {Reference : Type} (joint : Nat → Reference → ℂ) (index : Nat) (reference : Reference)
    (bound : index < frame.code.dimension) :
    applySourceOwner owners owners target target matrix joint index reference =
      action matrix (fun input ref => joint
        (encode owners (sourceDimension owners) fun b => if b = target then input
          else decode owners (sourceDimension owners) index b) ref)
        (decode owners (sourceDimension owners) index target) reference := by
  let cards := sourceDimension owners
  let digits := decode owners cards index
  let rest := owners.erase target
  let ordered := target::rest
  let high := encode rest cards digits
  let low := digits target
  let position := recode owners ordered cards index
  have permutation : owners.Perm ordered := List.perm_cons_erase member
  have cardinal (b : Binding) (present : b ∈ owners) : cards b = (ownerLayout b).labels.length := by
    simp only [cards,sourceDimension,if_pos present,Semantics.FiniteCarrier.dimension,
      (owner_layout (frame.available b present)).1,Option.map_some,Option.getD_some]
  have positive (b : Binding) (present : b ∈ owners) : 0 < cards b := by
    rw [cardinal b present]
    exact (RuntimeForestProduct.layout_bounds _ _ (owner_layout (frame.available b present)).1).1
  have inside : index < volume owners cards := frame_dimension frame ▸ bound
  have digitBound (b : Binding) (present : b ∈ owners) : digits b < cards b :=
    MixedRadix.decode_bound owners cards index positive inside b present
  have targetCard := cardinal target member
  have lowBound : low < cards target := digitBound target member
  have split : position = low+cards target*high := rfl
  have row := rows.trans targetCard.symm
  have column := cols.trans targetCard.symm
  have remainder : position % matrix.rows = low := by
    rw [split,row]
    simp only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt lowBound]
  have quotient : position / matrix.rows = high := by
    rw [split,row,Nat.add_mul_div_left _ _ (positive target member),Nat.div_eq_of_lt lowBound,Nat.zero_add]
  change action matrix
      (fun input ref => joint (recode ordered owners cards (input+matrix.cols*(position/matrix.rows))) ref)
      (position % matrix.rows) reference = _
  rw [remainder,quotient]
  unfold action
  apply Qleisli.Exact.sum_map_congr
  intro input present
  let replaced := fun b : Binding => if b = target then input else digits b
  have valid (b : Binding) (present : b ∈ owners) : replaced b < cards b := by
    by_cases same : b = target
    · subst b
      simp only [replaced,if_pos rfl]
      exact column ▸ List.mem_range.mp ‹input ∈ List.range matrix.cols›
    · simp only [replaced,if_neg same]
      exact digitBound b present
  have replacement : encode ordered cards replaced = input+cards target*high := by
    change replaced target+cards target*encode rest cards replaced = _
    simp only [replaced,if_pos rfl]
    apply congrArg (fun tail => input+cards target*tail)
    apply MixedRadix.encode_congr
    intro b present
    have absent := (List.nodup_cons.mp (permutation.nodup unique)).1
    have different : b ≠ target := fun same => absent (same ▸ present)
    simp only [if_neg different]
  let changed := encode owners cards replaced
  have regrouped : recode owners ordered cards changed = input+matrix.cols*high := by
    unfold recode
    calc
      _ = encode ordered cards replaced := by
        apply MixedRadix.encode_congr
        intro b present
        exact MixedRadix.decode_encode owners cards replaced valid b (permutation.mem_iff.mpr present)
      _ = _ := by rw [replacement,column]
  have original : recode ordered owners cards (input+matrix.cols*high) = changed := by
    rw [← regrouped]
    exact MixedRadix.recode_inverse owners ordered cards permutation unique positive changed
      (MixedRadix.encode_bound owners cards replaced valid)
  change Qleisli.Semantics.Exact.entry matrix low input *
      joint (recode ordered owners cards (input+matrix.cols*high)) reference =
    Qleisli.Semantics.Exact.entry matrix low input * joint changed reference
  rw [original]

/-- At one supported physical label, every contributing coefficient reads
the same source ordinal. The ordinal and physical label stay distinct. -/
theorem source_action_at_label {owners : Map} (frame : Frame owners) (unique : owners.Nodup)
    (selector target : Binding) (selectorMember : selector ∈ owners) (targetMember : target ∈ owners)
    (arms : List Matrix) (ordinal : Nat) (matrix : Matrix) (found : arms[ordinal]? = some matrix)
    (cols : matrix.cols = (ownerLayout target).labels.length)
    (rows : matrix.rows = (ownerLayout target).labels.length)
    (physicalFrame : List Nat) {Reference : Type} (joint : Nat → Reference → ℂ)
    (physical : Nat) (reference : Reference)
    (label : (ownerLayout selector).labels[ordinal]? =
      some (gather physical (selector.port.wires.map physicalFrame.idxOf))) :
    Qleisli.RuntimeSemanticForest.action frame physicalFrame
        (RuntimeSourceOrdinalAction.sourceAction owners selector target arms joint) physical reference =
      Qleisli.RuntimeSemanticForest.action frame physicalFrame
        (applySourceOwner owners owners target target matrix joint) physical reference := by
  have uniqueLabels := RuntimeCarrierLabels.layout_labels _ _ (owner_layout (frame.available selector selectorMember)).1
  unfold Qleisli.RuntimeSemanticForest.action
  apply Qleisli.Exact.sum_map_congr
  intro index present
  have bound := List.mem_range.mp present
  by_cases zero : scalar (embed physicalFrame owners frame.code physical index) = 0
  · simp only [zero,zero_mul]
  · have support := owner_support frame unique selector selectorMember physicalFrame physical index bound zero
    have selected : decode owners (sourceDimension owners) index selector = ordinal :=
      (List.getElem?_inj support.1 uniqueLabels).mp (support.2.trans label.symm)
    have inside := frame_dimension frame ▸ bound
    apply congrArg (fun value => scalar (embed physicalFrame owners frame.code physical index) * value)
    rw [target_update_at frame unique target targetMember matrix cols rows joint index reference bound]
    simp only [RuntimeSourceOrdinalAction.sourceAction,if_pos inside,selected,found]

/-- The original direct selection acts as the written source arm table
on every physical row and arbitrary reference. The complete owner codes
come from semantic layouts; only the actual local receipts are required. -/
theorem direct_selection_action
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {inputCode outputCode : Matrix} {selectorBits targetBits : Nat} {retained : Raw.Sector.Retained}
    (restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits selectorBits] [.bits targetBits]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained)
    {labels : List Nat} {arms : List Matrix}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (layouts : RuntimePureBody.SelectionLayouts selector.basis target.basis selectorBits targetBits labels)
    (table : RuntimeMultiwayGram.OrdinalTable inputCode outputCode retained.sectors labels arms)
    (before : Frame codes.owners.before.bindings) :
    ∃ trace : RuntimeSelectionTraceEvidence.TraceEvidence frame codes.owners selectorBits targetBits retained restricted,
    ∃ after : Frame codes.owners.transport.after.bindings,
    ∀ {Reference : Type} (joint : Nat → Reference → ℂ) (physical : Nat) (reference : Reference),
      events dependencies trace.traceResult.events
        (fun input => RuntimeSemanticForest.action before frame.interval.before.quantum.frame joint input reference)
        physical =
      RuntimeSemanticForest.action after frame.interval.after.quantum.frame
        (RuntimeSourceOrdinalAction.sourceAction codes.owners.transport.after.bindings
          codes.owners.returned.first codes.owners.returned.second arms joint) physical reference := by
  obtain ⟨trace,after,_,_⟩ := RuntimeSemanticSelectionGeometry.semantic_frames frame codes.owners restricted before
  obtain ⟨logicalTrace,logicalAction⟩ := logical_sector_action frame restricted codes layouts before
  obtain ⟨paddingTrace,paddingAction⟩ := padding_sector_action frame restricted codes.owners layouts before
  have logicalEvents : logicalTrace.traceResult.events = trace.traceResult.events :=
    congrArg Semantics.RawTrace.Prepared.events (Option.some.inj (logicalTrace.executed.symm.trans trace.executed))
  have paddingEvents : paddingTrace.traceResult.events = trace.traceResult.events :=
    congrArg Semantics.RawTrace.Prepared.events (Option.some.inj (paddingTrace.executed.symm.trans trace.executed))
  let all := codes.owners.transport.after.bindings
  let physicalFrame := frame.interval.after.quantum.frame
  let first := codes.owners.returned.first
  let second := codes.owners.returned.second
  let firstAxes := first.port.wires.map physicalFrame.idxOf
  let secondAxes := second.port.wires.map physicalFrame.idxOf
  have ordered := RuntimeSelectionPartition.order_values _ _ _ codes.owners.returned.ordered
  have firstMember : first ∈ all := ordered.1 (by simp [first])
  have secondMember : second ∈ all := ordered.1 (by simp [second])
  have owners : first.owner = selector ∧ second.owner = target := by
    simpa only [first,second,List.map_cons,List.map_nil,List.cons.injEq,and_true] using ordered.2
  have selectorLayout := native_owner_layout (after.available first firstMember)
    (congrArg (·.basis) owners.1) layouts.selectorRead
  have firstWidth : firstAxes.length = selectorBits := (List.length_map _).trans
    ((owner_layout (after.available first firstMember)).2.trans (congrArg Semantics.FiniteCarrier.Layout.bits selectorLayout))
  obtain ⟨targetLayout,targetReference,targetWidth,nativeInput,nativeOutput,_,_⟩ :=
    RuntimeFiniteTargetCode.target_codes frame codes layouts
  have actualTarget := (owner_layout (after.available second secondMember)).1
  rw [owners.2] at actualTarget
  have sameTarget := Option.some.inj (targetReference.symm.trans actualTarget)
  have secondWidth : secondAxes.length = targetBits := (List.length_map _).trans
    ((owner_layout (after.available second secondMember)).2.trans (sameTarget.symm ▸ targetWidth))
  have inputEncoding : inputCode = encoding (ownerLayout second) := nativeInput.trans (congrArg encoding sameTarget)
  have outputEncoding : outputCode = encoding (ownerLayout second) := nativeOutput.trans (congrArg encoding sameTarget)
  obtain ⟨axes,unique⟩ := returned_axes frame codes.owners
  have uniqueOwners := unique_bindings codes.owners.transport.after
  refine ⟨trace,after,?_⟩
  intro Reference joint physical reference
  let label := gather physical firstAxes
  let row := gather physical secondAxes
  by_cases supported : label ∈ labels
  · obtain ⟨index,inside,atIndex⟩ := List.getElem_of_mem supported
    let ordinal : Fin labels.length := ⟨index,inside⟩
    let matrix := table.arm ordinal
    have armFound : arms[ordinal.val]? = some matrix :=
      List.getElem?_eq_getElem (by rw [table.count]; exact ordinal.isLt)
    have labelAt : labels[ordinal.val] = label := atIndex
    have binding : NominalSector.LogicalBinding inputCode outputCode retained.sectors (label,matrix) matrix := by
      simpa only [labelAt,matrix] using table.arm_checked ordinal
    have cols : matrix.cols = (ownerLayout second).labels.length :=
      binding.2.1.trans (congrArg Matrix.cols inputEncoding)
    have rows : matrix.rows = (ownerLayout second).labels.length :=
      binding.2.2.1.trans (congrArg Matrix.cols outputEncoding)
    have outputRows : outputCode.rows = 2^targetBits :=
      (congrArg Matrix.rows nativeOutput).trans (congrArg (fun bits => 2^bits) targetWidth)
    have rowBound : row < outputCode.rows := by
      rw [outputRows,← secondWidth]
      exact RuntimeForestProduct.gather_bound physical secondAxes
    have coordinate : gather physical (forestAxes physicalFrame codes.owners.returned.toList) =
        pack selectorBits label row := by
      rw [axes,RuntimeForestProduct.gather_append,firstWidth]
      rfl
    have raw := logicalAction joint physical reference binding rowBound coordinate
    rw [logicalEvents] at raw
    have sameBase : scatter physical firstAxes label = physical :=
      RuntimeScatterTransport.scatter_gather physical firstAxes (List.nodup_append.mp unique).1
    change _ = Qleisli.Semantics.Exact.action outputCode
      (fun digit ref => action matrix
        (RuntimeSemanticSelectionFibre.targetFibre all second physicalFrame (scatter physical firstAxes label) joint)
        digit ref) row reference at raw
    rw [sameBase] at raw
    have selectedLabel : (ownerLayout first).labels[ordinal.val]? = some label := by
      rw [selectorLayout]
      change labels[ordinal.val]? = some label
      rw [List.getElem?_eq_getElem ordinal.isLt,labelAt]
    have source := source_action_at_label after uniqueOwners first second firstMember secondMember arms ordinal.val
      matrix armFound cols rows physicalFrame joint physical reference selectedLabel
    have target := target_update after uniqueOwners second secondMember physicalFrame matrix cols rows joint physical reference
    rw [source,target]
    exact raw.trans (congrArg (fun code => action code _ row reference) outputEncoding)
  · have raw := paddingAction joint physical reference supported
    rw [paddingEvents] at raw
    have padding : label ∉ (ownerLayout first).labels := by
      rw [selectorLayout]
      exact supported
    exact raw.trans (owner_padding_zero after uniqueOwners first firstMember physicalFrame _ physical reference padding).symm

#print axioms direct_selection_action
#print axioms target_update_at
#print axioms source_action_at_label
end Qleisli.RuntimeSemanticSelectionSource
