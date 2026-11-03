import Qleisli.RuntimeMultiwayAction

/-! Actual rectangular target-code receipts for a finite source selection.
Unit, nominal records and padding retain their original carrier descriptions.
The same native input/output code runs and indexed sector products are used;
no identity-code surrogate, new Gram run or joined whole-mode matrix appears.
Caller target-fibre encoding and its global transport are separate lemmas.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeFiniteTargetCode
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Semantics.Exact
open QleisliKernel.Semantics.Finite (width)
open QleisliKernel.FiniteRestriction (pack)
open Qleisli.Semantics.Exact

/-- Extract the genuine independent carrier encoding and actual native Gram
receipt from an original single-owner code computation. -/
theorem owner_code_reference (basis : Semantics.FiniteCarrier.Basis) (port : Semantics.Raw.Port)
    (code : Matrix) (read : RuntimeInterval.Computed (Carrier.ownerCode [⟨port,basis⟩]) code) :
    ∃ layout : Semantics.FiniteCarrier.Layout,
      Semantics.FiniteCarrier.layout basis = some layout ∧
      code = Semantics.FiniteCarrier.encoding layout ∧
      ∃ before after, QleisliKernel.Exact.Matrix.isometry code before = (.ok true,after) := by
  obtain ⟨work,left,ran⟩ := read
  obtain ⟨⟨before,after,codeRead⟩,_owners⟩ := Carrier.ownerCode_conditions _ _ work left ran
  obtain ⟨layout,gramBefore,gramAfter,original,same,gram⟩ :=
    QleisliKernel.FiniteCarrier.code_conditions _ _ before after codeRead
  exact ⟨layout,original,same,gramBefore,gramAfter,gram⟩

/-- Both original target-code reads are the same carrier encoding, including
its true logical cardinality and physical padding. Their two native Gram runs
remain retained; an equality of dimensions supplies none of these facts. -/
theorem target_codes
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {inputCode outputCode selectorBits targetBits labels}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (layouts : RuntimePureBody.SelectionLayouts selector.basis target.basis selectorBits targetBits labels) :
    ∃ layout : Semantics.FiniteCarrier.Layout,
      Semantics.FiniteCarrier.layout target.basis = some layout ∧ layout.bits = targetBits ∧
      inputCode = Semantics.FiniteCarrier.encoding layout ∧
      outputCode = Semantics.FiniteCarrier.encoding layout ∧
      (∃ before after, QleisliKernel.Exact.Matrix.isometry inputCode before = (.ok true,after)) ∧
      (∃ before after, QleisliKernel.Exact.Matrix.isometry outputCode before = (.ok true,after)) := by
  obtain ⟨left,leftOriginal,inputSame,inputGram⟩ :=
    owner_code_reference target.basis codes.owners.selected.second.port inputCode codes.inputRead
  obtain ⟨right,rightOriginal,outputSame,outputGram⟩ :=
    owner_code_reference target.basis codes.owners.returned.second.port outputCode codes.outputRead
  have same : right = left := Option.some.inj (rightOriginal.symm.trans leftOriginal)
  subst right
  obtain ⟨targetLabels,work,remaining,ran⟩ := layouts.targetRead
  have native := QleisliKernel.FiniteCarrier.read_reference _ _ work remaining ran
  have layout : left = (⟨targetBits,targetLabels⟩ : Semantics.FiniteCarrier.Layout) :=
    Option.some.inj (leftOriginal.symm.trans native)
  exact ⟨left,leftOriginal,congrArg Semantics.FiniteCarrier.Layout.bits layout,
    inputSame,outputSame,inputGram,outputGram⟩

theorem target_shapes
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {inputCode outputCode selectorBits targetBits labels}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (layouts : RuntimePureBody.SelectionLayouts selector.basis target.basis selectorBits targetBits labels) :
    inputCode.rows = 2^targetBits ∧ outputCode.rows = 2^targetBits ∧ inputCode.cols = outputCode.cols := by
  obtain ⟨layout,_original,bits,inputSame,outputSame,_inputGram,_outputGram⟩ := target_codes frame codes layouts
  rw [inputSame,outputSame]
  exact ⟨congrArg (fun bits => 2^bits) bits,congrArg (fun bits => 2^bits) bits,rfl⟩

/-- The original local sector acts through the actual rectangular target
encoding on every physical row, including target padding. A one-dimensional
Unit target still retains the requested phase-sensitive matrix action. -/
theorem local_code_action {Reference : Type}
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {inputCode outputCode : Matrix} {selectorBits targetBits : Nat} {retained : Raw.Sector.Retained}
    {restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits selectorBits] [.bits targetBits]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained} {labels : List Nat}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (layouts : RuntimePureBody.SelectionLayouts selector.basis target.basis selectorBits targetBits labels)
    (literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
      codes.owners.before codes.owners.transport.after)
    {label required logical}
    (binding : QleisliKernel.Qirf.NominalSector.LogicalBinding inputCode outputCode retained.sectors (label,required) logical)
    (joint : Nat → Nat → Reference → ℂ) (row : Nat) (ref : Reference) (bound : row < 2^targetBits) :
    Qleisli.Semantics.RawAction.circuit dependencies retained.steps
        (fun coordinate => Qleisli.NominalSector.encodedTargets selectorBits inputCode joint coordinate ref)
        (pack selectorBits label row) =
      action outputCode (fun output reference => action required (joint label) output reference) row ref := by
  have rows := (target_shapes frame codes layouts).2.1
  have physicalBound : row < outputCode.rows := by rw [rows]; exact bound
  exact Qleisli.NominalSector.read_logical_sector_action literal.sectorReference binding joint row ref physicalBound

#print axioms owner_code_reference
#print axioms target_codes
#print axioms local_code_action

end Qleisli.RuntimeFiniteTargetCode
