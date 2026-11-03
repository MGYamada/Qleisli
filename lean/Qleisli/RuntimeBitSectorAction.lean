import Qleisli.RawActionLocality
import Qleisli.NominalSectorAction
import Qleisli.RuntimeForestProduct
import QleisliKernel.Qirf.RuntimePureBody

/-! A source-bound Bit-target sector acting inside the actual caller forest.
Both target encodings are the producer's retained ownerCode computations.
The complete input forest is pulled through the actual ordered selected axes;
its amplitudes, spectators and external reference remain arbitrary. The same
literal tape and indexed nominal equation supply the phase-sensitive action.
This proves neither a full output-forest logical equation nor Gram transfer,
bounded-input availability, arbitrary padded-target factorization or acceptance.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeBitSectorAction
open QleisliKernel QleisliKernel.Semantics.Exact
open QleisliKernel.Semantics.Finite (gather scatter width)
open QleisliKernel.FiniteRestriction (pack)
open QleisliKernel.Qirf QleisliKernel.Qirf.RuntimeForestCode
open Qleisli.Semantics.Exact Qleisli.RuntimeForestProduct

theorem bit_code {port : Semantics.Raw.Port} {code : Matrix}
    (read : RuntimeInterval.Computed (Carrier.ownerCode [⟨port,[.bit]⟩]) code) :
    code = QleisliKernel.Semantics.FiniteCarrier.encoding ⟨1,[0,1]⟩ := by
  obtain ⟨work,left,ran⟩ := read
  obtain ⟨⟨before,after,codeRead⟩,_owners⟩ := Carrier.ownerCode_conditions _ _ work left ran
  obtain ⟨layout,_gramBefore,_gramAfter,original,same,_gram⟩ :=
    QleisliKernel.FiniteCarrier.code_conditions _ _ before after codeRead
  change some (⟨1,[0,1]⟩ : QleisliKernel.Semantics.FiniteCarrier.Layout) = some layout at original
  have equal := Option.some.inj original
  rw [← equal] at same
  exact same

private theorem bit_action {Reference : Type} {port : Semantics.Raw.Port} {code : Matrix}
    (read : RuntimeInterval.Computed (Carrier.ownerCode [⟨port,[.bit]⟩]) code)
    (joint : Nat → Reference → ℂ) (row : Nat) (reference : Reference) (bound : row < 2) :
    action code joint row reference = joint row reference := by
  rw [bit_code read]
  let identity := QleisliKernel.Semantics.FiniteCarrier.encoding (⟨1,[0,1]⟩ :
    QleisliKernel.Semantics.FiniteCarrier.Layout)
  have original : QleisliKernel.Exact.Matrix.identity 2 = .ok identity := by rfl
  have entries := (Qleisli.Exact.identity_meaning 2 identity original).2.2.2
  change ((List.range 2).map fun col => entry identity row col * joint col reference).sum = _
  have terms (col : Nat) (member : col ∈ List.range 2) :
      entry identity row col * joint col reference =
        if row = col then joint col reference else 0 := by
    rw [entries row col bound (List.mem_range.mp member)]
    split <;> simp
  exact (Qleisli.Exact.sum_map_congr _ _ _ terms).trans
    (Qleisli.Exact.range_delta_sum 2 row (fun col => joint col reference) bound)

/-- The actual indexed sector and the original target owner code supply the
selector bound and the exact column count used in the logical action. -/
theorem binding_bounds
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {retained : Raw.Sector.Retained}
    {restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits 1] [.bits 1]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained}
    {inputCode outputCode : Matrix}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (targetBasis : target.basis = [.bit])
    (literal : RuntimeLocalEvents.Literal frame 1 1 retained restricted
      codes.owners.before codes.owners.transport.after)
    {label required logical}
    (binding : QleisliKernel.Qirf.NominalSector.LogicalBinding
      inputCode outputCode retained.sectors (label,required) logical) :
    label < 2 ∧ required.cols = 2 := by
  obtain ⟨sector,found,_map,_same⟩ := Qleisli.NominalSector.logical_binding_map binding
  have inside := (List.getElem?_eq_some_iff.mp found).1
  have lengths := QleisliKernel.Exact.listRel_length _ _ _ literal.sectorReference.2.2.2.2.2.2.2
  rw [lengths,List.length_range] at inside
  have inputRead : RuntimeInterval.Computed
      (Carrier.ownerCode [⟨codes.owners.selected.second.port,[.bit]⟩]) inputCode := by
    simpa only [targetBasis] using codes.inputRead
  refine ⟨inside,?_⟩
  have original : logical = required := binding.1
  rw [← original,binding.2.1,bit_code inputRead]
  rfl

/-- A nonempty or empty actual local tape acts by its same nominal sector on
the Bit target slice of the entire source-coded caller state. The full joint
amplitudes are used directly, including every untouched owner and reference.
The coordinate premise identifies this output's actual ordered local axes; it
is not a factorization or separability assumption about those amplitudes. -/
theorem bit_target_sector_references {Reference : Type}
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {retained : Raw.Sector.Retained}
    {restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits 1] [.bits 1]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained}
    {inputCode outputCode : Matrix}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (targetBasis : target.basis = [.bit])
    (literal : RuntimeLocalEvents.Literal frame 1 1 retained restricted
      codes.owners.before codes.owners.transport.after)
    {label required logical}
    (binding : QleisliKernel.Qirf.NominalSector.LogicalBinding
      inputCode outputCode retained.sectors (label,required) logical)
    (joint : Nat → Reference → ℂ) (output row : Nat) (reference : Reference)
    (coordinate : gather output (forestAxes frame.interval.before.quantum.frame literal.selection.selected) =
      pack 1 label row)
    (rowBound : row < 2) :
    Qleisli.Semantics.RawAction.events dependencies literal.traceResult.events
        (fun physical => referenceAction literal.inputCode joint physical reference) output =
      action required (fun input ref => referenceAction literal.inputCode joint
        (scatter output (forestAxes frame.interval.before.quantum.frame literal.selection.selected)
          (pack 1 label input)) ref) row reference := by
  have inputRead : RuntimeInterval.Computed
      (Carrier.ownerCode [⟨codes.owners.selected.second.port,[.bit]⟩]) inputCode := by
    simpa only [targetBasis] using codes.inputRead
  have outputRead : RuntimeInterval.Computed
      (Carrier.ownerCode [⟨codes.owners.returned.second.port,[.bit]⟩]) outputCode := by
    simpa only [targetBasis] using codes.outputRead
  have read := literal.sectorReference
  have labelBound := (binding_bounds frame codes targetBasis literal binding).1
  obtain ⟨before,after,sectorsRead⟩ := read.2.2.2.2.2.2.1
  have valid := (QleisliKernel.FiniteRestriction.readSectors_bound _ _ _ _ _ before after sectorsRead).2.2.1
  have valid : retained.steps.all (QleisliKernel.Finite.stepValid dependencies 2) = true := by
    simpa only [width,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using valid
  let axes := forestAxes frame.interval.before.quantum.frame literal.selection.selected
  let pulled := fun input => referenceAction literal.inputCode joint (scatter output axes input) reference
  let family := fun selected input ref => referenceAction literal.inputCode joint
    (scatter output axes (pack 1 selected input)) ref
  have encoded : ∀ input, input < 2^2 → pulled input =
      Qleisli.NominalSector.encodedTargets (width [.bits 1]) inputCode family input reference := by
    intro input bound
    have highBound : input / 2 < 2 := by omega
    have encodedRow := bit_action inputRead (family (input % 2)) (input / 2) reference highBound
    change pulled input = action inputCode (family (input % 2)) (input / 2) reference
    rw [encodedRow]
    have packed : pack 1 (input % 2) (input / 2) = input := by
      change input % 2 + 2 * (input / 2) = input
      exact Nat.mod_add_div input 2
    change _ = referenceAction literal.inputCode joint
      (scatter output axes (pack 1 (input % 2) (input / 2))) reference
    rw [packed]
  have packedBound : pack 1 label row < 2^2 := by
    change label + 2 * row < 4
    omega
  have outputBound : row < outputCode.rows := by
    rw [bit_code outputRead]
    exact rowBound
  have sectorAction := Qleisli.NominalSector.read_logical_sector_action read binding family row reference outputBound
  have localized := congrFun (congrFun (Qleisli.Semantics.RawAction.Locality.literal_references literal
    (fun ref physical => referenceAction literal.inputCode joint physical ref)) reference) output
  calc
    _ = Qleisli.Semantics.RawAction.circuit dependencies retained.steps pulled
        (gather output axes) := localized
    _ = Qleisli.Semantics.RawAction.circuit dependencies retained.steps pulled
        (pack 1 label row) := by rw [coordinate]
    _ = Qleisli.Semantics.RawAction.circuit dependencies retained.steps
        (fun input => Qleisli.NominalSector.encodedTargets (width [.bits 1]) inputCode family input reference)
        (pack 1 label row) :=
      Qleisli.Finite.rawCircuit_congr dependencies 2 retained.steps _ _ valid encoded _ packedBound
    _ = action outputCode (fun value ref => action required (family label) value ref) row reference := sectorAction
    _ = action required (family label) row reference :=
      bit_action outputRead _ row reference rowBound

#print axioms bit_target_sector_references

end Qleisli.RuntimeBitSectorAction
