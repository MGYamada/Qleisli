import Qleisli.RawActionSector
import Qleisli.CodeSpaceAction
import QleisliKernel.Qirf.NominalSector

/-! Exact complex action of the same reconstructed physical sector and its
checked nominal code equation. Every selector coordinate has an arbitrary
joint target/reference family; no separability or normalization is assumed.
The original bounded reconstruction, both composition receipts and Gram checks
remain premises. This does not establish source attribution, full caller-forest
factorization, final permutations or the complete runtime-root theorem.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.NominalSector
open QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite
open QleisliKernel.Qirf QleisliKernel.FiniteRestriction
open Qleisli.Semantics.Exact

/-- This is the existing checked logical map on the very same indexed physical
sector. Its shape follows from the two actual successful matrix products. -/
theorem logical_binding_map {inputCode outputCode : Matrix} {physical : List Matrix}
    {request : Nat × Matrix} {logical : Matrix}
    (binding : QleisliKernel.Qirf.NominalSector.LogicalBinding inputCode outputCode physical request logical) :
    ∃ sector, physical[request.1]? = some sector ∧
      ∃ checked : QleisliKernel.CodeSpace.Map inputCode outputCode sector, checked.logical = logical := by
  obtain ⟨_requested,columns,rows,_gram,sector,actual,a,b,c,d,found,left,right⟩ := binding
  have physicalShape := Qleisli.Exact.compose_meaning sector inputCode actual a b left
  have outputShape := Qleisli.Exact.compose_meaning outputCode logical actual c d right
  exact ⟨sector,found,⟨logical,⟨physicalShape.1,physicalShape.2.1.symm.trans outputShape.2.1⟩,
    ⟨columns,rows⟩,⟨actual,a,b,c,d,left,right⟩⟩,rfl⟩

private theorem indexed_sector {dependencies selector target steps sectors label sector}
    (bindings : QleisliKernel.Exact.ListRel
      (SectorEvaluationBinding dependencies selector target steps) (List.range (2^selector)) sectors)
    (found : sectors[label]? = some sector) :
    SectorEvaluationBinding dependencies selector target steps label sector := by
  obtain ⟨inside,value⟩ := List.getElem?_eq_some_iff.mp found
  have labelBound : label < (List.range (2^selector)).length := by
    rw [← QleisliKernel.Exact.listRel_length _ _ _ bindings]
    exact inside
  have binding := QleisliKernel.Exact.listRel_getElem _ _ _ bindings label labelBound
  simpa only [List.getElem_range,value] using binding

/-- Encode each target slice independently. The selector and untouched reference
may be entangled with that target and with each other. -/
def encodedTargets {Reference : Type} (selector : Nat) (inputCode : Matrix)
    (joint : Nat → Nat → Reference → ℂ) : Nat → Reference → ℂ :=
  fun coordinate reference => action inputCode (joint (coordinate % 2^selector))
    (coordinate / 2^selector) reference

/-- The actual original Raw restriction and nominal equation imply the exact
phase-sensitive action at this same label. No fresh native check, replaced
matrix, bounded input execution or omitted Gram check supplies the premise. -/
theorem read_logical_sector_action {Reference : Type}
    {dependencies selector target program retained inputCode outputCode label required logical}
    (read : QleisliKernel.Raw.Sector.ReadBinding dependencies selector target program retained)
    (binding : QleisliKernel.Qirf.NominalSector.LogicalBinding
      inputCode outputCode retained.sectors (label,required) logical)
    (joint : Nat → Nat → Reference → ℂ) (row : Nat) (reference : Reference)
    (bound : row < outputCode.rows) :
    Qleisli.Semantics.RawAction.circuit dependencies retained.steps
        (fun coordinate => encodedTargets (width selector) inputCode joint coordinate reference)
        (pack (width selector) label row) =
      action outputCode (fun output ref => action required (joint label) output ref) row reference := by
  obtain ⟨sector,found,checked,sameLogical⟩ := logical_binding_map binding
  have sectorBinding := indexed_sector read.2.2.2.2.2.2.2 found
  have rowBound : row < sector.rows := by
    rw [checked.physicalShape.2]
    exact bound
  have selected : (fun input ref =>
      encodedTargets (width selector) inputCode joint (pack (width selector) label input) ref) =
      (fun input ref => action inputCode (joint label) input ref) := by
    funext input ref
    simp only [encodedTargets,pack_low _ _ _ sectorBinding.1,pack_high _ _ _ sectorBinding.1]
  calc
    _ = action sector (fun input ref =>
        encodedTargets (width selector) inputCode joint (pack (width selector) label input) ref)
        row reference :=
      Qleisli.Semantics.RawAction.Sector.sector_binding_action dependencies (width selector)
        target retained.steps label sector sectorBinding
        (encodedTargets (width selector) inputCode joint) row reference rowBound
    _ = action sector (fun input ref => action inputCode (joint label) input ref) row reference := by
      rw [selected]
    _ = _ := by
      have meaning := Qleisli.CodeSpace.map_reference_action checked (joint label) row reference rowBound
      simpa only [sameLogical,binding.1] using meaning

/-- Every ordered requested logical label retains its own checked physical
sector and arbitrary-reference action, including noncontiguous nominal labels.
The actual successful checkLogicals result supplies every logical equation. -/
theorem checkLogicals_reference_actions {Reference : Type}
    {dependencies selector target program retained inputCode outputCode labels required actual work left}
    (read : QleisliKernel.Raw.Sector.ReadBinding dependencies selector target program retained)
    (checked : (QleisliKernel.Qirf.NominalSector.checkLogicals inputCode outputCode retained.sectors
      labels required).run work = (.ok actual,left))
    (joint : Nat → Nat → Reference → ℂ) :
    QleisliKernel.Exact.ListRel (fun (request : Nat × Matrix) (_logical : Matrix) =>
      ∀ row reference, row < outputCode.rows →
        Qleisli.Semantics.RawAction.circuit dependencies retained.steps
            (fun coordinate => encodedTargets (width selector) inputCode joint coordinate reference)
            (pack (width selector) request.1 row) =
          action outputCode (fun output ref => action request.2 (joint request.1) output ref) row reference)
      (labels.zip required) actual := by
  have bindings := (QleisliKernel.Qirf.NominalSector.checkLogicals_bound _ _ _ _ _ _ _ _ checked).2
  generalize requestsEq : labels.zip required = requests at bindings ⊢
  clear requestsEq checked
  induction requests generalizing actual with
  | nil => cases actual with
    | nil => trivial
    | cons first rest => cases bindings
  | cons request requests ih => cases actual with
    | nil => cases bindings
    | cons first rest =>
      exact ⟨fun row reference bound => read_logical_sector_action read bindings.1 joint row reference bound,
        ih bindings.2⟩

#print axioms logical_binding_map
#print axioms read_logical_sector_action
#print axioms checkLogicals_reference_actions

end Qleisli.NominalSector
