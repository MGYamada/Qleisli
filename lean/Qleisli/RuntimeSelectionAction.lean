import Qleisli.RuntimeTargetScatter

/-! Logical action of a checked selection in the original caller order.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeSelectionAction
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Semantics.Exact
open RuntimeForestCode
open QleisliKernel.Semantics.Finite (gather)
open QleisliKernel.FiniteRestriction (pack)
open Qleisli.Semantics.Exact Qleisli.RuntimeForestProduct

/-- Move a local matrix action inside the caller's encoding sum while retaining
every external reference index. Both sums use total complex coefficients. -/
theorem reference_sum {roles state checked} (code : @Frame roles state checked)
    (matrix : Matrix) {Reference : Type} (family : Nat → Nat → Reference → ℂ)
    (physical row : Nat) (reference : Reference) :
    action matrix (fun col ref => referenceAction code (family col) physical ref) row reference =
      referenceAction code (fun logical ref => action matrix (fun col => family col logical) row ref)
        physical reference := by
  unfold action referenceAction
  simp only [← List.sum_map_mul_left]
  rw [Qleisli.Exact.sum_swap (List.range matrix.cols) (List.range code.code.dimension)]
  apply Qleisli.Exact.sum_map_congr
  intro logical _
  apply Qleisli.Exact.sum_map_congr
  intro col _
  exact mul_left_comm _ _ _

/-- The original selection interval and its indexed nominal arm act on the logical
target inside the entire returned code. The reference may be entangled with
any caller owner. The coordinate identifies the physical output sector. -/
theorem sector_action {Reference : Type}
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {retained : Raw.Sector.Retained}
    {restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits 1] [.bits 1]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained}
    {inputCode outputCode : Matrix}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (selectorBasis : selector.basis = [.bit]) (targetBasis : target.basis = [.bit])
    (literal : RuntimeLocalEvents.Literal frame 1 1 retained restricted codes.owners.before codes.owners.transport.after)
    (form : Qleisli.RuntimeOwnerTransitionAction.SelectionForm frame codes.owners)
    {label required logical}
    (binding : QleisliKernel.Qirf.NominalSector.LogicalBinding inputCode outputCode retained.sectors (label,required) logical)
    (joint : Nat → Reference → ℂ) (physical row : Nat) (reference : Reference)
    (coordinate : gather physical (forestAxes frame.interval.after.quantum.frame codes.owners.returned.toList) =
      pack 1 label row) (rowBound : row < 2) :
    Qleisli.Semantics.RawAction.events dependencies literal.traceResult.events
        (fun input => referenceAction literal.inputCode joint input reference) physical =
      referenceAction literal.outputCode (fun index ref =>
        action required (fun col => joint (RuntimeTargetDigit.update literal.outputCode
          codes.owners.returned.second index col)) row ref) physical reference := by
  rw [Qleisli.RuntimeOwnerTransitionAction.bit_target_selection_output frame codes targetBasis literal
    form binding joint physical row reference coordinate rowBound]
  let family := fun col index => joint (RuntimeTargetDigit.update literal.outputCode codes.owners.returned.second index col)
  have bounds := Qleisli.RuntimeBitSectorAction.binding_bounds frame codes targetBasis literal binding
  refine Eq.trans ?_ (reference_sum literal.outputCode required family physical row reference)
  unfold action
  apply Qleisli.Exact.sum_map_congr
  intro col member
  have small := List.mem_range.mp member
  rw [bounds.2] at small
  exact congrArg (fun value : ℂ => entry required row col * value)
    (Qleisli.RuntimeTargetScatter.target_scatter_references frame codes selectorBasis targetBasis literal
      joint physical label row col reference coordinate bounds.1 rowBound small)

theorem quantumIf_sector {Reference : Type}
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {retained : Raw.Sector.Retained}
    {restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits 1] [.bits 1]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained}
    {inputCode outputCode : Matrix}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (selectorBasis : selector.basis = [.bit]) (targetBasis : target.basis = [.bit])
    (literal : RuntimeLocalEvents.Literal frame 1 1 retained restricted codes.owners.before codes.owners.transport.after)
    (zero one : List Semantics.Raw.UnitaryStep)
    (original : frame.operations = [.quantumIf codes.owners.selected.first.port.token codes.owners.selected.second.port.token
      codes.owners.returned.first.port.token codes.owners.returned.second.port.token zero one])
    {label required logical}
    (binding : QleisliKernel.Qirf.NominalSector.LogicalBinding inputCode outputCode retained.sectors (label,required) logical)
    (joint : Nat → Reference → ℂ) (physical row : Nat) (reference : Reference)
    (coordinate : gather physical (forestAxes frame.interval.after.quantum.frame codes.owners.returned.toList) =
      pack 1 label row) (rowBound : row < 2) :
    Qleisli.Semantics.RawAction.events dependencies literal.traceResult.events
        (fun input => referenceAction literal.inputCode joint input reference) physical =
      referenceAction literal.outputCode (fun index ref =>
        action required (fun col => joint (RuntimeTargetDigit.update literal.outputCode
          codes.owners.returned.second index col)) row ref) physical reference := by
  exact sector_action frame codes selectorBasis targetBasis literal (.quantumIf zero one original)
    binding joint physical row reference coordinate rowBound

/-- The logical two-arm action in the original owner order. -/
noncomputable def logicalAction {roles state checked} (code : @Frame roles state checked)
    (selector target : RuntimeOwnerMap.Binding) (zero one : Matrix) {Reference : Type}
    (joint : Nat → Reference → ℂ) (index : Nat) (reference : Reference) : ℂ :=
  let digit := Qleisli.MixedRadix.decode checked.bindings (RuntimeOwnerCodeReindex.dimensionAt code.owners) index
  action (if digit selector = 0 then zero else one)
    (fun col => joint (RuntimeTargetDigit.update code target index col)) (digit target) reference

/-- On every physical output row, choose the actual indexed arm with the original
selector digit and apply it at the original target digit. -/
theorem caller_action {Reference : Type}
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {retained : Raw.Sector.Retained}
    {restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits 1] [.bits 1]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained}
    {inputCode outputCode : Matrix}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (selectorBasis : selector.basis = [.bit]) (targetBasis : target.basis = [.bit])
    (literal : RuntimeLocalEvents.Literal frame 1 1 retained restricted codes.owners.before codes.owners.transport.after)
    (form : Qleisli.RuntimeOwnerTransitionAction.SelectionForm frame codes.owners)
    {zeroArm oneArm zeroLogical oneLogical}
    (zeroChecked : QleisliKernel.Qirf.NominalSector.LogicalBinding inputCode outputCode retained.sectors (0,zeroArm) zeroLogical)
    (oneChecked : QleisliKernel.Qirf.NominalSector.LogicalBinding inputCode outputCode retained.sectors (1,oneArm) oneLogical)
    (joint : Nat → Reference → ℂ) (physical : Nat) (reference : Reference) :
    Qleisli.Semantics.RawAction.events dependencies literal.traceResult.events
        (fun input => referenceAction literal.inputCode joint input reference) physical =
      referenceAction literal.outputCode
        (logicalAction literal.outputCode codes.owners.returned.first codes.owners.returned.second zeroArm oneArm joint)
        physical reference := by
  unfold logicalAction
  let packed := gather physical (forestAxes frame.interval.after.quantum.frame codes.owners.returned.toList)
  let label := packed % 2
  let row := packed / 2
  have labelBound : label < 2 := Nat.mod_lt _ (by decide)
  have packedBound : packed < 4 :=
    Qleisli.RuntimeTargetScatter.returned_coordinate_bound frame codes selectorBasis targetBasis literal physical
  have rowBound : row < 2 := by dsimp [row]; omega
  have coordinate : packed = pack 1 label row := by
    change packed = packed % 2 + 2 * (packed / 2)
    omega
  have checked : QleisliKernel.Qirf.NominalSector.LogicalBinding inputCode outputCode retained.sectors
      (label,if label = 0 then zeroArm else oneArm) (if label = 0 then zeroLogical else oneLogical) := by
    by_cases low : label = 0
    · simpa only [low,if_pos rfl] using zeroChecked
    · have high : label = 1 := by omega
      simpa only [high,Nat.one_ne_zero,if_false] using oneChecked
  rw [sector_action frame codes selectorBasis targetBasis literal form checked joint physical row reference coordinate rowBound]
  unfold referenceAction
  apply Qleisli.Exact.sum_map_congr
  intro index member
  by_cases empty : scalar (literal.outputCode.embedding physical index) = 0
  · simp only [empty,zero_mul]
  · have digits := Qleisli.RuntimeTargetScatter.source_pair_support frame codes selectorBasis targetBasis literal
      physical index label row (List.mem_range.mp member) coordinate labelBound empty
    dsimp only
    rw [digits.1,digits.2]

theorem quantumIf_action {Reference : Type}
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {retained : Raw.Sector.Retained}
    {restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits 1] [.bits 1]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained}
    {inputCode outputCode : Matrix}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (selectorBasis : selector.basis = [.bit]) (targetBasis : target.basis = [.bit])
    (literal : RuntimeLocalEvents.Literal frame 1 1 retained restricted codes.owners.before codes.owners.transport.after)
    (zero one : List Semantics.Raw.UnitaryStep)
    (original : frame.operations = [.quantumIf codes.owners.selected.first.port.token codes.owners.selected.second.port.token
      codes.owners.returned.first.port.token codes.owners.returned.second.port.token zero one])
    {zeroArm oneArm zeroLogical oneLogical}
    (zeroChecked : QleisliKernel.Qirf.NominalSector.LogicalBinding inputCode outputCode retained.sectors (0,zeroArm) zeroLogical)
    (oneChecked : QleisliKernel.Qirf.NominalSector.LogicalBinding inputCode outputCode retained.sectors (1,oneArm) oneLogical)
    (joint : Nat → Reference → ℂ) (physical : Nat) (reference : Reference) :
    Qleisli.Semantics.RawAction.events dependencies literal.traceResult.events
        (fun input => referenceAction literal.inputCode joint input reference) physical =
      referenceAction literal.outputCode
        (logicalAction literal.outputCode codes.owners.returned.first codes.owners.returned.second zeroArm oneArm joint)
        physical reference := by
  exact caller_action frame codes selectorBasis targetBasis literal (.quantumIf zero one original)
    zeroChecked oneChecked joint physical reference

#print axioms caller_action
#print axioms quantumIf_action

#print axioms quantumIf_sector
end Qleisli.RuntimeSelectionAction
