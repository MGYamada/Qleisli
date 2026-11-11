import Qleisli.RuntimePureProviderSourceAction

/-! Read the evaluated provider result in the original declared codomain.
The finite layout fixes the logical-to-physical labels without inspecting the
computed logical action or imposing a separate equality premise.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimePureProviderLogicalAction
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite QleisliKernel.SourceTypes
open Semantics.FiniteCarrier (Basis Layout layout encoding)
open RuntimeSelectionSteps (Edge)
open RuntimeSemanticForest (Frame)
open Qleisli.RuntimeLiteralBody
open Qleisli.RuntimePureProviderBoundary (packedAction)
open Qleisli.Semantics.Exact (action entry scalar)

theorem encoding_label {basis : Basis} {code : Layout} (read : layout basis = some code)
    {Reference : Type} (joint : Nat → Reference → ℂ) (ordinal : Fin code.labels.length)
    (reference : Reference) :
    action (encoding code) joint code.labels[ordinal.val] reference = joint ordinal.val reference := by
  let row := code.labels[ordinal.val]
  have physicalBound : row < 2^code.bits :=
    (RuntimeForestProduct.layout_bounds _ _ read).2 _ (List.getElem_mem _)
  have unique := RuntimeCarrierLabels.layout_labels _ _ read
  have atOrdinal : code.labels[ordinal.val]? = some row := List.getElem?_eq_getElem ordinal.isLt
  unfold action
  change ((List.range code.labels.length).map fun digit => entry (encoding code) row digit *
    joint digit reference).sum = _
  calc
    _ = ((List.range code.labels.length).map fun digit =>
        if ordinal.val = digit then joint digit reference else 0).sum := by
      apply Qleisli.Exact.sum_map_congr
      intro digit present
      have bounded := List.mem_range.mp present
      rw [← RuntimeForestProduct.encoding_coefficient _ _ _ physicalBound bounded]
      have selected : code.labels[digit]? = some row ↔ ordinal.val = digit := by
        constructor
        · intro found
          exact ((List.getElem?_inj bounded unique).mp (found.trans atOrdinal.symm)).symm
        · rintro rfl
          exact atOrdinal
      change scalar (if code.labels[digit]? == some row then _ else _) * joint digit reference =
        if ordinal.val = digit then joint digit reference else 0
      by_cases same : ordinal.val = digit <;>
        simp [beq_iff_eq,selected,same,Qleisli.Exact.scalar_one_meaning,Qleisli.Exact.scalar_zero_meaning]
    _ = _ := Qleisli.Exact.range_delta_sum _ _ _ ordinal.isLt

/-- The returned source operator, evaluated at the declared codomain's
original finite code labels, equals the checked logical provider matrix on
all logical rows. The matrix on the right does not define the source result. -/
theorem logical_execution {artifact context description graph index request header root demand}
    (checked : @RuntimeProviderAction.Checked artifact context description graph index request header root demand)
    (scope : List Edge) (joint : Nat → Nat → ℂ) :
    let native := checked.paths.ir.original
    let body := checked.originalBody.body
    let source : RuntimeStructuralAction.SourceState :=
      ⟨checked.originalBody.initial,header.original.body.checked.summary.parameterValues.flatMap
        SourceRuntimeValues.valueOwners,header.original.body.checked.summary.nextOwner⟩
    let initial : SourceHistory := ⟨source,[],[],joint,[]⟩
    ∃ code : Layout,
      layout native.prepared.ports.codomain = some code ∧ checked.action.rows = code.labels.length ∧
      ∃ result : SourceHistory, ∃ output : Frame body.result.history.bindings,
        runSourceHistories (pureRecursiveSourceSteps recursiveBodyLeaves 127 scope) [] body.result.steps
          [initial] = some [result] ∧
        ∀ (ordinal : Fin code.labels.length) column,
          packedAction output (returnHistory body.result.history.bindings result).operator
            code.labels[ordinal.val] column = action checked.action joint ordinal.val column := by
  intro native body source initial
  obtain ⟨code,original,codeEq,_⟩ := RuntimeFiniteTargetCode.owner_code_reference
    native.prepared.ports.codomain native.prepared.ports.output native.prepared.outputCode
    native.prepared.outputCodeRead
  obtain ⟨work,left,specified⟩ := native.prepared.equations.specifiedRead
  have shape := (Qleisli.Exact.compose_meaning native.prepared.outputCode checked.action
    native.prepared.equations.specified work left (exactWork_success _ _ _ _ specified)).1
  have dimension : checked.action.rows = code.labels.length :=
    shape.symm.trans (congrArg Semantics.Exact.Matrix.cols codeEq)
  obtain ⟨_,returned,result,output,_,returnMap,evaluated,physical⟩ :=
    RuntimePureProviderSourceAction.source_execution checked scope joint
  refine ⟨code,original,dimension,result,output,evaluated,?_⟩
  intro ordinal column
  have rowBound : code.labels[ordinal.val] < native.prepared.physical.rows := by
    have width := native.prepared.equations.physicalShape.2.trans (congrArg Semantics.Exact.Matrix.rows codeEq)
    rw [width]
    exact (RuntimeForestProduct.layout_bounds _ _ original).2 _ (List.getElem_mem _)
  have same := physical code.labels[ordinal.val] column rowBound
  rw [returnMap] at same
  exact same.trans ((congrArg (fun matrix => action matrix
    (fun row ref => action checked.action joint row ref) code.labels[ordinal.val] column) codeEq).trans
      (encoding_label original (fun row ref => action checked.action joint row ref) ordinal column))

#print axioms encoding_label
#print axioms logical_execution
end Qleisli.RuntimePureProviderLogicalAction
