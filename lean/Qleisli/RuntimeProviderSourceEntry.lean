import Qleisli.RuntimeProviderOccurrenceAction

/-! A provider coefficient is read from the original source evaluation on a
basis column and from the declared output layout. The checked result matrix
is not an argument of this evaluator.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeProviderSourceEntry
open QleisliKernel QleisliKernel.Qirf QleisliKernel.SourceTypes
open RuntimeSelectionSteps (Edge)
open RuntimeForestCode (sparseLayout forestBasis sparseEntry)
open Qleisli.RuntimeLiteralBody
open Qleisli.Semantics.Exact (entry action scalar)

private noncomputable def basisColumn (row column : Nat) : ℂ := if row = column then 1 else 0

noncomputable def evaluate {artifact root owner name signature program request bindings}
    {body : @SourceRuntimeTrace.Body artifact.sources owner name signature}
    (written : @RuntimePureBody.Checked artifact root owner name signature body program request bindings)
    (codomain : Semantics.FiniteCarrier.Basis) (scope : List Edge) (row column : Nat) : ℂ :=
  let source : RuntimeStructuralAction.SourceState :=
    ⟨bindings,body.checked.summary.parameterValues.flatMap SourceRuntimeValues.valueOwners,
      body.checked.summary.nextOwner⟩
  let initial : SourceHistory := ⟨source,[],[],basisColumn,[]⟩
  let returned := written.result.history.bindings
  (do
    let layout ← Semantics.FiniteCarrier.layout codomain
    let physical ← layout.labels[row]?
    let [result] ← runSourceHistories (pureRecursiveSourceSteps recursiveBodyLeaves 127 scope) []
      written.result.steps [initial] | none
    let code ← sparseLayout (forestBasis returned)
    let coefficients := (returnHistory returned result).operator
    return ((List.range code.dimension).map fun digit =>
      scalar (sparseEntry code physical digit) * coefficients digit column).sum).getD 0

theorem exact_entry {artifact context description graph index request header root demand}
    (checked : @RuntimeProviderAction.Checked artifact context description graph index request header root demand)
    {basis : Semantics.FiniteCarrier.Basis} (declared : header.original.supplied.provider.signature.outputs = [basis])
    (scope : List Edge) (row column : Nat) (rowBound : row < checked.action.rows)
    (colBound : column < checked.action.cols) :
    evaluate checked.originalBody.body basis scope row column = entry checked.action row column := by
  let native := checked.paths.ir.original
  obtain ⟨layout,original,rows,result,output,executed,each⟩ :=
    RuntimePureProviderLogicalAction.logical_execution checked scope basisColumn
  have same : basis = native.prepared.ports.codomain :=
    (List.cons.inj (declared.symm.trans native.prepared.ports.sourceOutputs)).1
  subst basis
  change Semantics.FiniteCarrier.layout native.prepared.ports.codomain = some layout at original
  have bounded : row < layout.labels.length := rows ▸ rowBound
  let ordinal : Fin layout.labels.length := ⟨row,bounded⟩
  have label : layout.labels[row]? = some layout.labels[ordinal.val] :=
    List.getElem?_eq_getElem bounded
  have sourceEq := each ordinal column
  have value : action checked.action basisColumn row column = entry checked.action row column := by
    unfold action
    calc
      _ = ((List.range checked.action.cols).map fun digit =>
          if column = digit then entry checked.action row digit else 0).sum := by
        apply Qleisli.Exact.sum_map_congr
        intro digit _
        by_cases same : column = digit
        · simp [basisColumn,same]
        · have different : digit ≠ column := Ne.symm same
          simp [basisColumn,same,different]
      _ = _ := Qleisli.Exact.range_delta_sum _ _ _ colBound
  calc
    _ = Qleisli.RuntimePureProviderBoundary.packedAction output
        (returnHistory checked.originalBody.body.result.history.bindings result).operator
        layout.labels[ordinal.val] column := by
      simp only [evaluate,original,label,executed,output.original,bind,Option.bind,pure,Option.getD_some,
        Qleisli.RuntimePureProviderBoundary.packedAction]
    _ = _ := sourceEq.trans value

#print axioms exact_entry
end Qleisli.RuntimeProviderSourceEntry
