import Qleisli.RuntimeProviderSourceEntry

/-! Coefficient semantics on the original operation stack. Native matrices
supply evidence of equality; source dimensions and the ordered source
operands specify the coefficient calculation.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeGraphCoefficients
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite QleisliKernel.SourceTypes
open Semantics.Exact (Matrix)
open RuntimeOperationTree (Value Step)
open Qleisli.Semantics.Exact (entry action)

abbrev Coefficient := Nat → Nat → ℂ

def dimension (basis : Semantics.FiniteCarrier.Basis) : Nat :=
  (Semantics.FiniteCarrier.dimension basis).getD 0

structure Agrees (value : Value) (source : Coefficient) : Prop where
  rows : value.action.rows = dimension value.output
  cols : value.action.cols = dimension value.input
  coefficient : ∀ row col, row < value.action.rows → col < value.action.cols →
    source row col = entry value.action row col

noncomputable def sequential (size : Nat) (first second : Coefficient) : Coefficient :=
  fun row col => ((List.range size).map fun mid => second row mid * first mid col).sum

noncomputable def tensor (lowRows lowCols : Nat) (low high : Coefficient) : Coefficient :=
  fun row col => low (row % lowRows) (col % lowCols) * high (row / lowRows) (col / lowCols)

theorem shape {artifact catalogue context description graph order occurrence root demand before}
    (step : @Step artifact catalogue context description graph order occurrence root demand before) :
    step.output.action.rows = dimension step.output.output ∧ step.output.action.cols = dimension step.output.input := by
  obtain ⟨work,left,read⟩ := step.calculated
  obtain ⟨input,output,_,_,_,_,_,inputLayout,outputLayout,cols,rows⟩ :=
    OperationIRMeaning.readNode_shape _ _ _ _ _ _ _ work left read
  exact ⟨by simpa only [Step.output,dimension,Semantics.FiniteCarrier.dimension,outputLayout,
    Option.map_some,Option.getD_some] using rows,
    by simpa only [Step.output,dimension,Semantics.FiniteCarrier.dimension,inputLayout,
      Option.map_some,Option.getD_some] using cols⟩

theorem shared_calculation {sources} (metadata : StaticOperation.Result sources)
    (calculate : WorkM (Matrix × Nat)) (value : Matrix) (used work left : Nat)
    (read : (do
      let (matrix,count) ← calculate
      let input ← FiniteCarrier.read metadata.input
      let output ← FiniteCarrier.read metadata.output
      guard (matrix.cols == input.labels.length && matrix.rows == output.labels.length) .request
      pure (matrix,count) : WorkM (Matrix × Nat)).run work = (.ok (value,used),left)) :
    ∃ after, calculate.run work = (.ok (value,used),after) := by
  obtain ⟨⟨matrix,count⟩,after,ran,rest⟩ := bind_success _ _ _ _ _ read
  obtain ⟨_,_,_,rest⟩ := bind_success _ _ _ _ _ rest
  obtain ⟨_,_,_,rest⟩ := bind_success _ _ _ _ _ rest
  obtain ⟨_,_,_,returned⟩ := bind_success _ _ _ _ _ rest
  have same := (pure_success _ _ _ _ returned).1
  exact ⟨after,same.symm ▸ ran⟩

private theorem then_read {sources} (metadata : StaticOperation.Result sources) (leftIndex rightIndex : Nat)
    (first second : Matrix) (providers : List Matrix) (value : Matrix) (used work left : Nat)
    (read : (OperationIRMeaning.readNode metadata (.thenOp leftIndex rightIndex)
      [first,second] providers 0).run work = (.ok (value,used),left)) :
    ∃ before after, Exact.Matrix.compose second first before = (.ok value,after) := by
  obtain ⟨after,ran⟩ := shared_calculation metadata
    (do pure (← exactWork (Exact.Matrix.composeWork second first),0)) value used work left read
  obtain ⟨matrix,middle,composed,returned⟩ := bind_success _ _ _ _ _ ran
  have same : value = matrix := congrArg Prod.fst (pure_success _ _ _ _ returned).1
  exact ⟨work,middle,same.symm ▸ exactWork_success _ _ _ _ composed⟩

private theorem tensor_read {sources} (metadata : StaticOperation.Result sources) (leftIndex rightIndex : Nat)
    (first second : Matrix) (providers : List Matrix) (value : Matrix) (used work left : Nat)
    (read : (OperationIRMeaning.readNode metadata (.tensor leftIndex rightIndex)
      [first,second] providers 0).run work = (.ok (value,used),left)) :
    ∃ before after, Exact.Matrix.tensor first second before = (.ok value,after) := by
  obtain ⟨after,ran⟩ := shared_calculation metadata
    (do pure (← exactWork (Exact.Matrix.tensorWork first second),0)) value used work left read
  obtain ⟨matrix,middle,composed,returned⟩ := bind_success _ _ _ _ _ ran
  have same : value = matrix := congrArg Prod.fst (pure_success _ _ _ _ returned).1
  exact ⟨work,middle,same.symm ▸ exactWork_success _ _ _ _ composed⟩

/-- The two semantic operands are the two actual child stack entries in their
written order. The same graph index can appear in both positions. -/
theorem binary_children {artifact catalogue context description graph order occurrence root demand before}
    (step : @Step artifact catalogue context description graph order occurrence root demand before)
    {left right : Nat} (written : step.node.children = [left,right]) :
    ∃ first second, step.children = [first,second] ∧ first.index = left ∧ second.index = right := by
  have length := step.arity
  rw [written] at length
  have found : ∃ first second, step.children = [first,second] := ⟨_,_,List.eq_getElem_of_length_eq_two _ length⟩
  obtain ⟨first,second,children⟩ := found
  have indices := step.childIndices
  rw [written,children] at indices
  exact ⟨first,second,children,(List.cons.inj indices).1,(List.cons.inj (List.cons.inj indices).2).1⟩

theorem then_step {artifact catalogue context description graph order occurrence root demand before}
    (step : @Step artifact catalogue context description graph order occurrence root demand before)
    {leftIndex rightIndex : Nat} (written : step.node = .thenOp leftIndex rightIndex)
    {first second : Value} (children : step.children = [first,second])
    {left right : Coefficient} (leftAgrees : Agrees first left) (rightAgrees : Agrees second right) :
    Agrees step.output (sequential (dimension second.input) left right) := by
  obtain ⟨work,leftWork,read⟩ := step.calculated
  have original : (OperationIRMeaning.readNode occurrence.result (.thenOp leftIndex rightIndex)
      [first.action,second.action] step.provider.actions 0).run work = (.ok (step.value,step.consumedProviders),leftWork) := by
    simpa only [written,children,List.map_cons,List.map_nil] using read
  obtain ⟨a,b,composed⟩ := then_read _ _ _ _ _ _ _ _ _ _ original
  obtain ⟨inner,rows,cols,exact⟩ := Qleisli.Exact.compose_meaning second.action first.action step.value a b composed
  refine ⟨(shape step).1,(shape step).2,?_⟩
  intro row col rowBound colBound
  change row < step.value.rows at rowBound
  change col < step.value.cols at colBound
  rw [rows] at rowBound
  rw [cols] at colBound
  change sequential (dimension second.input) left right row col = entry step.value row col
  rw [exact row col rowBound colBound,← rightAgrees.cols]
  unfold sequential
  apply Qleisli.Exact.sum_map_congr
  intro middle member
  have inside := List.mem_range.mp member
  rw [rightAgrees.coefficient row middle rowBound inside,leftAgrees.coefficient middle col (inner ▸ inside) colBound]

theorem tensor_step {artifact catalogue context description graph order occurrence root demand before}
    (step : @Step artifact catalogue context description graph order occurrence root demand before)
    {leftIndex rightIndex : Nat} (written : step.node = .tensor leftIndex rightIndex)
    {first second : Value} (children : step.children = [first,second])
    {low high : Coefficient} (firstAgrees : Agrees first low) (secondAgrees : Agrees second high) :
    Agrees step.output (tensor (dimension first.output) (dimension first.input) low high) := by
  obtain ⟨work,leftWork,read⟩ := step.calculated
  have original : (OperationIRMeaning.readNode occurrence.result (.tensor leftIndex rightIndex)
      [first.action,second.action] step.provider.actions 0).run work = (.ok (step.value,step.consumedProviders),leftWork) := by
    simpa only [written,children,List.map_cons,List.map_nil] using read
  obtain ⟨a,b,composed⟩ := tensor_read _ _ _ _ _ _ _ _ _ _ original
  obtain ⟨rows,cols,exact⟩ := Qleisli.Exact.tensor_meaning first.action second.action step.value a b composed
  refine ⟨(shape step).1,(shape step).2,?_⟩
  intro row col rowBound colBound
  change row < step.value.rows at rowBound
  change col < step.value.cols at colBound
  change tensor (dimension first.output) (dimension first.input) low high row col = entry step.value row col
  rw [exact row col rowBound colBound,← firstAgrees.rows,← firstAgrees.cols]
  have rowsPos : 0 < first.action.rows := by
    by_contra nonpositive
    have zero : first.action.rows = 0 := by omega
    rw [rows,zero,Nat.zero_mul] at rowBound
    omega
  have colsPos : 0 < first.action.cols := by
    by_contra nonpositive
    have zero : first.action.cols = 0 := by omega
    rw [cols,zero,Nat.zero_mul] at colBound
    omega
  have highRow : row / first.action.rows < second.action.rows :=
    Nat.div_lt_of_lt_mul (rows ▸ rowBound)
  have highCol : col / first.action.cols < second.action.cols :=
    Nat.div_lt_of_lt_mul (cols ▸ colBound)
  unfold tensor
  rw [firstAgrees.coefficient _ _ (Nat.mod_lt _ rowsPos) (Nat.mod_lt _ colsPos),
    secondAgrees.coefficient _ _ highRow highCol]

#print axioms then_step
#print axioms tensor_step
end Qleisli.RuntimeGraphCoefficients
