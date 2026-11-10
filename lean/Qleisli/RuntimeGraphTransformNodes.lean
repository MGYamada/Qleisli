import Qleisli.RuntimeGraphLocalNodes

/-! Independent coefficient laws for control, repeated action and
conjugation at their original operation occurrences.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeGraphTransformNodes
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite QleisliKernel.SourceTypes
open Semantics.Exact (Matrix Scalar)
open RuntimeOperationTree (Value Step)
open RuntimeGraphCoefficients (Coefficient Agrees dimension sequential shape shared_calculation)
open RuntimeGraphLocalNodes (adjoint)
open Qleisli.Semantics.Exact (entry scalar)

private def Entries (matrix : Matrix) (meaning : Coefficient) : Prop :=
  ∀ row col, row < matrix.rows → col < matrix.cols → meaning row col = entry matrix row col

private theorem product_entries {first second result : Matrix} {firstSource secondSource : Coefficient}
    (firstEntries : Entries first firstSource) (secondEntries : Entries second secondSource)
    (work left : Nat) (read : Exact.Matrix.compose second first work = (.ok result,left)) :
    Entries result (sequential second.cols firstSource secondSource) := by
  obtain ⟨inner,rows,cols,each⟩ := Qleisli.Exact.compose_meaning _ _ _ _ _ read
  intro row col rowBound colBound
  rw [rows] at rowBound
  rw [cols] at colBound
  rw [each row col rowBound colBound]
  unfold sequential
  apply Qleisli.Exact.sum_map_congr
  intro index present
  have inside := List.mem_range.mp present
  rw [secondEntries row index rowBound inside,firstEntries index col (inner ▸ inside) colBound]

noncomputable def control (operand : Coefficient) : Coefficient :=
  fun row col =>
    if row % 2 ≠ col % 2 then 0
    else if row % 2 = 0 then if row / 2 = col / 2 then 1 else 0
    else operand (row / 2) (col / 2)

private theorem controlled_entries {operand result : Matrix} {meaning : Coefficient}
    (entries : Entries operand meaning) (work left : Nat)
    (read : (OperationIRMeaning.controlled operand).run work = (.ok result,left)) :
    Entries result (control meaning) := by
  unfold OperationIRMeaning.controlled at read
  obtain ⟨_,_,square,rest⟩ := bind_success _ _ _ _ _ read
  obtain ⟨_,_,_,rest⟩ := bind_success _ _ _ _ _ rest
  obtain ⟨_,_,_,made⟩ := bind_success _ _ _ _ _ rest
  have equal := beq_iff_eq.mp (guard_success _ _ _ _ square).1
  let size := 2*operand.rows
  let values := fun index : Nat =>
    let row := index / size
    let col := index % size
    if row % 2 != col % 2 then Scalar.zero
    else if row % 2 == 0 then if row / 2 == col / 2 then Scalar.one else Scalar.zero
    else operand.entry (row / 2) (col / 2)
  have native : Exact.Matrix.make size size ((List.range (size*size)).map values) = .ok result :=
    arithmetic_success _ _ (lift_success _ _ _ _ made).1
  obtain ⟨same,positive,_,_⟩ := Qleisli.Exact.matrix_make_result _ _ _ _ native
  intro row col rowBound colBound
  rw [same] at rowBound colBound ⊢
  have outputBound : row < size := rowBound
  have inputBound : col < size := colBound
  have output : row / 2 < operand.rows :=
    Nat.div_lt_of_lt_mul (by simpa only [size,Nat.mul_comm] using outputBound)
  have input : col / 2 < operand.cols := by
    rw [← equal]
    exact Nat.div_lt_of_lt_mul (by simpa only [size,Nat.mul_comm] using inputBound)
  have coefficient := Qleisli.Exact.matrix_entry_of_meanings size size _ (scalar ∘ values)
    row col outputBound inputBound (by rw [List.map_map])
  rw [coefficient]
  have quotient : (row*size+col)/size = row := by
    rw [Nat.add_comm,Nat.add_mul_div_right col row positive,Nat.div_eq_of_lt inputBound,Nat.zero_add]
  have residue : (row*size+col)%size = col := by simp only [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt inputBound]
  dsimp only [Function.comp_def,values]
  rw [quotient,residue]
  unfold control
  simp only [bne_iff_ne,beq_iff_eq]
  by_cases different : row % 2 ≠ col % 2
  · simp only [if_pos different,Qleisli.Exact.scalar_zero_meaning]
  · simp only [if_neg different]
    by_cases inactive : row % 2 = 0
    · simp only [if_pos inactive]
      by_cases same : row/2 = col/2
      · simp only [if_pos same,Qleisli.Exact.scalar_one_meaning]
      · simp only [if_neg same,Qleisli.Exact.scalar_zero_meaning]
    · simp only [if_neg inactive]
      exact entries _ _ output input

theorem controlled_step {artifact catalogue context description graph order occurrence root demand before}
    (step : @Step artifact catalogue context description graph order occurrence root demand before)
    {childIndex : Nat} (written : step.node = .controlled childIndex)
    {child : Value} (children : step.children = [child])
    {source : Coefficient} (agrees : Agrees child source) :
    Agrees step.output (control source) := by
  obtain ⟨work,left,read⟩ := step.calculated
  have original : (OperationIRMeaning.readNode occurrence.result (.controlled childIndex) [child.action]
      step.provider.actions 0).run work = (.ok (step.value,step.consumedProviders),left) := by
    simpa only [written,children,List.map_cons,List.map_nil] using read
  obtain ⟨_,calculated⟩ := shared_calculation occurrence.result
    (do pure (← OperationIRMeaning.controlled child.action,0)) _ _ _ _ original
  obtain ⟨matrix,middle,controlled,returned⟩ := bind_success _ _ _ _ _ calculated
  have same : step.value = matrix := congrArg Prod.fst (pure_success _ _ _ _ returned).1
  refine ⟨(shape step).1,(shape step).2,?_⟩
  change Entries step.value (control source)
  rw [same]
  exact controlled_entries agrees.coefficient work middle controlled

noncomputable def repeatFrom (size : Nat) (operand : Coefficient) : Nat → Coefficient → Coefficient
  | 0,initial => initial
  | count+1,initial => repeatFrom size operand count (sequential size initial operand)

noncomputable def repeatedAction (size : Nat) (operand : Coefficient) (count : Nat) : Coefficient :=
  repeatFrom size operand count (fun row col => if row = col then 1 else 0)

private def nativeRepeat (operand : Matrix) : Nat → Matrix → WorkM Matrix :=
  Nat.rec pure (fun _ next accumulated => do
    let accumulated ← exactWork (Exact.Matrix.composeWork operand accumulated)
    next accumulated)

private theorem repeat_entries {operand initial result : Matrix} {meaning initialMeaning : Coefficient}
    (count work left : Nat) (input : Entries operand meaning) (starting : Entries initial initialMeaning)
    (read : (nativeRepeat operand count initial).run work = (.ok result,left)) :
    Entries result (repeatFrom operand.cols meaning count initialMeaning) := by
  induction count generalizing initial work initialMeaning with
  | zero =>
    have same : result = initial := (pure_success _ _ _ _ read).1
    exact same.symm ▸ starting
  | succ count ih =>
    change (do
      let next ← exactWork (Exact.Matrix.composeWork operand initial)
      nativeRepeat operand count next).run work = (.ok result,left) at read
    obtain ⟨next,middle,composed,rest⟩ := bind_success _ _ _ _ _ read
    have product := product_entries starting input work middle (exactWork_success _ _ _ _ composed)
    exact ih middle product rest

theorem power_step {artifact catalogue context description graph order occurrence root demand before}
    (step : @Step artifact catalogue context description graph order occurrence root demand before)
    {childIndex count : Nat} (written : step.node = .power childIndex count)
    {child : Value} (children : step.children = [child])
    {source : Coefficient} (agrees : Agrees child source) :
    Agrees step.output (repeatedAction (dimension child.input) source count) := by
  obtain ⟨work,left,read⟩ := step.calculated
  have original : (OperationIRMeaning.readNode occurrence.result (.power childIndex count) [child.action]
      step.provider.actions 0).run work = (.ok (step.value,step.consumedProviders),left) := by
    simpa only [written,children,List.map_cons,List.map_nil] using read
  obtain ⟨_,calculated⟩ := shared_calculation occurrence.result
    (do pure (← OperationIRMeaning.power child.action count,0)) _ _ _ _ original
  obtain ⟨matrix,finished,powered,returned⟩ := bind_success _ _ _ _ _ calculated
  have same : step.value = matrix := congrArg Prod.fst (pure_success _ _ _ _ returned).1
  unfold OperationIRMeaning.power at powered
  obtain ⟨_,_,_,rest⟩ := bind_success _ _ _ _ _ powered
  obtain ⟨_,_,_,rest⟩ := bind_success _ _ _ _ _ rest
  obtain ⟨initial,middle,identityRead,repeated⟩ := bind_success _ _ _ _ _ rest
  have identity := arithmetic_success _ _ (lift_success _ _ _ _ identityRead).1
  obtain ⟨_,rows,cols,each⟩ := Qleisli.Exact.identity_meaning _ _ identity
  have initialEntries : Entries initial (fun row col => if row = col then 1 else 0) :=
    fun row col rowBound colBound => (each row col (rows ▸ rowBound) (cols ▸ colBound)).symm
  have final := repeat_entries count middle finished agrees.coefficient initialEntries repeated
  rw [agrees.cols] at final
  refine ⟨(shape step).1,(shape step).2,?_⟩
  change Entries step.value (repeatedAction (dimension child.input) source count)
  rw [same]
  exact final

theorem conjugate_step {artifact catalogue context description graph order occurrence root demand before}
    (step : @Step artifact catalogue context description graph order occurrence root demand before)
    {outerIndex middleIndex : Nat} (written : step.node = .conjugate outerIndex middleIndex)
    {outer middle : Value} (children : step.children = [outer,middle])
    {outerSource middleSource : Coefficient} (outerAgrees : Agrees outer outerSource)
    (middleAgrees : Agrees middle middleSource) :
    Agrees step.output (sequential (dimension outer.input)
      (sequential (dimension middle.input) (adjoint outerSource) middleSource) outerSource) := by
  obtain ⟨work,left,read⟩ := step.calculated
  have original : (OperationIRMeaning.readNode occurrence.result (.conjugate outerIndex middleIndex)
      [outer.action,middle.action] step.provider.actions 0).run work =
      (.ok (step.value,step.consumedProviders),left) := by
    simpa only [written,children,List.map_cons,List.map_nil] using read
  obtain ⟨_,calculated⟩ := shared_calculation occurrence.result (do
    let adj ← exactWork (Exact.Matrix.adjointWork outer.action)
    let inner ← exactWork (Exact.Matrix.composeWork middle.action adj)
    pure (← exactWork (Exact.Matrix.composeWork outer.action inner),0)) _ _ _ _ original
  obtain ⟨adj,first,readAdj,rest⟩ := bind_success _ _ _ _ _ calculated
  obtain ⟨inner,second,readInner,rest⟩ := bind_success _ _ _ _ _ rest
  obtain ⟨matrix,_,readOuter,returned⟩ := bind_success _ _ _ _ _ rest
  have same : step.value = matrix := congrArg Prod.fst (pure_success _ _ _ _ returned).1
  obtain ⟨rows,cols,each⟩ := Qleisli.Exact.adjoint_meaning _ _ _ _ (exactWork_success _ _ _ _ readAdj)
  have adjointEntries : Entries adj (adjoint outerSource) := by
    intro row col rowBound colBound
    change star (outerSource col row) = entry adj row col
    rw [each row col (rows ▸ rowBound) (cols ▸ colBound),
      outerAgrees.coefficient col row (cols ▸ colBound) (rows ▸ rowBound)]
  have innerEntries := product_entries adjointEntries middleAgrees.coefficient _ _
    (exactWork_success _ _ _ _ readInner)
  have final := product_entries innerEntries outerAgrees.coefficient _ _ (exactWork_success _ _ _ _ readOuter)
  rw [outerAgrees.cols,middleAgrees.cols] at final
  refine ⟨(shape step).1,(shape step).2,?_⟩
  change Entries step.value (sequential (dimension outer.input)
    (sequential (dimension middle.input) (adjoint outerSource) middleSource) outerSource)
  rw [same]
  exact final

#print axioms controlled_step
#print axioms power_step
#print axioms conjugate_step
end Qleisli.RuntimeGraphTransformNodes
