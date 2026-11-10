import Qleisli.RuntimeGraphCoefficients

/-! Local exact laws for the original primitive, inverse and requested
operation occurrences, reusing the common stack correspondence.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeGraphLocalNodes
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite QleisliKernel.SourceTypes
open RuntimeOperationTree (Value Step)
open RuntimeGraphCoefficients (Coefficient Agrees shape shared_calculation)
open Qleisli.Semantics.Exact (entry)

noncomputable def adjoint (operand : Coefficient) : Coefficient :=
  fun row col => star (operand col row)

def primitiveMeaning (kind : OperationDescription.Primitive) (target : Semantics.FiniteCarrier.Basis) :
    Option Semantics.Exact.Matrix :=
  Semantics.PrimitiveOperator.meaning
    (match kind with | .h => .h | .globalPhaseEighth => .globalPhaseEighth) target

theorem unary_child {artifact catalogue context description graph order occurrence root demand before}
    (step : @Step artifact catalogue context description graph order occurrence root demand before)
    {childIndex : Nat} (written : step.node.children = [childIndex]) :
    ∃ child, step.children = [child] ∧ child.index = childIndex := by
  have length := step.arity
  rw [written] at length
  obtain ⟨child,found⟩ := List.length_eq_one_iff.mp length
  have indices := step.childIndices
  rw [found,written] at indices
  exact ⟨child,found,(List.cons.inj indices).1⟩

theorem inverse_step {artifact catalogue context description graph order occurrence root demand before}
    (step : @Step artifact catalogue context description graph order occurrence root demand before)
    {childIndex : Nat} (written : step.node = .inverse childIndex)
    {child : Value} (children : step.children = [child])
    {source : Coefficient} (agrees : Agrees child source) :
    Agrees step.output (adjoint source) := by
  obtain ⟨work,left,read⟩ := step.calculated
  have original : (OperationIRMeaning.readNode occurrence.result (.inverse childIndex) [child.action]
      step.provider.actions 0).run work = (.ok (step.value,step.consumedProviders),left) := by
    simpa only [written,children,List.map_cons,List.map_nil] using read
  obtain ⟨finished,calculated⟩ := shared_calculation occurrence.result
    (do pure (← exactWork (Exact.Matrix.adjointWork child.action),0)) _ _ _ _ original
  obtain ⟨matrix,middle,readAdjoint,returned⟩ := bind_success _ _ _ _ _ calculated
  have same : step.value = matrix := congrArg Prod.fst (pure_success _ _ _ _ returned).1
  have ran := exactWork_success _ _ _ _ readAdjoint
  obtain ⟨rows,cols,each⟩ := Qleisli.Exact.adjoint_meaning _ _ _ _ ran
  refine ⟨(shape step).1,(shape step).2,?_⟩
  intro row col rowBound colBound
  change row < step.value.rows at rowBound
  change col < step.value.cols at colBound
  rw [same,rows] at rowBound
  rw [same,cols] at colBound
  change star (source col row) = entry step.value row col
  rw [same,each row col rowBound colBound,agrees.coefficient col row colBound rowBound]

theorem requested_step {artifact catalogue context description graph order occurrence root demand before}
    (step : @Step artifact catalogue context description graph order occurrence root demand before)
    {childIndex : Nat} {moduleName declarationName : String}
    (written : step.node = .requested childIndex moduleName declarationName)
    {child : Value} (children : step.children = [child])
    {source : Coefficient} (agrees : Agrees child source) :
    Agrees step.output source := by
  obtain ⟨work,left,read⟩ := step.calculated
  have original : (OperationIRMeaning.readNode occurrence.result (.requested childIndex moduleName declarationName)
      [child.action] step.provider.actions 0).run work = (.ok (step.value,step.consumedProviders),left) := by
    simpa only [written,children,List.map_cons,List.map_nil] using read
  obtain ⟨_,returned⟩ := shared_calculation occurrence.result (pure (child.action,0)) _ _ _ _ original
  have same : step.value = child.action := congrArg Prod.fst (pure_success _ _ _ _ returned).1
  refine ⟨(shape step).1,(shape step).2,?_⟩
  intro row col rowBound colBound
  change row < step.value.rows at rowBound
  change col < step.value.cols at colBound
  rw [same] at rowBound colBound
  change source row col = entry step.value row col
  rw [same]
  exact agrees.coefficient row col rowBound colBound

theorem primitive_step {artifact catalogue context description graph order occurrence root demand before}
    (step : @Step artifact catalogue context description graph order occurrence root demand before)
    {kind : OperationDescription.Primitive} {target : Semantics.FiniteCarrier.Basis}
    (written : step.node = .primitive kind target) (children : step.children = []) :
    ∃ matrix, primitiveMeaning kind target = some matrix ∧ Agrees step.output (entry matrix) := by
  obtain ⟨work,left,read⟩ := step.calculated
  have original : (OperationIRMeaning.readNode occurrence.result (.primitive kind target)
      [] step.provider.actions 0).run work = (.ok (step.value,step.consumedProviders),left) := by
    simpa only [written,children,List.map_nil] using read
  obtain ⟨after,calculated⟩ := shared_calculation occurrence.result
    (do pure (← OperationIRMeaning.primitive kind target,0)) _ _ _ _ original
  obtain ⟨matrix,middle,primitive,returned⟩ := bind_success _ _ _ _ _ calculated
  have same : step.value = matrix := congrArg Prod.fst (pure_success _ _ _ _ returned).1
  unfold OperationIRMeaning.primitive at primitive
  obtain ⟨_,_,_,rest⟩ := bind_success _ _ _ _ _ primitive
  obtain ⟨_,_,_,value⟩ := bind_success _ _ _ _ _ rest
  have found : readOption (primitiveMeaning kind target) = .ok matrix :=
    (lift_success _ _ _ _ value).1
  have denoted : primitiveMeaning kind target = some matrix := by
    cases lookup : primitiveMeaning kind target with
    | none => simp [readOption,lookup] at found
    | some original => simpa [readOption,lookup] using congrArg some found
  refine ⟨matrix,denoted,⟨(shape step).1,(shape step).2,?_⟩⟩
  intro row col _ _
  change entry matrix row col = entry step.value row col
  rw [same]

/-- Choose the formal's written actual by the name in its original header.
The resulting position is used on this occurrence's ordered children. -/
def formalSourcePosition {sources} (metadata : StaticOperation.Result sources)
    (operations : List (String × Nat)) (ordinal : Nat) : Option Nat := do
  let owner ← metadata.formal
  match owner.signature.instantiation with
  | .closed _ => none
  | .static _ environment _ =>
    let formal ← environment.numeric.original.header.formals[ordinal]?
    pure ((operations.map (·.1)).idxOf formal.name)

theorem formal_step {artifact catalogue context description graph order occurrence root demand before}
    (step : @Step artifact catalogue context description graph order occurrence root demand before)
    {moduleName declarationName : String} {bases : List (String × Semantics.FiniteCarrier.Basis)}
    {naturals operations : List (String × Nat)} {ordinal : Nat}
    (written : step.node = .formal moduleName declarationName bases naturals operations ordinal) :
    ∃ position child,
      formalSourcePosition occurrence.result operations ordinal = some position ∧
      step.children[position]? = some child ∧ step.value = child.action := by
  obtain ⟨work,left,read⟩ := step.calculated
  have original : (OperationIRMeaning.readNode occurrence.result
      (.formal moduleName declarationName bases naturals operations ordinal)
      (step.children.map (·.action)) step.provider.actions 0).run work =
        (.ok (step.value,step.consumedProviders),left) := by
    simpa only [written] using read
  obtain ⟨_,owner,arguments,environment,sameOriginal,formal,position,present,instantiation,header,_,selected,_,_,matrix⟩ :=
    OperationIRMeaning.readNode_formal_selection occurrence.result moduleName declarationName bases naturals
      operations ordinal _ _ _ _ _ _ _ original
  have atSource : formalSourcePosition occurrence.result operations ordinal = some position := by
    unfold formalSourcePosition
    simp only [present,bind,Option.bind,instantiation,header,pure,selected]
  rw [List.getElem?_map] at matrix
  cases lookup : step.children[position]? with
  | none => simp only [lookup,Option.map_none] at matrix; cases matrix
  | some child =>
    have chosen : child.action = step.value := by
      simpa only [lookup,Option.map_some,Option.some.injEq] using matrix
    exact ⟨position,child,atSource,lookup,chosen.symm⟩

#print axioms formal_step
#print axioms inverse_step
#print axioms requested_step
#print axioms primitive_step
end Qleisli.RuntimeGraphLocalNodes
