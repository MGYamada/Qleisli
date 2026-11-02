import QleisliKernel.SourceTypes.SourceRuntimeValues
import QleisliKernel.OrdinaryDomain

/-! Complete finite injectivity of an original coherent basis body.
Every coherent input and every captured ordinary valuation is enumerated from
the independent finite carrier. Producer-selected samples cannot certify it.
Actual source/native operator, code-space and reference equations remain required.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceBasisFunction
open QleisliKernel QleisliKernel.SourceTypes SourceRuntimeValues
open Semantics.FiniteCarrier

private def adapt {α : Type} (action : Except String α) : Finite.WorkM α :=
  Finite.lift (action.mapError fun _ => .request)

def boundValue (basis : Basis) : Except String (Value × List Basis) := do
  let (values,_,_) ← seedValues [(⟨Semantics.RuntimeType.ordinary basis,[]⟩ : RuntimeSignature.Part #[])]
  let [value] := values | throw "coherent basis input shape"
  let value ← value.mapM fun atom => match atom with
    | .ordinary basis (.input ordinal) => pure (.ordinary basis (.basisInput ordinal))
    | .tuple arity => pure (.tuple arity)
    | _ => throw "coherent basis input contains a quantum owner"
  return (value,(ordinary value).map Prod.fst)

private def freeVariables (inputTypes boundTypes : List Basis) : Expression →
    Except String (List (Expression × Basis))
  | .input ordinal => do
    let some basis := inputTypes[ordinal]? | throw "unknown captured ordinary input"
    return [(.input ordinal,basis)]
  | .basisInput ordinal => do
    let some _ := boundTypes[ordinal]? | throw "unknown coherent basis input"
    return []
  | expression@(.measured ..) => pure [(expression,[.bit])]
  | .unit | .bit _ | .ordinal _ => pure []
  | .project .. => throw "coherent nominal field projection needs its original field contract"
  | .not value | .field _ _ value => freeVariables inputTypes boundTypes value
  | .xor first second | .and first second | .combine _ first second => do
    return (← freeVariables inputTypes boundTypes first) ++ (← freeVariables inputTypes boundTypes second)
  | .choose condition thenValue elseValue => do
    return (← freeVariables inputTypes boundTypes condition) ++
      (← freeVariables inputTypes boundTypes thenValue) ++ (← freeVariables inputTypes boundTypes elseValue)

private def labels (bases : List Basis) (bits : List Bool) : Except String (List Nat) := do
  let (values,rest) ← bases.foldlM (fun (values,rest) basis => do
    let some layout := Semantics.FiniteCarrier.layout basis | throw "ordinary finite layout"
    if rest.length < layout.bits then throw "ordinary finite assignment width"
    let code := Semantics.OrdinaryValue.littleEndian (rest.take layout.bits)
    let ordinal := layout.labels.idxOf code
    if ordinal ≥ layout.labels.length then throw "ordinary assignment outside logical code"
    return (values ++ [ordinal],rest.drop layout.bits)) ([],bits)
  if !rest.isEmpty then throw "ordinary finite assignment trailing bits"
  return values

def valuation (bound : List Nat) (external : List (Expression × Nat)) : Semantics.SourceOrdinary.Valuation :=
  { inputs := fun ordinal => (external.find? (fun (key,_) => key == .input ordinal)).map Prod.snd
    basisInputs := fun ordinal => bound[ordinal]?
    measured := fun origin calls owner =>
      (external.find? (fun (key,_) => key == .measured origin calls owner)).map Prod.snd }

private def evaluate (bound : List Nat) (external : List (Expression × Nat)) (expression : Expression) :
    Except String Nat :=
  match Semantics.SourceOrdinary.evaluate (valuation bound external) expression with
  | none => .error "undefined original ordinary expression"
  | some value => .ok value

theorem evaluate_reference (bound : List Nat) (external : List (Expression × Nat)) (expression : Expression) :
    (evaluate bound external expression).toOption =
      Semantics.SourceOrdinary.evaluate (valuation bound external) expression := by
  unfold evaluate
  cases Semantics.SourceOrdinary.evaluate (valuation bound external) expression <;> rfl

private structure Label where
  basis : Basis
  value : Nat
  dimension : Nat

private def resultLabel (bound : List Nat) (external : List (Expression × Nat)) (value : Value) : Except String Label := do
  let stack ← value.reverse.foldlM (fun (stack : List Label) atom => do
    match atom with
    | .owner _ => throw "quantum owner in coherent ordinary result"
    | .ordinary basis expression =>
      let some dimension := Semantics.FiniteCarrier.dimension basis | throw "ordinary result basis"
      let ordinal ← evaluate bound external expression
      if ordinal ≥ dimension then throw "ordinary result outside its exact basis"
      return ⟨basis,ordinal,dimension⟩ :: stack
    | .tuple arity =>
      if stack.length < arity then throw "coherent result tuple shape"
      let fields := stack.take arity
      let (ordinal,dimension) := fields.foldl (fun (value,stride) field =>
        (value+stride*field.value,stride*field.dimension)) (0,1)
      let basis := (if arity == 2 then Semantics.FiniteCarrier.Atom.pair else .tuple arity) :: fields.flatMap (·.basis)
      return ⟨basis,ordinal,dimension⟩ :: stack.drop arity) ([] : List Label)
  let [result] := stack | throw "coherent ordinary result multiplicity"
  return result

private def variables (inputTypes boundTypes : List Basis) (value : Value) :
    Except String (List (Expression × Basis)) := do
  return (← (ordinary value).mapM fun (_,term) => freeVariables inputTypes boundTypes term).flatten.eraseDups

private def enumerateRows (boundTypes : List Basis) (variables : List (Expression × Basis)) (value : Value)
    (inputDomain : OrdinaryDomain.Checked boundTypes)
    (externalDomain : OrdinaryDomain.Checked (variables.map Prod.snd)) (output : Basis) :
    Except String (List (List Nat)) :=
  (OrdinaryDomain.assignments externalDomain).mapM fun external => do
    let externalValues ← labels (variables.map Prod.snd) external
    let environment := (variables.map Prod.fst).zip externalValues
    (OrdinaryDomain.assignments inputDomain).mapM fun inputBits => do
      let inputValues ← labels boundTypes inputBits
      let result ← resultLabel inputValues environment value
      if result.basis != output then throw "coherent result exact type"
      return result.value

structure Checked (input output : Basis) (inputTypes : List Basis) (value : Value) where
  bound : Value
  boundTypes : List Basis
  seeded : boundValue input = .ok (bound,boundTypes)
  variables : List (Expression × Basis)
  variablesRead : SourceBasisFunction.variables inputTypes boundTypes value = .ok variables
  inputDomain : OrdinaryDomain.Checked boundTypes
  externalDomain : OrdinaryDomain.Checked (variables.map Prod.snd)
  outputLayout : Layout
  outputRead : ∃ before after,(FiniteCarrier.read output).run before = (.ok outputLayout,after)
  rows : List (List Nat)
  evaluated : enumerateRows boundTypes variables value inputDomain externalDomain output = .ok rows
  completeRows : rows.all (fun row => row.length == (OrdinaryDomain.assignments inputDomain).length) = true
  injective : ∀ row ∈ rows,row.Nodup
  effect : Semantics.Raw.Effect
  classified : effect = if (OrdinaryDomain.assignments inputDomain).length == outputLayout.labels.length then .unitary else .iso

def read (input output : Basis) (inputTypes : List Basis) (value : Value) : Finite.WorkM (Checked input output inputTypes value) := do
  match seeded : boundValue input with
  | .error _ => throw .request
  | .ok (bound,boundTypes) =>
    let nodes := value.length+((ordinary value).map fun (_,term) => expressionSize term).sum
    Finite.exactWork (Exact.charge (32*(nodes+1)*(valueFields value+1)))
    match variablesRead : variables inputTypes boundTypes value with
    | .error _ => throw .request
    | .ok variables =>
      let inputDomain ← OrdinaryDomain.read boundTypes
      let externalDomain ← OrdinaryDomain.read (variables.map Prod.snd)
      let outputLayout ← NaturalAffine.witness (FiniteCarrier.read output)
      let inputs := OrdinaryDomain.assignments inputDomain
      let externals := OrdinaryDomain.assignments externalDomain
      Finite.exactWork (Exact.charge (64*(inputs.length+1)*(externals.length+1)*
        (valueFields value+variables.length+1)+16*(inputs.length+1)^2*(externals.length+1)))
      match evaluated : enumerateRows boundTypes variables value inputDomain externalDomain output with
      | .error _ => throw .request
      | .ok rows =>
        if completeRows : rows.all (fun row => row.length == inputs.length) = true then
          if injective : ∀ row ∈ rows,row.Nodup then
            let effect := if inputs.length == outputLayout.val.labels.length then Semantics.Raw.Effect.unitary else .iso
            return ⟨bound,boundTypes,seeded,variables,variablesRead,inputDomain,externalDomain,
              outputLayout.val,by with_reducible exact outputLayout.property,rows,evaluated,completeRows,injective,effect,rfl⟩
          else throw .notIsometric
        else throw .request

end QleisliKernel.SourceTypes.SourceBasisFunction
