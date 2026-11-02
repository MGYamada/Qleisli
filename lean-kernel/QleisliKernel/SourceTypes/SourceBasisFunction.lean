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

private def evaluate (bound : List Nat) (external : List (Expression × Nat)) : Expression → Except String Nat
  | expression@(.input _) | expression@(.measured ..) => do
    let some (_,value) := external.find? (fun (key,_) => key == expression)
      | throw "missing captured ordinary valuation"
    return value
  | .basisInput ordinal => do
    let some value := bound[ordinal]? | throw "missing coherent basis valuation"
    return value
  | .unit => pure 0
  | .bit value => pure (if value then 1 else 0)
  | .ordinal value => pure value
  | .project .. => throw "unsupported untyped ordinary field projection"
  | .combine stride first second => do
    if stride == 0 then throw "zero logical record packing stride"
    let first ← evaluate bound external first
    let second ← evaluate bound external second
    if first ≥ stride then throw "logical record prefix exceeds its exact dimension"
    return first+stride*second
  | .field stride dimension receiver => do
    if stride == 0 || dimension == 0 then throw "invalid logical original field dimensions"
    let receiver ← evaluate bound external receiver
    return (receiver/stride)%dimension
  | .not value => do
    let value ← evaluate bound external value
    if value ≥ 2 then throw "Boolean basis operand range"
    return 1-value
  | .xor first second => do
    let first ← evaluate bound external first
    let second ← evaluate bound external second
    if first ≥ 2 || second ≥ 2 then throw "Boolean basis operand range"
    return if first == second then 0 else 1
  | .and first second => do
    let first ← evaluate bound external first
    let second ← evaluate bound external second
    if first ≥ 2 || second ≥ 2 then throw "Boolean basis operand range"
    return if first == 1 && second == 1 then 1 else 0
  | .choose condition thenValue elseValue => do
    let condition ← evaluate bound external condition
    if condition ≥ 2 then throw "Boolean basis condition range"
    if condition == 1 then evaluate bound external thenValue else evaluate bound external elseValue

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
