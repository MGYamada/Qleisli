import QleisliKernel.SourceTypes.SourceRuntimeValues
import QleisliKernel.SourceTypes.SourceNominal

/-! Typed logical ordinal expressions for original ordinary nominal values.
Written initializer evaluation belongs to the source traversal; construction
restores exact original declaration order without changing nominal identity.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceRuntimeNominalValue
open QleisliKernel QleisliKernel.SourceTypes SourceRuntimeValues Semantics.FiniteCarrier

private structure Logical where
  basis : Basis
  expression : Expression
  dimension : Nat

private def combine (values : List Logical) : Expression × Nat :=
  values.foldl (fun (expression,stride) value =>
    (.combine stride expression value.expression,stride*value.dimension)) (.ordinal 0,1)

/-- Collapse a complete ordinary runtime tuple using logical cardinalities,
never physical bit widths. A quantum-containing value is rejected intact. -/
def collapse (value : Value) : Except String (Basis × Expression) := do
  let stack ← value.reverse.foldlM (fun (stack : List Logical) atom => do
    match atom with
    | .owner _ => throw "ordinary record field contains a quantum owner"
    | .ordinary basis expression =>
      let some dimension := Semantics.FiniteCarrier.dimension basis | throw "ordinary field exact type"
      return ⟨basis,expression,dimension⟩ :: stack
    | .tuple arity =>
      if arity < 2 || stack.length < arity then throw "ordinary field complete tuple shape"
      let fields := stack.take arity
      let basis := (if arity == 2 then Semantics.FiniteCarrier.Atom.pair else .tuple arity) :: fields.flatMap (·.basis)
      let (expression,dimension) := combine fields
      return ⟨basis,expression,dimension⟩ :: stack.drop arity) ([] : List Logical)
  let [result] := stack | throw "ordinary field result multiplicity"
  if Semantics.RuntimeType.ordinary result.basis != typeOf value then throw "ordinary field full result type"
  return (result.basis,result.expression)

/-- Preserve the ordinary tuple representation used by parameter seeding and
patterns. A nominal record remains one ordinary leaf; its fields stay private. -/
def expand (basis : Basis) (expression : Expression) : Except String Value := do
  let (values,_,_) ← seedValues [(⟨Semantics.RuntimeType.ordinary basis,[]⟩ : RuntimeSignature.Part #[])]
  let [template] := values | throw "ordinary logical value shape"
  match template with
  | [.ordinary _ _] => return [.ordinary basis expression]
  | _ =>
    let (value,_) ← template.foldlM (fun (value,stride) atom => do
      match atom with
      | .owner _ => throw "ordinary expansion introduced a quantum owner"
      | .tuple arity => return (value ++ [.tuple arity],stride)
      | .ordinary field _ =>
        let some dimension := Semantics.FiniteCarrier.dimension field | throw "ordinary logical field dimension"
        return (value ++ [.ordinary field (.field stride dimension expression)],stride*dimension))
      (([] : Value),1)
    return value

def construct {sources caller scope tokens written} (reference : @SourceNominal.Record sources caller scope tokens written)
    (values : List Value) : Except String Value := do
  if values.map typeOf != reference.fields.map (fun field => Semantics.RuntimeType.ordinary field.basis) then
    throw "record written initializer exact ordinary field types"
  let logical ← values.mapM fun value => do
    let (basis,expression) ← collapse value
    let some dimension := Semantics.FiniteCarrier.dimension basis | throw "record field logical dimension"
    return (⟨basis,expression,dimension⟩ : Logical)
  let written := reference.fields.zip logical
  let ordered ← reference.definition.fields.mapM fun field => do
    let some (_,value) := written.find? (fun (original,_) => original.member.name.text == field.member.name.text)
      | throw "missing original record initializer"
    if value.basis != field.basis then throw "record original field exact type"
    return value
  let (expression,_) := combine ordered
  return [.ordinary reference.nominal.query.basis expression]

def project {sources caller basis tokens written}
    (reference : @SourceNominal.Projection sources caller basis tokens written) (receiver : Expression) :
    Except String Value := do
  let dimensions ← reference.definition.fields.mapM fun field => do
    let some dimension := Semantics.FiniteCarrier.dimension field.basis | throw "original field logical dimension"
    return dimension
  let some dimension := dimensions[reference.index]? | throw "original projection field ordinal"
  let stride := (dimensions.take reference.index).foldl (·*·) 1
  if stride == 0 || dimension == 0 then throw "empty original field logical carrier"
  expand reference.field.basis (.field stride dimension receiver)

end QleisliKernel.SourceTypes.SourceRuntimeNominalValue
