import Protocol.ExecutionView.Graph
import Protocol.EngineeringPureTensor

/-! A typed view of the two-component request and all six fresh graphs.
This walker reads retained kernel fields, never a JSON success assertion.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.ExecutionView.FiniteView

private def engineeringRecord (name : String) (fields : List Value) : Value :=
  .array (.text name :: fields)

private def engineeringPort (value : Semantics.Raw.Port) : Value :=
  engineeringRecord "port" [.natural value.token,.array (value.wires.map Value.natural),.natural value.bits]

private def engineeringLeaf (value : Protocol.EngineeringPure.Leaf) : Value :=
  engineeringRecord "leaf" [engineeringPort value.input,engineeringPort value.output,matrix value.required]

private def engineeringBudget (value : Semantics.Exact.Coefficient) : Value :=
  engineeringRecord "dyadic" [.text (toString value.numerator),.natural value.exponent]

private def engineeringComponent (value : Protocol.EngineeringPureTensor.Component) : Value :=
  engineeringRecord "engineering-pure-component" [basis value.domain,basis value.codomain,
    engineeringLeaf value.actual,engineeringLeaf value.ideal,engineeringBudget value.epsilon,
    .text value.actualText,.text value.idealText]

/-- Every profile name, full type tree, literal budget and original component
text remains bound alongside the independent graphs. Parent trees are derived
by the same low-first pair construction used by the composed checker. -/
def engineeringPureTensorRequest (value : Protocol.EngineeringPureTensor.Decoded) : Value :=
  engineeringRecord "engineering-pure-tensor-request" [
    .text "qleisli.engineering-pure-tensor-request",.natural 1,.text "engineering-pure-tensor-bound",
    .text "pure-euclidean-operator-norm-v1",.text "tensor-additive-r8-pure-leaf-v1",
    .text "qirf-r8-pure-v1",.text "ordered-tensor-two-v1",.text "implementation-distance",
    basis value.domain,basis value.codomain,engineeringLeaf value.actual,engineeringLeaf value.ideal,
    engineeringBudget value.epsilon,engineeringComponent value.left,engineeringComponent value.right,
    .text value.expectedText]

def engineeringPureTensor (value : Protocol.EngineeringPureTensor.Retained) : Finite.WorkM Value := do
  let actual ← graph value.actual value.checked.parentActual.root
  let ideal ← graph value.ideal value.checked.parentIdeal.root
  let leftActual ← graph value.leftActual value.checked.left.actual.root
  let leftIdeal ← graph value.leftIdeal value.checked.left.ideal.root
  let rightActual ← graph value.rightActual value.checked.right.actual.root
  let rightIdeal ← graph value.rightIdeal value.checked.right.ideal.root
  return engineeringRecord "engineering-pure-tensor"
    [engineeringPureTensorRequest value.decoded,actual,ideal,leftActual,leftIdeal,rightActual,rightIdeal]

end QleisliKernel.Protocol.ExecutionView.FiniteView
