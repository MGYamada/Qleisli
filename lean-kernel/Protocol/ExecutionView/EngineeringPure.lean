import Protocol.ExecutionView.Graph
import Protocol.EngineeringPure

/-! A typed view of the separate engineering request and both fresh graphs.
This walker reads retained kernel fields, never a JSON success assertion.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.ExecutionView.FiniteView

private def engineeringRecord (name : String) (fields : List Value) : Value :=
  .array (.text name :: fields)

private def engineeringPort (value : Semantics.Raw.Port) : Value :=
  engineeringRecord "port" [.natural value.token,.array (value.wires.map Value.natural),.natural value.bits]

private def engineeringLeaf (value : Protocol.EngineeringPure.Leaf) : Value :=
  engineeringRecord "leaf" [engineeringPort value.input,engineeringPort value.output,matrix value.required]

/-- Fixed profile names are included explicitly after independent decoding has
checked every name. Original ideal text remains bound as well as its graph. -/
def engineeringPureRequest (value : Protocol.EngineeringPure.Decoded) : Value :=
  engineeringRecord "engineering-pure-request" [
    .text "qleisli.engineering-pure-request",.natural 1,.text "engineering",
    .text "pure-euclidean-operator-norm-v1",.text "frobenius-r8-pure-leaf-v1",
    .text "qirf-r8-pure-v1",.text "single-component-v1",.text "implementation-distance",
    basis value.domain,basis value.codomain,engineeringLeaf value.actual,engineeringLeaf value.ideal,
    engineeringRecord "dyadic" [.text (toString value.epsilon.numerator),.natural value.epsilon.exponent],
    .text value.expectedText]

def engineeringPure (value : Protocol.EngineeringPure.Retained) : Finite.WorkM Value := do
  let actual ← graph value.actual value.checked.actual.root
  let ideal ← graph value.ideal value.checked.ideal.root
  return engineeringRecord "engineering-pure" [engineeringPureRequest value.decoded,actual,ideal]

end QleisliKernel.Protocol.ExecutionView.FiniteView
