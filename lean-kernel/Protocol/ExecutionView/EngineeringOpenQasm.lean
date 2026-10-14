import Protocol.ExecutionView.Contracts
import Protocol.EngineeringOpenQasm

/-! Typed target request, literal target bytes/word and both fresh graphs.
The view describes retained checked fields, never producer outcome labels,
matrices, probabilities or claimed success. The actual graph is generated from the independently decoded target bytes.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.ExecutionView.FiniteView

private def engineeringRecord (name : String) (fields : List Value) : Value :=
  .array (.text name :: fields)

private def engineeringBound (value : Semantics.Exact.Coefficient) : Value :=
  engineeringRecord "dyadic" [.text (toString value.numerator),.natural value.exponent]

/-- Fixed profiles and the complete typed interfaces remain bound alongside
the original expected text, before either retained graph is described. -/
def engineeringOpenQasmRequest (value : Protocol.EngineeringOpenQasm.Decoded) : Value :=
  engineeringRecord "engineering-openqasm-request" [
    .text "qleisli.engineering-openqasm-request",.natural 1,.text "engineering-target-instrument-bound",
    .text "complete-adjoint-euclidean-operator-norm-v1",.text "canonical-target-choi-l1-r8-v1",
    .text "openqasm3-canonical-one-qubit-terminal-r8-v1",.text "single-component-v1",.text "implementation-distance",
    instrumentSignature value.actualSignature,instrumentSignature value.expectedSignature,
    contractIdentity value.identity,engineeringBound value.epsilon,
    .array (value.majorants.map engineeringBound),.text value.expectedText]

def engineeringOpenQasm (value : Protocol.EngineeringOpenQasm.Retained) : Finite.WorkM Value := do
  let actual ← graph (Qirf.EngineeringOpenQasm.actualArtifact value.checked.target)
    value.checked.instrument.actual
  let expected ← graph value.expected value.checked.instrument.expected
  Finite.exactWork (Exact.charge (1 + value.checked.target.original.size + value.checked.target.gates.length))
  return engineeringRecord "engineering-openqasm"
    [engineeringOpenQasmRequest value.decoded,
      .array (value.checked.target.original.data.toList.map fun byte => .natural byte.toNat),
      .array (value.checked.target.gates.map fun gate => .text gate.name),actual,expected]

end QleisliKernel.Protocol.ExecutionView.FiniteView
