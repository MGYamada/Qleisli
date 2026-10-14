import Protocol.ExecutionView.Contracts
import Protocol.EngineeringInstrument

/-! Typed engineering instrument context and both fresh original graphs.
The view describes retained checked fields, never producer outcome labels,
matrices, probabilities or claimed success. This is an IR engineering profile.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.ExecutionView.FiniteView

private def engineeringRecord (name : String) (fields : List Value) : Value :=
  .array (.text name :: fields)

private def engineeringBound (value : Semantics.Exact.Coefficient) : Value :=
  engineeringRecord "dyadic" [.text (toString value.numerator),.natural value.exponent]

/-- Fixed profiles and the complete typed interfaces remain bound alongside
the original expected text, before either retained graph is described. -/
def engineeringInstrumentRequest (value : Protocol.EngineeringInstrument.Decoded) : Value :=
  engineeringRecord "engineering-instrument-request" [
    .text "qleisli.engineering-instrument-request",.natural 1,.text "engineering-instrument-bound",
    .text "complete-adjoint-euclidean-operator-norm-v1",.text "choi-l1-r8-instrument-v1",
    .text "qirf-r8-instrument-v1",.text "single-component-v1",.text "implementation-distance",
    instrumentSignature value.actualSignature,instrumentSignature value.expectedSignature,
    contractIdentity value.identity,engineeringBound value.epsilon,
    .array (value.majorants.map engineeringBound),.text value.expectedText]

def engineeringInstrument (value : Protocol.EngineeringInstrument.Retained) : Finite.WorkM Value := do
  let actual ← graph value.actual value.checked.actual
  let expected ← graph value.expected value.checked.expected
  return engineeringRecord "engineering-instrument"
    [engineeringInstrumentRequest value.decoded,actual,expected]

end QleisliKernel.Protocol.ExecutionView.FiniteView
