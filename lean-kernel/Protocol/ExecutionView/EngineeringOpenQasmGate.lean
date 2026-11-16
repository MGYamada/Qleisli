import Protocol.ExecutionView.EngineeringPure
import Protocol.EngineeringOpenQasmGate

/-! Phase-sensitive engineering gate/resource view. The literal tape and
original ideal graphs are reconstructed independently in the native check.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.ExecutionView.FiniteView
open Protocol.EngineeringOpenQasmGate (Decoded Retained Ideal Component Contract Result)
open Qirf.EngineeringOpenQasmGate (Block)
open Target.CanonicalOpenQasmResources (Gate)
open Target.CanonicalOpenQasm (GateCounts)

private def record (name : String) (fields : List Value) : Value :=
  .array (.text name :: fields)

private def bound (epsilon : Semantics.Exact.Coefficient) : Value :=
  record "dyadic" [.text (toString epsilon.numerator),.natural epsilon.exponent]

private def ideal (value : Ideal) : Value :=
  record "ideal" [engineeringLeaf value.leaf,.text value.original]

private def component (value : Component) : Value :=
  record "component" [ideal value.expected,bound value.epsilon]

def engineeringOpenQasmGateRequest (request : Decoded) : Value :=
  let contract := match request.contract with
    | .sequential split first second =>
      record "ordered-sequential-two-v1" [.natural split,component first,component second]
    | .controlled expected => record "controlled-low-selector-v1" [ideal expected]
  record "engineering-openqasm-gate-request" [
    .text Protocol.EngineeringOpenQasmGate.format,.natural 1,
    .text Protocol.EngineeringOpenQasmGate.claimKind,.text Protocol.EngineeringOpenQasmGate.metric,
    .text Protocol.EngineeringOpenQasmGate.checkerProfile,.text Protocol.EngineeringOpenQasmGate.targetProfile,
    .text "implementation-distance",bound request.epsilon,contract,
    record "resource-limits" [
      .text Protocol.EngineeringOpenQasmGate.resourceModel,.natural request.limits.gates,.natural request.limits.tGates]]

private def gateName : Gate → String
  | .h => "h"
  | .x => "x"
  | .y => "y"
  | .z => "z"
  | .s => "s"
  | .sdg => "sdg"
  | .t => "t"
  | .tdg => "tdg"
  | .cx => "cx"
  | .cz => "cz"
  | .swap => "swap"
  | .ccx => "ccx"

def engineeringOpenQasmGateTape (body : ByteArray) (block : Block) : Value :=
  record "gate-tape" [.array (body.data.toList.map fun byte => .natural byte.toNat),basis block.ports.basis,
    .array (block.instructions.map fun inst =>
      record "gate" [.text (gateName inst.gate),.array (inst.wires.map Value.natural)])]

private def describeResult {body : ByteArray} {limits : GateCounts}
    {epsilon : Semantics.Exact.Coefficient} {contract : Contract}
    (result : Result body limits epsilon contract) : Finite.WorkM (Block × List Value) :=
  match result with
  | .sequential first second _ _ checked => do
    let firstGraph ← graph first.artifact checked.first.intended.root
    let secondGraph ← graph second.artifact checked.second.intended.root
    pure (checked.target.block,[firstGraph,secondGraph])
  | .controlled leaf _ checked => do
    let idealGraph ← graph leaf.artifact checked.ideal.root
    pure (checked.target.block,[idealGraph])

def engineeringOpenQasmGate {bytes : ByteArray} (value : Retained bytes) : Finite.WorkM Value := do
  let (block,graphs) ← describeResult value.result
  Finite.exactWork (Exact.charge (1 + value.prepared.body.size + block.instructions.length))
  return record "engineering-openqasm-gate"
    [engineeringOpenQasmGateRequest value.decoded,engineeringOpenQasmGateTape value.prepared.body block,.array graphs]

end QleisliKernel.Protocol.ExecutionView.FiniteView
