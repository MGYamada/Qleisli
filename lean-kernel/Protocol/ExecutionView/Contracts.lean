import Protocol.ExecutionView.Graph
import Protocol.NativeContract

/-! Typed contract obligations read from retained native stages. These
walkers grant no acceptance authority or source/runtime preservation claim.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.ExecutionView.FiniteView
open QleisliKernel.Semantics

private def contractRecord (name : String) (fields : List Value) : Value :=
  .array (.text name :: fields)

private def contractPort (value : Raw.Port) : Value :=
  contractRecord "port" [.natural value.token,.array (value.wires.map Value.natural),.natural value.bits]

def encoding (value : Finite.Encoding) : Value :=
  contractRecord "encoding" [basis value.logical,basis value.physical,matrix value.map]

def contract (value : Finite.Contract) : Value :=
  contractRecord "encoded-contract" [encoding value.input,encoding value.output,matrix value.logical]

def instrumentSignature (value : InstrumentContract.Signature) : Value :=
  contractRecord "instrument-signature" [basis value.input,.array (value.result.map fun atom =>
    match atom with
    | .unit => contractRecord "unit" []
    | .bit => contractRecord "bit" []
    | .bits width => contractRecord "bits" [.natural width]
    | .quantum tree => contractRecord "quantum" [basis tree]
    | .pair => contractRecord "pair" []
    | .tuple arity => contractRecord "tuple" [.natural arity])]

def contractIdentity (value : Function.Identity) : Value :=
  contractRecord "identity" [.text value.implementation,.text value.specification,
    .array (value.sources.map fun source => contractRecord "source" [.text source.1,.text source.2])]

/-- Describe exactly the typed obligation retained by the original native
adapter, without reading producer-supplied success flags or JSON fields. -/
def nativeRequest (value : NativeContract.RequestRetained) : Value :=
  match value with
  | .encoded required _ => contractRecord "encoded" [contract required]
  | .leaf signature input output required _ _ =>
    contractRecord "leaf" [basis signature,contractPort input,contractPort output,matrix required]
  | .pureLeaf value => contractRecord "pure-leaf" [basis value.domain,basis value.codomain,
      contractPort value.input,contractPort value.output,matrix value.required]
  | .control value => contractRecord "control" [basis value.signature,.array (value.axes.map Value.natural)]
  | .controlOwners value => contractRecord "control-owners"
      [.array (value.signatures.map basis),.array (value.axes.map Value.natural)]
  | .instrument value => contractRecord "instrument" [instrumentSignature value.decoded.actualSignature,
      instrumentSignature value.decoded.expectedSignature,contractIdentity value.decoded.identity]

/-- Select the actual fresh root retained by the original profile check.
No root check is repeated or substituted for the result being described. -/
def nativeRoot : NativeContract.RequestRetained → Qirf.Validity.Root
  | .encoded _ checked => checked.root
  | .leaf _ _ _ _ root _ => root
  | .control value => value.checked.root
  | .controlOwners value => value.checked.root
  | .instrument value => value.checked.actual
  | .pureLeaf value => value.checked.root

/-- Describe both independently checked graphs for an observing request.
For all other profiles the reference slot is explicitly null. -/
def nativeContract (value : NativeContract.Retained) : QleisliKernel.Finite.WorkM Value := do
  let actual ← graph value.artifact (nativeRoot value.request)
  let expected ← match value.request with
    | .instrument instrument => graph instrument.expected instrument.checked.expected
    | _ => pure .null
  return contractRecord "native-contract" [nativeRequest value.request,actual,expected]

end QleisliKernel.Protocol.ExecutionView.FiniteView
