import QleisliKernel.SourceTypes.CallSyntax

/-! Shared original operation application syntax classification. This selects
a rule only; it supplies no type, effect or execution interface.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceOperationSyntax

def controlled (tokens : List LocatedToken) : Bool :=
  match CallSyntax.read tokens with
  | .ok call => call.call.callee.map (·.text) == ["controlled"]
  | .error _ => false

def selected (operationNames : List String) (tokens : List LocatedToken) : Bool :=
  tokens.getLast?.map (·.text) == some ")" ||
    match tokens.map (·.text) with | [name] => operationNames.contains name | _ => false

end QleisliKernel.SourceTypes.SourceOperationSyntax
