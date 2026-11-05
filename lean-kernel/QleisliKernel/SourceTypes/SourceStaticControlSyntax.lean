import QleisliKernel.SourceTypes.SourceControlSyntax
import QleisliKernel.SourceTypes.NaturalHeaders

/-! Exact original static conditional syntax. Both source arms and the original
natural comparison remain present; this decomposition selects no branch and
proves no original typing, effect or recursive decrease obligation.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceStaticControlSyntax

structure Conditional where
  marker : LocatedToken
  parts : SourceControlSyntax.Conditional

def Conditional.render (written : Conditional) : List LocatedToken :=
  [written.parts.keyword,written.marker] ++ written.parts.condition ++
    [written.parts.thenOpen] ++ written.parts.thenBody ++
    [written.parts.thenClose,written.parts.otherwise,written.parts.elseOpen] ++
    written.parts.elseBody ++ [written.parts.elseClose]

def Conditional.spelling (written : Conditional) : Bool :=
  written.marker.text == "static" && written.parts.spelling

structure Checked (tokens : List LocatedToken) where
  written : Conditional
  original : written.render = tokens
  spelling : written.spelling = true
  predicate : Semantics.SourceNatural.Predicate
  predicateRead : NaturalHeaders.predicate (written.parts.condition.map (·.text)) = .ok predicate

def Checked.parts {tokens} (checked : Checked tokens) : SourceControlSyntax.Conditional :=
  checked.written.parts

def read (tokens : List LocatedToken) : Except String (Checked tokens) := do
  let keyword :: marker :: rest := tokens | throw "missing original if static prefix"
  let parts ← SourceControlSyntax.conditionalParts keyword rest
  let written : Conditional := ⟨marker,parts⟩
  if original : written.render = keyword :: marker :: rest then
    if spelling : written.spelling = true then
      match predicateRead : NaturalHeaders.predicate (written.parts.condition.map (·.text)) with
      | .ok predicate => return ⟨written,original,spelling,predicate,predicateRead⟩
      | .error reason => throw reason
    else throw "original static conditional spelling"
  else throw "original static conditional token reconstruction"

end QleisliKernel.SourceTypes.SourceStaticControlSyntax
