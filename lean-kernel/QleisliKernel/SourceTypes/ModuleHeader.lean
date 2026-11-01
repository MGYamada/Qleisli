import QleisliKernel.SourceTypes.Declarations

/-! The existing module directive and original declaration-header projection.
The complete source and byte envelope remain unchanged. Header projection
grants no body, effect, operation capability or execution authority.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.ModuleHeader

/-- Exactly one initial opt-out is supported; every other hash directive is
malformed or misplaced. Comments/whitespace are handled by the common lexer. -/
def policyTokens (tokens : List String) : Except String Bool := do
  let disabled := tokens.take 5 == ["#","!","[","no_implicit_prelude","]"]
  let rest := if disabled then tokens.drop 5 else tokens
  if rest.contains "#" then throw "misplaced or malformed module header"
  return disabled

/-- Restore the complete original header from its exact initial module prefix
and declaration tokens. Prefix identity includes original byte positions. -/
structure Projection (source : String) (original : List LocatedToken) where
  moduleTokens : List LocatedToken
  lexed : lexLocated source = .ok moduleTokens
  disabled : Bool
  policy : policyTokens (moduleTokens.map (·.text)) = .ok disabled
  modulePrefix : List LocatedToken
  tokens : List LocatedToken
  initial : modulePrefix = [] ∨ (disabled = true ∧ modulePrefix = moduleTokens.take 5)
  restored : modulePrefix ++ tokens = original

def project (source : String) (original : List LocatedToken) :
    Except String (Projection source original) := do
  match lexed : lexLocated source with
  | .error error => throw error
  | .ok moduleTokens =>
    match policy : policyTokens (moduleTokens.map (·.text)) with
    | .error error => throw error
    | .ok disabled =>
      if (original.take 5).map (·.text) == ["#","!","[","no_implicit_prelude","]"] then
        if initial : disabled = true ∧ original.take 5 = moduleTokens.take 5 then
          return ⟨moduleTokens,lexed,disabled,policy,original.take 5,original.drop 5,
            Or.inr initial,List.take_append_drop 5 original⟩
        else throw "declaration header directive is not initial"
      else
        return ⟨moduleTokens,lexed,disabled,policy,[],original,Or.inl rfl,rfl⟩

theorem Projection.original_header {source original} (projection : Projection source original) :
    projection.modulePrefix ++ projection.tokens = original := projection.restored

end QleisliKernel.SourceTypes.ModuleHeader
