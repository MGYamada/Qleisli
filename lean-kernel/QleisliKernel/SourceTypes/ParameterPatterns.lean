import QleisliKernel.SourceTypes.OrdinarySignature

/-! Shared parameter patterns from the exact original header. Every untouched
type clause is compared to the original common header reader.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.ParameterPatterns

def read {sources owner name} (original : OrdinarySignature.Original sources owner name) :
    Except String (List (List String)) := do
  let suffix := original.occurrence.header.dropWhile (· != original.occurrence.nameToken)
  let nameToken :: header := suffix | throw "missing original parameter clause"
  let header ← match original.parsedHeader.staticTokens with
    | none => pure header
    | some statics => do
      if (header.take (statics.length+2)).map (·.text) !=
          ["["] ++ statics.map (·.text) ++ ["]"] then
        throw "original static parameter boundary mismatch"
      pure (header.drop (statics.length+2))
  let opener :: tail := header | throw "missing original parameter opener"
  if nameToken != original.occurrence.nameToken || opener.text != "(" then throw "parameter occurrence mismatch"
  let result := original.parsedHeader.resultTokens
  let requirements := match original.parsedHeader.requiresTokens with
    | none => [] | some tokens => "requires" :: tokens.map (·.text)
  if tail.length < result.length+requirements.length+3 then throw "incomplete original parameter envelope"
  let raw := tail.take (tail.length-result.length-requirements.length-3)
  let ending := tail.drop raw.length
  if ending.map (·.text) != [")","-",">"] ++ result.map (·.text) ++ requirements then
    throw "original parameter boundary mismatch"
  let clauses ← splitMembers (raw.map (·.text))
  let pairs ← clauses.mapM fun clause => do
    let pattern := clause.takeWhile (· != ":")
    let ":" :: ty := clause.drop pattern.length | throw "missing original parameter type"
    if pattern.isEmpty || ty.isEmpty then throw "empty original parameter pattern/type"
    pure (pattern,ty)
  if pairs.map Prod.snd != original.parsedHeader.parameterTypes then throw "original type clause mismatch"
  pure (pairs.map Prod.fst)

end QleisliKernel.SourceTypes.ParameterPatterns
