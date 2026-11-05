import QleisliKernel.SourceTypes.SourceControlSyntax
import QleisliKernel.SourceTypes.CallName

/-! Located ordinary nominal expression decomposition. Type lookup, exact
member/privacy/type checks and evaluation remain separate obligations. Written
record initializer order is preserved rather than sorted by declaration.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceNominalSyntax

structure Variant (tokens : List LocatedToken) where
  typeTokens : List LocatedToken
  typeName : CallName.Name typeTokens
  separator : LocatedToken
  member : LocatedToken
  original : typeTokens ++ [separator,member] = tokens
  spelling : separator.text = "::" ∧ identifier member.text = true

def readVariant (tokens : List LocatedToken) : Except String (Variant tokens) := do
  let typeTokens := tokens.dropLast.dropLast
  let typeName ← CallName.readName typeTokens
  let some separator := tokens[tokens.length-2]? | throw "missing original variant separator"
  let some member := tokens.getLast? | throw "missing original variant member"
  if original : typeTokens ++ [separator,member] = tokens then
    if spelling : separator.text = "::" ∧ identifier member.text = true then
      return ⟨typeTokens,typeName,separator,member,original,spelling⟩
    else throw "original variant spelling"
  else throw "original variant reconstruction"

structure Field where
  name : LocatedToken
  colon : LocatedToken
  expression : List LocatedToken
  comma : Option LocatedToken

def Field.render (field : Field) : List LocatedToken :=
  [field.name,field.colon] ++ field.expression ++ field.comma.toList

def Field.spelling (field : Field) : Bool :=
  identifier field.name.text && field.colon.text == ":" && !field.expression.isEmpty &&
    field.comma.all (fun comma => comma.text == ",")

private def field (tokens : List LocatedToken) (comma : Option LocatedToken) : Except String Field := do
  let name :: colon :: expression := tokens | throw "incomplete original record field"
  let result : Field := ⟨name,colon,expression,comma⟩
  if !result.spelling then throw "original record field spelling"
  return result

private def fields : Nat → List LocatedToken → Except String (List Field) :=
  Nat.rec (fun _ => throw "original record field traversal fuel") (fun _ recurse tokens => do
    if tokens.isEmpty then return []
    match SourceControlSyntax.delimiter "," tokens with
    | .ok (leading,comma,rest) => return (← field leading (some comma)) :: (← recurse rest)
    | .error _ => return [← field tokens none])

structure Record (tokens : List LocatedToken) where
  typeTokens : List LocatedToken
  typeName : CallName.Name typeTokens
  opening : LocatedToken
  initializers : List Field
  closing : LocatedToken
  original : typeTokens ++ [opening] ++ initializers.flatMap Field.render ++ [closing] = tokens
  spelling : opening.text = "{" ∧ closing.text = "}" ∧ initializers.all Field.spelling = true

def readRecord (tokens : List LocatedToken) : Except String (Record tokens) := do
  let (typeTokens,opening,rest) ← SourceControlSyntax.delimiter "{" tokens
  let typeName ← CallName.readName typeTokens
  let (body,closing,suffix) ← SourceControlSyntax.delimiter "}" rest
  if !suffix.isEmpty then throw "trailing original record tokens"
  let initializers ← fields (body.length+1) body
  if original : typeTokens ++ [opening] ++ initializers.flatMap Field.render ++ [closing] = tokens then
    if spelling : opening.text = "{" ∧ closing.text = "}" ∧ initializers.all Field.spelling = true then
      return ⟨typeTokens,typeName,opening,initializers,closing,original,spelling⟩
    else throw "original record spelling"
  else throw "original record reconstruction"

structure Projection (tokens : List LocatedToken) where
  receiver : List LocatedToken
  dot : LocatedToken
  member : LocatedToken
  original : receiver ++ [dot,member] = tokens
  spelling : receiver ≠ [] ∧ dot.text = "." ∧ identifier member.text = true

def readProjection (tokens : List LocatedToken) : Except String (Projection tokens) := do
  let receiver := tokens.dropLast.dropLast
  let some dot := tokens[tokens.length-2]? | throw "missing original field dot"
  let some member := tokens.getLast? | throw "missing original field member"
  if original : receiver ++ [dot,member] = tokens then
    if spelling : receiver ≠ [] ∧ dot.text = "." ∧ identifier member.text = true then
      return ⟨receiver,dot,member,original,spelling⟩
    else throw "original projection spelling"
  else throw "original projection reconstruction"

end QleisliKernel.SourceTypes.SourceNominalSyntax
