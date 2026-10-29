import QleisliKernel.SourceTypes.QuantumSignature

/-! Informed original qmatch-site extraction. All expression/arm tokens and
their original byte occurrences are retained. This is neither typing nor an
operation-capability verdict, source preservation theorem or native acceptance.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.QuantumMatch
open Finite

private structure Chunk where
  tokens : List LocatedToken
  delimiter : LocatedToken
  rest : List LocatedToken

/-- Balanced source delimiters only. Expressions are retained intact rather
than inferred, evaluated or normalized by this extraction pass. -/
private def segment : Nat → List String → List String → List LocatedToken → List LocatedToken →
    Except String Chunk :=
  Nat.rec (fun _ _ _ _ => throw "unterminated qmatch source segment")
    (fun _ next stops stack tokens reversed => do
      let token :: rest := tokens | throw "missing qmatch source delimiter"
      if stack.isEmpty && stops.contains token.text then return ⟨reversed.reverse,token,rest⟩
      if ["(","[","{"].contains token.text then
        let closer := if token.text == "(" then ")" else if token.text == "[" then "]" else "}"
        return ← next stops (closer :: stack) rest (token :: reversed)
      if [")","]","}"].contains token.text then
        let expected :: tail := stack | throw "unmatched qmatch source delimiter"
        if token.text != expected then throw "mismatched qmatch source delimiter"
        return ← next stops tail rest (token :: reversed)
      next stops stack rest (token :: reversed))

private def expect (text : String) (tokens : List LocatedToken) :
    Except String (LocatedToken × List LocatedToken) := do
  let token :: rest := tokens | throw "missing qmatch source token"
  if token.text != text then throw "unexpected qmatch source token"
  return (token,rest)

structure Arm where
  label : List LocatedToken
  operation : List LocatedToken
  deriving BEq, DecidableEq, Repr

private def arms : Nat → List LocatedToken → List Arm →
    Except String (List Arm × List LocatedToken) :=
  Nat.rec (fun _ _ => throw "qmatch exceeds existing arm bound") (fun _ next tokens reversed => do
    if tokens.head?.map (·.text) == some "}" then
      return (reversed.reverse,tokens.drop 1)
    let label ← segment (tokens.length+1) ["="] [] tokens []
    if label.tokens.isEmpty then throw "empty qmatch label"
    let (arrow,rest) ← expect ">" label.rest
    if label.delimiter.span.endByte != arrow.span.startByte then throw "split qmatch fat arrow"
    let operation ← segment (rest.length+1) [",","}"] [] rest []
    if operation.tokens.isEmpty then throw "empty qmatch operation"
    let result := ⟨label.tokens,operation.tokens⟩ :: reversed
    if result.length > 64 then throw "qmatch exceeds existing arm bound"
    if operation.delimiter.text == "}" then return (result.reverse,operation.rest)
    next operation.rest result)

structure Parsed where
  keyword : LocatedToken
  selector : List LocatedToken
  target : List LocatedToken
  arms : List Arm
  tokens : List LocatedToken
  deriving BEq, DecidableEq, Repr

def parse (tokens : List LocatedToken) : Except String (Parsed × List LocatedToken) := do
  let (keyword,rest) ← expect "qmatch" tokens
  let (_,rest) ← expect "(" rest
  let selector ← segment (rest.length+1) [","] [] rest []
  let target ← segment (selector.rest.length+1) [",",")"] [] selector.rest []
  if target.delimiter.text != ")" then throw "qmatch requires exactly two owner expressions"
  if selector.tokens.isEmpty || target.tokens.isEmpty then throw "empty qmatch owner expression"
  let (_,rest) ← expect "{" target.rest
  let (arms,suffix) ← arms 65 rest []
  if arms.isEmpty then throw "empty qmatch partition"
  return (⟨keyword,selector.tokens,target.tokens,arms,tokens.take (tokens.length-suffix.length)⟩,suffix)

structure Site (sources : Sources) (owner name : String) (offset : Nat) where
  original : OrdinarySignature.Original sources owner name
  parsed : Parsed
  leading : List LocatedToken
  suffix : List LocatedToken
  originalBody : original.occurrence.body = leading ++ parsed.tokens ++ suffix
  occurrence : parsed.keyword.span.startByte = offset
  parsing : parse (original.occurrence.body.drop leading.length) = .ok (parsed,suffix)

/-- An offset selects an actual token in the freshly read original function,
not a supplied substring or independently submitted occurrence table. -/
def read (sources : Sources) (owner name : String) (offset : Nat) :
    WorkM (Site sources owner name offset) := do
  let original ← OrdinarySignature.readOriginal sources owner name
  let body := original.occurrence.body
  exactWork (Exact.charge (256*(body.length+1)))
  let leading := body.takeWhile (fun token => token.span.startByte != offset)
  match parsed : parse (body.drop leading.length) with
  | .error _ => throw .request
  | .ok (site,suffix) =>
    if same : body = leading ++ site.tokens ++ suffix ∧ site.keyword.span.startByte = offset then
      return ⟨original,site,leading,suffix,same.1,same.2,parsed⟩
    else throw .request

end QleisliKernel.SourceTypes.QuantumMatch
