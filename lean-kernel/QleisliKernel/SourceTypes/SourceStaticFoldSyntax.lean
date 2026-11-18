import QleisliKernel.SourceTypes.SourceControlSyntax
import QleisliKernel.SourceTypes.StatementSyntax
import QleisliKernel.SourceTypes.NaturalSyntax
import QleisliKernel.SourceTypes.QuantumMoves

/-! Exact original static fold bounds, carry pattern, initializer and yield.
The reader preserves both contextual keywords and every written token. The
bound, carry type and execution checks use the same slices separately.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceStaticFoldSyntax

structure Parts where
  keyword : LocatedToken
  marker : LocatedToken
  index : LocatedToken
  inToken : LocatedToken
  first : List LocatedToken
  rangeFirst : LocatedToken
  rangeLast : LocatedToken
  last : List LocatedToken
  carry : LocatedToken
  pattern : List LocatedToken
  equals : LocatedToken
  initial : List LocatedToken
  opening : LocatedToken
  steps : List LocatedToken
  yieldToken : LocatedToken
  result : List LocatedToken
  semicolon : Option LocatedToken
  closing : LocatedToken

def Parts.render (parts : Parts) : List LocatedToken :=
  [parts.keyword,parts.marker,parts.index,parts.inToken] ++ parts.first ++
    [parts.rangeFirst,parts.rangeLast] ++ parts.last ++ [parts.carry] ++ parts.pattern ++
    [parts.equals] ++ parts.initial ++ [parts.opening] ++ parts.steps ++
    [parts.yieldToken] ++ parts.result ++ parts.semicolon.toList ++ [parts.closing]

def Parts.spelling (parts : Parts) : Bool :=
  ["qfor","for"].contains parts.keyword.text && parts.marker.text == "static" &&
    NaturalSyntax.isName parts.index.text && parts.inToken.text == "in" &&
    parts.rangeFirst.text == "." && parts.rangeLast.text == "." &&
    parts.rangeFirst.span.endByte == parts.rangeLast.span.startByte &&
    parts.carry.text == "carry" && parts.equals.text == "=" && parts.opening.text == "{" &&
    parts.yieldToken.text == "yield" && parts.semicolon.all (·.text == ";") &&
    parts.closing.text == "}" && !parts.initial.isEmpty &&
    (!parts.result.isEmpty || parts.semicolon.isNone)

/-- The ordinary statement reader sees the original steps and result in order.
`render` separately retains the contextual yield and its optional terminator. -/
def Parts.body (parts : Parts) : List LocatedToken := parts.steps ++ parts.result

structure Checked (tokens : List LocatedToken) where
  parts : Parts
  original : parts.render = tokens
  spelling : parts.spelling = true
  start : Semantics.SourceNatural.Expr
  startRead : NaturalSyntax.read (parts.first.map (·.text)) = .ok start
  stop : Semantics.SourceNatural.Expr
  stopRead : NaturalSyntax.read (parts.last.map (·.text)) = .ok stop
  carryPattern : QuantumMoves.Term
  patternRead : QuantumMoves.parsePattern 65 (parts.pattern.map (·.text)) = .ok carryPattern

/-- Walk the final body backwards so an initializer containing original nested
blocks keeps those blocks. The reconstruction below checks exact token order. -/
private def splitBody : Nat → Nat → List LocatedToken → List LocatedToken →
    Except String (List LocatedToken × LocatedToken × List LocatedToken) :=
  Nat.rec (fun _ _ _ => throw "static fold body delimiter")
    (fun _ next depth tokens body => do
      let token :: rest := tokens | throw "static fold body opener"
      if token.text == "{" then
        if depth == 0 then return (rest.reverse,token,body)
        else next (depth-1) rest (token::body)
      else
        next (if token.text == "}" then depth+1 else depth) rest (token::body))

/-- Inspect complete statement prefixes until the final contextual yield. -/
private def splitYield {fuel : Nat} (prepared : StatementSyntax.Prepared fuel) :
    Nat → List LocatedToken → List (List LocatedToken) →
    Except String (List LocatedToken × LocatedToken × List LocatedToken × Option LocatedToken) :=
  Nat.rec (fun _ _ => throw "static fold yield delimiter")
    (fun _ next tokens steps => do
      let first :: rest := tokens | throw "missing final static fold yield"
      if first.text == "yield" then
        match SourceControlSyntax.delimiter ";" rest with
        | .ok (result,semicolon,[]) =>
          return (steps.reverse.flatten,first,result,some semicolon)
        | .ok _ => throw "static fold yield must be final"
        | .error _ => return (steps.reverse.flatten,first,rest,none)
      else
        let statement ← StatementSyntax.cutPrepared prepared ";" tokens
        if statement.leading.isEmpty then throw "empty static fold statement"
        next statement.suffix ((statement.leading ++ [statement.delimiter])::steps))

def read (tokens : List LocatedToken) : Except String (Checked tokens) := do
  let keyword :: marker :: index :: inToken :: originalTail := tokens | throw "missing original static fold header"
  let (start,rangeFirst,rest) ← SourceControlSyntax.delimiter "." originalTail
  let rangeLast :: rest := rest | throw "missing second range dot"
  let (stop,carry,rest) ← NaturalSyntax.cut "carry" rest
  let (pattern,equals,rest) ← SourceControlSyntax.delimiter "=" rest
  let closing :: backwards := rest.reverse | throw "missing original static fold body"
  let (initial,opening,body) ← splitBody (backwards.length + 1) 0 backwards []
  let bodyFuel := body.length+1
  let (steps,yieldToken,result,semicolon) ← splitYield (StatementSyntax.prepare bodyFuel) bodyFuel body []
  let parts : Parts := ⟨keyword,marker,index,inToken,start,rangeFirst,rangeLast,stop,carry,
    pattern,equals,initial,opening,steps,yieldToken,result,semicolon,closing⟩
  if original : parts.render = keyword :: marker :: index :: inToken :: originalTail then
    if spelling : parts.spelling = true then
      match startRead : NaturalSyntax.read (parts.first.map (·.text)),
          stopRead : NaturalSyntax.read (parts.last.map (·.text)),
          patternRead : QuantumMoves.parsePattern 65 (parts.pattern.map (·.text)) with
      | .ok first,.ok last,.ok carry =>
        pure ⟨parts,original,spelling,first,startRead,last,stopRead,carry,patternRead⟩
      | .error msg,_,_ | _,.error msg,_ | _,_,.error msg => throw msg
    else throw "static fold spelling"
  else throw "static fold original reconstruction"

end QleisliKernel.SourceTypes.SourceStaticFoldSyntax
