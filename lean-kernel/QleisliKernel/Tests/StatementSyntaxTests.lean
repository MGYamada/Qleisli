import QleisliKernel.SourceTypes.StatementSyntax
import QleisliKernel.SourceTypes.SourceSyntax

/-! Bounded segmentation controls, not source-language acceptance examples.
Literal observations are executable guards; the general retained-token theorem
is checked separately without normalizing every literal in the proof kernel.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.StatementSyntaxTests
open QleisliKernel.SourceTypes
open QleisliKernel.SourceTypes StatementSyntax

def split (source : String) : Option (List String × List String) := do
  let tokens ← (lexLocated source).toOption
  let result ← (cut ";" tokens).toOption
  return (result.leading.map (·.text),result.suffix.map (·.text))

def parsed (source : String) : Option Let := do
  let tokens ← (lexLocated source).toOption
  let result ← (read tokens).toOption
  return result.statement

def shape (source : String) : Option (List String × List String × List String) :=
  (parsed source).map fun statement =>
    (statement.pattern.map (·.text),statement.expression.map (·.text),statement.rest.map (·.text))

#guard split "h(q);q" == some (["h","(","q",")"],["q"])
#guard split "f(g(q));h(q)" ==
  some (["f","(","g","(","q",")",")"],["h","(","q",")"])
#guard split "f[1,2](q);q" ==
  some (["f","[","1",",","2","]","(","q",")"],["q"])
#guard split "if b {let q=h(q);q}else{q};q" ==
  some (["if","b","{","let","q","=","h","(","q",")",";","q","}",
    "else","{","q","}"],["q"])
#guard split "f(q; r);s" == some (["f","(","q",";","r",")"],["s"])
#guard split "h(q)" == none
#guard split "h(q; q" == none
#guard split "h(q]; q" == none
#guard split "h([q));q" == none
#guard split "h(q)};q" == none
#guard split "/*λ*/h(q);r" == some (["h","(","q",")"],["r"])
#guard ((lexLocated "/*λ*/h(q);r").toOption.bind fun tokens =>
  (cut ";" tokens).toOption.map fun result =>
    (result.delimiter.span.startByte,result.delimiter.span.endByte)) == some (10,11)

#guard shape "let q=h(q);q" == some (["q"],["h","(","q",")"],["q"])
#guard shape "let (s,q)=qmatch(s,q){0=>f,1=>g};(s,q)" ==
  some (["(","s",",","q",")"],
    ["qmatch","(","s",",","q",")","{","0","=",">","f",",","1","=",">","g","}"],
    ["(","s",",","q",")"])
#guard shape "let q=if b{let q=h(q);q}else{q};q" ==
  some (["q"],["if","b","{","let","q","=","h","(","q",")",";","q","}",
    "else","{","q","}"],["q"])
#guard (parsed "let q=h(q)").isNone
#guard (parsed "let q=;q").isNone
#guard (parsed "let =h(q);q").isNone
#guard (parsed "q=h(q);q").isNone
#guard (parsed "let (q]=h(q);q").isNone
-- The suffix is retained verbatim; its validity belongs to complete traversal.
#guard shape "let q=h(q);junk }" == some (["q"],["h","(","q",")"],["junk","}"])

-- Exact former scanner, retained only as a differential test reference.
-- It is not an executable acceptance fallback.
namespace Legacy
private structure Scan where
  stack : List String := []
  before : List LocatedToken := []
  separator : Option LocatedToken := none
  after : List LocatedToken := []

private def closing (text : String) : Option String :=
  if text == "(" then some ")" else if text == "[" then some "]"
  else if text == "{" then some "}" else none

private def advance (separator : String) (s : Scan) (token : LocatedToken) : Except String Scan := do
  if s.separator.isSome then return {s with after := token :: s.after}
  if s.stack.isEmpty && token.text == separator then return {s with separator := some token}
  if let some expected := closing token.text then
    if s.stack.length ≥ 64 then throw "source statement nesting capacity"
    return {s with stack := expected :: s.stack,before := token :: s.before}
  if [")","]","}"].contains token.text then
    let expected :: stack := s.stack | throw "unmatched source statement delimiter"
    if token.text != expected then throw "mismatched source statement delimiter"
    return {s with stack,before := token :: s.before}
  return {s with before := token :: s.before}

structure Cut (separator : String) (tokens : List LocatedToken) where
  leading : List LocatedToken
  delimiter : LocatedToken
  suffix : List LocatedToken
  spelling : delimiter.text = separator
  original : leading ++ [delimiter] ++ suffix = tokens

/-- Locate the first separator at delimiter depth zero. The entire suffix is
retained, and must still be consumed by the enclosing complete traversal. -/
def cut (separator : String) (tokens : List LocatedToken) : Except String (Cut separator tokens) := do
  if !["=",";"].contains separator then throw "unsupported statement separator"
  let state ← tokens.foldlM (advance separator) {}
  if !state.stack.isEmpty then throw "unclosed original statement expression"
  let some delimiter := state.separator | throw "missing original statement separator"
  let leading := state.before.reverse
  let suffix := state.after.reverse
  if spelling : delimiter.text = separator then
    if original : leading ++ [delimiter] ++ suffix = tokens then
      return ⟨leading,delimiter,suffix,spelling,original⟩
    else throw "source statement cut lost original tokens"
  else throw "source statement separator differs"

structure Let where
  keyword : LocatedToken
  pattern : List LocatedToken
  assignment : LocatedToken
  expression : List LocatedToken
  terminator : LocatedToken
  rest : List LocatedToken
  deriving BEq, DecidableEq, Repr

def Let.render (statement : Let) : List LocatedToken :=
  [statement.keyword] ++ statement.pattern ++ [statement.assignment] ++
    statement.expression ++ [statement.terminator] ++ statement.rest

structure Checked (tokens : List LocatedToken) where
  statement : Let
  original : statement.render = tokens
  keyword : statement.keyword.text = "let"
  assignment : statement.assignment.text = "="
  terminator : statement.terminator.text = ";"
  pattern : statement.pattern.isEmpty = false
  expression : statement.expression.isEmpty = false

def read (tokens : List LocatedToken) : Except String (Checked tokens) := do
  let first :: rest := tokens | throw "missing source let"
  if keyword : first.text = "let" then
    let binding ← cut "=" rest
    let body ← cut ";" binding.suffix
    let statement : Let := ⟨first,binding.leading,binding.delimiter,body.leading,body.delimiter,body.suffix⟩
    if original : statement.render = first :: rest then
      if pattern : statement.pattern.isEmpty = false then
        if expression : statement.expression.isEmpty = false then
          return ⟨statement,original,keyword,binding.spelling,body.spelling,pattern,expression⟩
        else throw "missing original let expression"
      else throw "missing original let pattern"
    else throw "source let segmentation lost original tokens"
  else throw "source statement is not a let"

theorem Checked.originalTokens {tokens : List LocatedToken} (checked : Checked tokens) :
    checked.statement.render = tokens := checked.original


end Legacy

private inductive Observation (α : Type) where
  | error (message : String)
  | success (value : α)
  deriving BEq, DecidableEq

private def observe {α : Type} : Except String α → Observation α
  | .error error => .error error
  | .ok value => .success value

private def currentCut (separator : String) (tokens : List LocatedToken) :=
  observe ((cut separator tokens).map fun result => (result.leading,result.delimiter,result.suffix))
private def formerCut (separator : String) (tokens : List LocatedToken) :=
  observe ((Legacy.cut separator tokens).map fun result => (result.leading,result.delimiter,result.suffix))
private def currentLet (tokens : List LocatedToken) := observe ((read tokens).map (·.statement))
private def formerLet (tokens : List LocatedToken) := observe ((Legacy.read tokens).map fun result =>
  let s := result.statement
  (⟨s.keyword,s.pattern,s.assignment,s.expression,s.terminator,s.rest⟩ : Let))
private def originalTokens (source : String) : List LocatedToken := (lexLocated source).toOption.getD []

private def sameCut (source : String) : Bool :=
  let tokens := originalTokens source
  ["=",";",":"].all fun separator => currentCut separator tokens == formerCut separator tokens
private def sameLet (source : String) : Bool :=
  let tokens := originalTokens source
  currentLet tokens == formerLet tokens
private def corpus : List String := [
  "", "q", "q;", "=;", "h(q);junk }", "h(q", "h(q];q", "h(q)};q",
  "f[1,2](q);q", "/*λ*/h(q);r", "q;/* after separator */( }",
  "let q=h(q);q", "let q=if b{let q=h(q);q}else{q};q",
  "let(s,q)=qmatch(s,q){0=>f,1=>g};(s,q)", "let =h(q);q", "let q=;q",
  "let q=h(q)", "let (q]=h(q);q", "let q=h(q);junk }", "let (q)=q;q"]
#guard corpus.all sameCut
#guard corpus.all sameLet

-- Exhaustive bounded token corpus includes all three delimiter kinds, both
-- separators, empty input and complete returned spans, not only success bits.
private def alphabet := ["q","=",";","(",")","[","]","{","}"]
private def wordsUpTo (depth : Nat) : List (List String) :=
  (List.range depth).foldl (fun words _ => [] :: alphabet.flatMap fun symbol =>
    words.map (symbol :: ·)) [[]]
private def words := wordsUpTo 4
#guard words.length = 7381
#guard words.all fun word => sameCut (String.intercalate " " word)
#guard words.all fun word => sameLet ("let " ++ String.intercalate " " word)

-- Preserve the existing nesting threshold and the precise diagnostic text.
private def nested (count : Nat) := String.join (List.replicate count "(") ++ "q" ++
  String.join (List.replicate count ")") ++ ";junk }"
#guard sameCut (nested 64)
#guard sameCut (nested 65)
#guard (currentCut ";" (originalTokens (nested 65))) = .error "source statement nesting capacity"
#guard (currentCut ";" (originalTokens "h(q")) = .error "unclosed original statement expression"
#guard (currentCut ";" (originalTokens "h(q)")) = .error "missing original statement separator"
#guard (currentCut ";" (originalTokens "h(q];r")) = .error "mismatched source statement delimiter"
#guard (currentCut ";" (originalTokens "q};r")) = .error "unmatched source statement delimiter"

-- Only the prefix consumes scan fuel; a long/malformed suffix is still shared.
private def longSuffix := "q;" ++ String.join (List.replicate 129 "let q=h(q);") ++ "junk }"
#guard observe ((cutWithFuel 2 ";" (originalTokens longSuffix)).map fun result =>
  (result.leading.map (·.text),result.delimiter.text,result.suffix.map (·.text))) =
  observe ((cut ";" (originalTokens longSuffix)).map fun result =>
  (result.leading.map (·.text),result.delimiter.text,result.suffix.map (·.text)))
#guard match cutWithFuel 1 ";" (originalTokens longSuffix) with
  | .error "source statement traversal fuel" => true
  | _ => false
#guard observe ((readWithFuel 2 (originalTokens "let q=q;junk }")).map (·.statement)) =
  currentLet (originalTokens "let q=q;junk }")
-- Scan fuel remains independent of the original AST-depth fuel contract.
#guard match SourceSyntax.read 2 0 true (originalTokens "let (q)=q;q") with
  | .ok _ => true
  | .error _ => false

#print axioms QleisliKernel.SourceTypes.StatementSyntax.cutWithFuel
#print axioms QleisliKernel.SourceTypes.StatementSyntax.readWithFuel

#print axioms QleisliKernel.SourceTypes.StatementSyntax.cut
#print axioms QleisliKernel.SourceTypes.StatementSyntax.read
#print axioms QleisliKernel.SourceTypes.StatementSyntax.Checked.originalTokens

end QleisliKernel.Tests.StatementSyntaxTests
