import QleisliKernel.SourceTypes.CallSyntax

/-! Complete original block slices for ordinary if and coherent basis lifting.
No branch is selected and no basis owner is observed by this syntax reader.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceControlSyntax

private def closing (text : String) : Option String :=
  if text == "(" then some ")" else if text == "[" then some "]"
  else if text == "{" then some "}" else none

private def cut : Nat → String → List String → List LocatedToken → List LocatedToken →
    Except String (List LocatedToken × LocatedToken × List LocatedToken) :=
  Nat.rec (fun _ _ _ _ => throw "original control delimiter fuel")
    (fun _ recurse delimiter stack tokens reversed => do
      let token :: rest := tokens | throw "missing original control delimiter"
      if stack.isEmpty && token.text == delimiter then return (reversed.reverse,token,rest)
      if let some close := closing token.text then recurse delimiter (close :: stack) rest (token :: reversed)
      else if [")","]","}"].contains token.text then do
        let close :: stack := stack | throw "unmatched original control delimiter"
        if token.text != close then throw "mismatched original control delimiter"
        recurse delimiter stack rest (token :: reversed)
      else recurse delimiter stack rest (token :: reversed))

/-- Split one complete original top-level delimiter, respecting nested source
parentheses, brackets and braces. The caller retains exact reconstruction. -/
def delimiter (text : String) (tokens : List LocatedToken) :
    Except String (List LocatedToken × LocatedToken × List LocatedToken) :=
  cut (tokens.length+1) text [] tokens []

structure Conditional where
  keyword : LocatedToken
  condition : List LocatedToken
  thenOpen : LocatedToken
  thenBody : List LocatedToken
  thenClose : LocatedToken
  otherwise : LocatedToken
  elseOpen : LocatedToken
  elseBody : List LocatedToken
  elseClose : LocatedToken

def Conditional.render (parts : Conditional) : List LocatedToken :=
  [parts.keyword] ++ parts.condition ++ [parts.thenOpen] ++ parts.thenBody ++
    [parts.thenClose,parts.otherwise,parts.elseOpen] ++ parts.elseBody ++ [parts.elseClose]

def Conditional.spelling (parts : Conditional) : Bool :=
  parts.keyword.text == "if" && parts.thenOpen.text == "{" && parts.thenClose.text == "}" &&
    parts.otherwise.text == "else" && parts.elseOpen.text == "{" && parts.elseClose.text == "}"

/-- Shared original block splitter. A caller adding a static marker must retain
that marker and check its complete original reconstruction separately. -/
def conditionalParts (keyword : LocatedToken) (tokens : List LocatedToken) : Except String Conditional := do
  let (condition,thenOpen,rest) ← cut (tokens.length+1) "{" [] tokens []
  let (thenBody,thenClose,rest) ← cut (tokens.length+1) "}" [] rest []
  let otherwise :: elseOpen :: rest := rest | throw "missing original else block"
  let (elseBody,elseClose,suffix) ← cut (tokens.length+1) "}" [] rest []
  if !suffix.isEmpty || condition.isEmpty then throw "incomplete original if expression"
  return ⟨keyword,condition,thenOpen,thenBody,thenClose,otherwise,elseOpen,elseBody,elseClose⟩

private def conditional (tokens : List LocatedToken) : Except String Conditional := do
  let keyword :: rest := tokens | throw "missing original if keyword"
  conditionalParts keyword rest

structure CheckedConditional (tokens : List LocatedToken) where
  parts : Conditional
  original : parts.render = tokens
  spelling : parts.spelling = true

def readConditional (tokens : List LocatedToken) : Except String (CheckedConditional tokens) := do
  let parts ← conditional tokens
  if original : parts.render = tokens then
    if spelling : parts.spelling = true then return ⟨parts,original,spelling⟩
    else throw "original if spelling"
  else throw "original if token reconstruction"

structure Basis where
  keyword : LocatedToken
  input : List LocatedToken
  binder : LocatedToken
  pattern : List LocatedToken
  opening : LocatedToken
  body : List LocatedToken
  closing : LocatedToken

def Basis.render (parts : Basis) : List LocatedToken :=
  [parts.keyword] ++ parts.input ++ [parts.binder] ++ parts.pattern ++
    [parts.opening] ++ parts.body ++ [parts.closing]

def Basis.spelling (parts : Basis) : Bool :=
  parts.keyword.text == "basis" && parts.binder.text == "as" &&
    parts.opening.text == "{" && parts.closing.text == "}"

private def basis (tokens : List LocatedToken) : Except String Basis := do
  let keyword :: rest := tokens | throw "missing original basis keyword"
  let (input,binder,rest) ← cut (tokens.length+1) "as" [] rest []
  let (pattern,opening,rest) ← cut (tokens.length+1) "{" [] rest []
  let (body,closing,suffix) ← cut (tokens.length+1) "}" [] rest []
  if !suffix.isEmpty || input.isEmpty || pattern.isEmpty then throw "incomplete original basis expression"
  return ⟨keyword,input,binder,pattern,opening,body,closing⟩

structure CheckedBasis (tokens : List LocatedToken) where
  parts : Basis
  original : parts.render = tokens
  spelling : parts.spelling = true

def readBasis (tokens : List LocatedToken) : Except String (CheckedBasis tokens) := do
  let parts ← basis tokens
  if original : parts.render = tokens then
    if spelling : parts.spelling = true then return ⟨parts,original,spelling⟩
    else throw "original basis spelling"
  else throw "original basis token reconstruction"

end QleisliKernel.SourceTypes.SourceControlSyntax
