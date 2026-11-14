import QleisliKernel.SourceTypes.SourceControlSyntax
import QleisliKernel.SourceTypes.CallName

/-! Original workspace arguments, ordered binders and body tokens.
Restoration, effects and owner flow have separate checking obligations.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceWorkspaceSyntax

structure Parts where
  headerTokens : List LocatedToken
  header : CallSyntax.Checked headerTokens
  data : CallSyntax.Argument
  dirty : Option CallSyntax.Argument
  logical : CallSyntax.Argument
  logicalName : CallName.Name logical.tokens
  opening : LocatedToken
  firstPipe : LocatedToken
  dataBinder : LocatedToken
  comma : LocatedToken
  scratchBinder : LocatedToken
  lastPipe : LocatedToken
  body : List LocatedToken
  closing : LocatedToken

def Parts.render (parts : Parts) : List LocatedToken :=
  parts.headerTokens ++ [parts.opening,parts.firstPipe,parts.dataBinder,parts.comma,
    parts.scratchBinder,parts.lastPipe] ++ parts.body ++ [parts.closing]

def Parts.spelling (parts : Parts) : Bool :=
  parts.header.call.callee.map (·.text) == [if parts.dirty.isSome then "dirty" else "clean"] &&
  parts.opening.text == "{" && parts.firstPipe.text == "|" && parts.comma.text == "," &&
  parts.lastPipe.text == "|" && parts.closing.text == "}" &&
  identifier parts.dataBinder.text && identifier parts.scratchBinder.text &&
  parts.dataBinder.text != parts.scratchBinder.text &&
  parts.data.followingComma.isSome && parts.dirty.toList.all (·.followingComma.isSome) &&
  parts.logical.followingComma.isNone

structure Checked (tokens : List LocatedToken) where
  parts : Parts
  original : parts.render = tokens
  arguments : parts.header.call.arguments = [parts.data] ++ parts.dirty.toList ++ [parts.logical]
  spelling : parts.spelling = true

private def parse (tokens : List LocatedToken) : Except String Parts := do
  let (headerTokens,opening,rest) ← SourceControlSyntax.delimiter "{" tokens
  let header ← CallSyntax.read headerTokens
  let (data,dirty,logical) ← match header.call.arguments with
    | [data,logical] => pure (data,none,logical)
    | [data,dirty,logical] => pure (data,some dirty,logical)
    | _ => throw "workspace scope requires data, an existing owner for dirty, and a logical reference"
  let logicalName ← CallName.readName logical.tokens
  let firstPipe :: rest := rest | throw "missing original workspace binder pipe"
  let (binders,lastPipe,rest) ← SourceControlSyntax.delimiter "|" rest
  let [dataBinder,comma,scratchBinder] := binders | throw "original workspace binder shape"
  let (body,closing,suffix) ← SourceControlSyntax.delimiter "}" rest
  if !suffix.isEmpty then throw "trailing original workspace scope tokens"
  return ⟨headerTokens,header,data,dirty,logical,logicalName,opening,firstPipe,
    dataBinder,comma,scratchBinder,lastPipe,body,closing⟩

def read (tokens : List LocatedToken) : Except String (Checked tokens) := do
  let parts ← parse tokens
  if original : parts.render = tokens then
    if arguments : parts.header.call.arguments = [parts.data] ++ parts.dirty.toList ++ [parts.logical] then
      if spelling : parts.spelling = true then return ⟨parts,original,arguments,spelling⟩
      else throw "original workspace scope spelling"
    else throw "original workspace argument correspondence"
  else throw "original workspace scope reconstruction"

end QleisliKernel.SourceTypes.SourceWorkspaceSyntax
