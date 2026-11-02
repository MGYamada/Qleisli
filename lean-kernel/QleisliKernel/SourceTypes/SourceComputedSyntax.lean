import QleisliKernel.SourceTypes.SourceControlSyntax
import QleisliKernel.SourceTypes.CallName

/-! Exact original scoped compute/use/uncompute syntax. This is neither a
closure nor a synthetic function call. Predicate, logical reference and body
remain original slices; typing and exact cleanup are separate obligations.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceComputedSyntax

structure Reference where
  argument : CallSyntax.Argument
  name : CallName.Name argument.tokens

structure Parts where
  headerTokens : List LocatedToken
  header : CallSyntax.Checked headerTokens
  source : CallSyntax.Argument
  predicate : Reference
  logical : Option Reference
  opening : LocatedToken
  firstPipe : LocatedToken
  data : Option LocatedToken
  comma : Option LocatedToken
  auxiliary : LocatedToken
  lastPipe : LocatedToken
  body : List LocatedToken
  closing : LocatedToken

def Parts.render (parts : Parts) : List LocatedToken :=
  parts.headerTokens ++ [parts.opening,parts.firstPipe] ++ parts.data.toList ++
    parts.comma.toList ++ [parts.auxiliary,parts.lastPipe] ++ parts.body ++ [parts.closing]

def Parts.spelling (parts : Parts) : Bool :=
  parts.header.call.callee.map (·.text) == ["with_computed"] &&
  parts.opening.text == "{" && parts.firstPipe.text == "|" && parts.lastPipe.text == "|" &&
  parts.closing.text == "}" && identifier parts.auxiliary.text &&
  parts.source.followingComma.map (·.text) == some "," &&
  match parts.logical,parts.data,parts.comma with
  | none,none,none => parts.predicate.argument.followingComma.isNone
  | some logical,some data,some comma => identifier data.text && data.text != parts.auxiliary.text &&
      comma.text == "," && parts.predicate.argument.followingComma.map (·.text) == some "," &&
      logical.argument.followingComma.isNone
  | _,_,_ => false

structure Checked (tokens : List LocatedToken) where
  parts : Parts
  original : parts.render = tokens
  arguments : parts.header.call.arguments =
    [parts.source,parts.predicate.argument] ++ (parts.logical.toList.map (·.argument))
  spelling : parts.spelling = true

private def reference (argument : CallSyntax.Argument) : Except String Reference := do
  return ⟨argument,← CallName.readName argument.tokens⟩

private def parse (tokens : List LocatedToken) : Except String Parts := do
  let (headerTokens,opening,rest) ← SourceControlSyntax.delimiter "{" tokens
  let header ← CallSyntax.read headerTokens
  let (source,predicate,logical) ← match header.call.arguments with
    | [source,predicate] => pure (source,← reference predicate,none)
    | [source,predicate,logical] => pure (source,← reference predicate,some (← reference logical))
    | _ => throw "computed scope requires source, predicate and optional logical reference"
  let firstPipe :: rest := rest | throw "missing original computed binder pipe"
  let (binders,lastPipe,rest) ← SourceControlSyntax.delimiter "|" rest
  let (body,closing,suffix) ← SourceControlSyntax.delimiter "}" rest
  if !suffix.isEmpty then throw "trailing original computed scope tokens"
  let (data,comma,auxiliary) ← match logical,binders with
    | none,[auxiliary] => pure (none,none,auxiliary)
    | some _,[data,comma,auxiliary] => pure (some data,some comma,auxiliary)
    | _,_ => throw "original computed scope binder shape"
  return ⟨headerTokens,header,source,predicate,logical,opening,firstPipe,data,comma,auxiliary,lastPipe,body,closing⟩

def read (tokens : List LocatedToken) : Except String (Checked tokens) := do
  let parts ← parse tokens
  if original : parts.render = tokens then
    if arguments : parts.header.call.arguments =
        [parts.source,parts.predicate.argument] ++ (parts.logical.toList.map (·.argument)) then
      if spelling : parts.spelling = true then return ⟨parts,original,arguments,spelling⟩
      else throw "original computed scope spelling"
    else throw "original computed scope argument correspondence"
  else throw "original computed scope reconstruction"

end QleisliKernel.SourceTypes.SourceComputedSyntax
