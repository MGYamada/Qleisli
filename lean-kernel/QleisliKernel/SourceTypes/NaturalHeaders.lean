import QleisliKernel.SourceTypes.Declarations
import QleisliKernel.SourceTypes.NaturalSyntax
import QleisliKernel.Semantics.SourceAffine

/-! The existing provisional helper surface, read from complete original
headers/bodies. Parsing supplies no generic validity or invocation authority.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.NaturalHeaders
open Semantics.SourceNatural Semantics.SourceAffine

abbrev Predicate := Semantics.SourceNatural.Predicate

structure Helper where
  parameters : List String
  premises : List Predicate
  body : Expr

private structure Groups where
  stack : List String := []
  current : List String := []
  parts : List (List String) := []

private def group (s : Groups) (token : String) : Except String Groups := do
  if token == "(" || token == "[" then
    if s.stack.length ≥ 64 then throw "helper group nesting capacity"
    return {s with stack := (if token == "(" then ")" else "]") :: s.stack,current := token :: s.current}
  if token == ")" || token == "]" then
    let expected :: rest := s.stack | throw "unmatched helper delimiter"
    if token != expected then throw "mismatched helper delimiter"
    return {s with stack := rest,current := token :: s.current}
  if token == "," && s.stack.isEmpty then
    if s.current.isEmpty then throw "empty helper member"
    return {s with current := [],parts := s.current.reverse :: s.parts}
  return {s with current := token :: s.current}

private def groups (tokens : List String) : Except String (List (List String)) := do
  let s ← tokens.foldlM group {}
  if !s.stack.isEmpty then throw "incomplete helper group"
  return (if s.current.isEmpty then s.parts else s.current.reverse :: s.parts).reverse

private def parameters (tokens : List String) : Except String (List String) := do
  let names ← (← groups tokens).mapM fun part => do
    let ["const",name,":","Nat"] := part | throw "helper requires const Nat formals"
    if !identifier name then throw "invalid helper formal"
    return name
  if names.length > 32 then throw "helper formal capacity"
  let unique ← names.foldlM (fun seen name => do
    if seen.contains name then throw "duplicate helper formal"
    return name :: seen) ([] : List String)
  return unique.reverse

private structure CompareScan where
  stack : List String := []
  left : List String := []
  operator : List String := []
  right : List String := []

private def predicateToken (s : CompareScan) (token : String) : Except String CompareScan := do
  if s.stack.isEmpty && ["=","!","<",">"].contains token then
    if !s.right.isEmpty then throw "multiple helper comparisons"
    return {s with operator := token :: s.operator}
  let stack ← if token == "(" || token == "[" then
      if s.stack.length ≥ 64 then throw "helper comparison nesting capacity"
      pure ((if token == "(" then ")" else "]") :: s.stack)
    else if token == ")" || token == "]" then
      let expected :: rest := s.stack | throw "unmatched comparison delimiter"
      if expected != token then throw "mismatched comparison delimiter"
      pure rest
    else pure s.stack
  return if s.operator.isEmpty then {s with stack,left := token :: s.left}
    else {s with stack,right := token :: s.right}

def predicate (tokens : List String) : Except String Predicate := do
  let s ← tokens.foldlM predicateToken {}
  if !s.stack.isEmpty then throw "incomplete helper comparison"
  let comparison ← match s.operator.reverse with
    | ["=","="] => pure Comparison.eq | ["!","="] => pure .ne
    | ["<"] => pure .lt | ["<","="] => pure .le
    | [">"] => pure .gt | [">","="] => pure .ge
    | _ => throw "invalid helper comparison"
  return ⟨← NaturalSyntax.read s.left.reverse,comparison,← NaturalSyntax.read s.right.reverse⟩

/-- `Declaration.body` retains the complete static header and outer braces. -/
def read (declaration : Declaration) : Except String Helper := do
  if declaration.kind != "static-fn" then throw "expected a static Nat helper"
  let (formals,remaining) ← if declaration.body.head? == some "[" then
      let (formals,closing) := declaration.body.drop 1 |>.span (· != "]")
      if closing.head? != some "]" then throw "incomplete helper formals"
      pure (← parameters formals,closing.drop 1)
    else pure ([],declaration.body)
  let "(" :: ")" :: "-" :: ">" :: "Nat" :: remaining := remaining
    | throw "helper requires no runtime parameters and a literal Nat result"
  let (header,opening) := remaining.span (· != "{")
  if opening.head? != some "{" || opening.getLast? != some "}" then
    throw "helper requires a complete expression body"
  let premises ← if header.isEmpty then pure [] else do
    let "requires" :: conditions := header | throw "invalid helper header"
    if conditions.isEmpty then throw "empty helper requires clause"
    (← groups conditions).mapM predicate
  let body ← NaturalSyntax.read (opening.drop 1 |>.dropLast)
  return ⟨formals,premises,body⟩

end QleisliKernel.SourceTypes.NaturalHeaders
