import QleisliKernel.SourceTypes.CallSyntax

/-! Original ordinary Boolean syntax, retaining child slices and precedence.
Typing and effects remain the enclosing runtime evaluator's obligations.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceBoolean

inductive Operator where
  | not | xor | and
  deriving BEq, DecidableEq, Repr

def Operator.name : Operator → String
  | .not => "not" | .xor => "xor" | .and => "and"

structure Syntax (tokens : List LocatedToken) where
  operator : Operator
  keyword : LocatedToken
  parts : List (List LocatedToken)
  original : match operator,parts with
    | .not,[argument] => tokens = keyword :: argument ∧ keyword.text = "not"
    | .xor,[left,right] => tokens = left ++ keyword :: right ∧ keyword.text = "xor"
    | .and,[left,right] => tokens = left ++ keyword :: right ∧ keyword.text = "and"
    | _,_ => False

private def closing (text : String) : Option String :=
  if text == "(" then some ")" else if text == "[" then some "]"
  else if text == "{" then some "}" else none

private def split : Nat → String → List String → List LocatedToken → List LocatedToken →
    Option (List LocatedToken × LocatedToken × List LocatedToken) :=
  Nat.rec (fun _ _ _ _ => none) (fun _ recurse operator stack rest reversed => do
    let token :: tail := rest | none
    if stack.isEmpty && token.text == operator then return (reversed.reverse,token,tail)
    if let some close := closing token.text then recurse operator (close :: stack) tail (token :: reversed)
    else if [")","]","}"].contains token.text then do
      let close :: stack := stack | none
      if token.text != close then none else recurse operator stack tail (token :: reversed)
    else recurse operator stack tail (token :: reversed))

def read (tokens : List LocatedToken) : Option (Syntax tokens) := do
  if let some (left,keyword,right) := split (tokens.length+1) "xor" [] tokens [] then
    if original : tokens = left ++ keyword :: right ∧ keyword.text = "xor" then
      return ⟨.xor,keyword,[left,right],original⟩
    else none
  else if let some (left,keyword,right) := split (tokens.length+1) "and" [] tokens [] then
    if original : tokens = left ++ keyword :: right ∧ keyword.text = "and" then
      return ⟨.and,keyword,[left,right],original⟩
    else none
  else
    let keyword :: rest := tokens | none
    if original : tokens = keyword :: rest ∧ keyword.text = "not" then
      return ⟨.not,keyword,[rest],⟨rfl,original.2⟩⟩
    else none

end QleisliKernel.SourceTypes.SourceBoolean
