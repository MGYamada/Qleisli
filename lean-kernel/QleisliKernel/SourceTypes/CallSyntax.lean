import QleisliKernel.SourceTypes.Lexer

/-! Original-token call segmentation. Callee and argument expressions
remain intact, including their byte spans. This establishes neither callable
resolution nor expression typing: an opaque callee must never authorize an
interval. In particular, consumed lexical bindings still block primitive lookup.
The enclosing source rule must retain that scope independently of live owners.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.CallSyntax
open QleisliKernel.SourceTypes

structure Argument where
  tokens : List LocatedToken
  followingComma : Option LocatedToken
  deriving BEq, DecidableEq, Repr

def Argument.render (argument : Argument) : List LocatedToken :=
  argument.tokens ++ argument.followingComma.toList

structure Call where
  callee : List LocatedToken
  opening : LocatedToken
  arguments : List Argument
  closing : LocatedToken
  deriving BEq, DecidableEq, Repr

def Call.render (call : Call) : List LocatedToken :=
  call.callee ++ [call.opening] ++ call.arguments.flatMap Argument.render ++ [call.closing]

private def closer (text : String) : Option String :=
  if text == "(" then some ")" else if text == "[" then some "]"
  else if text == "{" then some "}" else none

private def advance (stack : List String) (token : LocatedToken) : Except String (List String) := do
  if let some expected := closer token.text then
    if stack.length ≥ 64 then throw "source delimiter nesting capacity"
    return expected :: stack
  if [")", "]", "}"].contains token.text then
    let expected :: rest := stack | throw "unmatched source delimiter"
    if token.text != expected then throw "mismatched source delimiter"
    return rest
  return stack

private structure Envelope where
  stack : List String := []
  index : Nat := 0
  opening : Option (Nat × LocatedToken) := none
  completed : Option (Nat × LocatedToken × LocatedToken × Nat) := none

private def envelopeStep (s : Envelope) (token : LocatedToken) : Except String Envelope := do
  let opening := if s.stack.isEmpty && (closer token.text).isSome then
      some (s.index,token) else s.opening
  let stack ← advance s.stack token
  let completed := if !s.stack.isEmpty && stack.isEmpty then
      opening.map fun (index,first) => (index,first,token,s.index+1)
    else s.completed
  return ⟨stack,s.index+1,opening,completed⟩

private structure Arguments where
  stack : List String := []
  reversed : List LocatedToken := []
  finished : List Argument := []

private def argumentStep (s : Arguments) (token : LocatedToken) : Except String Arguments := do
  if s.stack.isEmpty && token.text == "," then
    if s.reversed.isEmpty then throw "empty source call argument"
    if s.finished.length ≥ 128 then throw "source argument capacity"
    return ⟨[],[],⟨s.reversed.reverse,some token⟩ :: s.finished⟩
  let stack ← advance s.stack token
  return {s with stack,reversed := token :: s.reversed}

private def arguments (tokens : List LocatedToken) : Except String (List Argument) := do
  let s ← tokens.foldlM argumentStep {}
  if !s.stack.isEmpty then throw "unclosed source argument"
  let result := if s.reversed.isEmpty then s.finished.reverse
    else (⟨s.reversed.reverse,none⟩ :: s.finished).reverse
  if result.length > 128 then throw "source argument capacity"
  return result

structure Checked (tokens : List LocatedToken) where
  call : Call
  original : call.render = tokens
  hasCallee : call.callee.isEmpty = false
  delimiters : call.opening.text = "(" ∧ call.closing.text = ")"

/-- The context coordinate names the original first callee token.
Grouping spans and the opening parenthesis are different coordinates. This
accessor supplies no callable-name, owner, effect or execution authority. -/
def Checked.calleeToken {tokens : List LocatedToken} (checked : Checked tokens) : LocatedToken :=
  checked.call.callee.head (by
    intro absent
    have present := checked.hasCallee
    simp [absent] at present)

def Checked.calleeOffset {tokens : List LocatedToken} (checked : Checked tokens) : Nat :=
  checked.calleeToken.span.startByte

theorem Checked.calleeToken_original {tokens : List LocatedToken} (checked : Checked tokens) :
    tokens.head? = some checked.calleeToken := by
  calc
    tokens.head? = checked.call.render.head? := congrArg List.head? checked.original.symm
    _ = some checked.calleeToken := by
      cases original : checked.call.callee with
      | nil =>
        have present := checked.hasCallee
        simp [original] at present
      | cons first rest => simp [Call.render, Checked.calleeToken, original]

/-- Split the final outer application, preserving nested calls/static expressions
as original tokens. Qualified lookup, implicit prelude, primitive fallback,
lexical shadowing, owner/effect rules and all body equations remain separate. -/
def read (tokens : List LocatedToken) : Except String (Checked tokens) := do
  let envelope ← tokens.foldlM envelopeStep {}
  if !envelope.stack.isEmpty then throw "unclosed source call"
  let some (start,opening,closing,finish) := envelope.completed
    | throw "source expression has no complete call"
  if finish != tokens.length || start == 0 then throw "source expression is not a complete application"
  let args ← arguments ((tokens.drop (start+1)).take (finish-start-2))
  let call : Call := ⟨tokens.take start,opening,args,closing⟩
  if original : call.render = tokens then
    if hasCallee : call.callee.isEmpty = false then
      if delimiters : call.opening.text = "(" ∧ call.closing.text = ")" then
        return ⟨call,original,hasCallee,delimiters⟩
      else throw "source expression does not end in call parentheses"
    else throw "source call has no callee"
  else throw "source call segmentation lost original tokens"

theorem Checked.originalTokens {tokens : List LocatedToken} (checked : Checked tokens) :
    checked.call.render = tokens := checked.original

/-- Parenthesized expressions share the exact balanced comma splitter with
call arguments, including braces in nested qmatch expressions. -/
structure Group where
  opening : LocatedToken
  arguments : List Argument
  closing : LocatedToken
  deriving BEq, DecidableEq, Repr

def Group.render (group : Group) : List LocatedToken :=
  [group.opening] ++ group.arguments.flatMap Argument.render ++ [group.closing]

structure CheckedGroup (tokens : List LocatedToken) where
  group : Group
  original : group.render = tokens
  delimiters : group.opening.text = "(" ∧ group.closing.text = ")"

def readGroup (tokens : List LocatedToken) : Except String (CheckedGroup tokens) := do
  let envelope ← tokens.foldlM envelopeStep {}
  if !envelope.stack.isEmpty then throw "unclosed source group"
  let some (start,opening,closing,finish) := envelope.completed
    | throw "source expression has no complete group"
  if start != 0 || finish != tokens.length then throw "source expression is not one complete group"
  let args ← arguments ((tokens.drop 1).take (finish-2))
  let group : Group := ⟨opening,args,closing⟩
  if original : group.render = tokens then
    if delimiters : opening.text = "(" ∧ closing.text = ")" then
      return ⟨group,original,delimiters⟩
    else throw "source group does not use parentheses"
  else throw "source group lost original tokens"

end QleisliKernel.SourceTypes.CallSyntax
