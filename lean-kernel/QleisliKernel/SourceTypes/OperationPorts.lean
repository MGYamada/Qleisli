import QleisliKernel.SourceTypes.Lexer

/-! Original separate operation ports and optional declared Meaning path.
Only top-level arrows/commas separate these clauses; nested type/Nat tokens
remain unchanged. This parser grants no effect, access or equality evidence.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.OperationPorts

structure Parsed where
  input : List String
  output : List String
  meaning : Option (List String)
  deriving BEq, DecidableEq, Repr

private structure State where
  input : List String := []
  output : List String := []
  meaning : List String := []
  stack : List String := []
  arrow : Bool := false
  afterArrow : Bool := false
  afterComma : Bool := false

private def token (state : State) (text : String) : Except String State := do
  if state.arrow then
    if text != ">" then throw "incomplete original operation arrow"
    return {state with arrow := false,afterArrow := true}
  if state.stack.isEmpty && text == "," then
    if state.afterComma then throw "multiple original Meaning clauses"
    return {state with afterComma := true}
  if state.stack.isEmpty && text == "-" && !state.afterComma then
    if state.afterArrow then throw "multiple original operation arrows"
    return {state with arrow := true}
  let stack ← if ["(","<","["].contains text then
      pure ((if text == "(" then ")" else if text == "<" then ">" else "]") :: state.stack)
    else if [")",">","]"].contains text then do
      let expected :: rest := state.stack | throw "unmatched operation type delimiter"
      if text != expected then throw "mismatched operation type delimiter"
      pure rest
    else pure state.stack
  return if state.afterComma then {state with stack,meaning := state.meaning ++ [text]}
    else if state.afterArrow then {state with stack,output := state.output ++ [text]}
    else {state with stack,input := state.input ++ [text]}

def read (tokens : List String) : Except String Parsed := do
  let state ← tokens.foldlM token {}
  if state.input.isEmpty || !state.stack.isEmpty || state.arrow then throw "incomplete original operation kind"
  if state.afterArrow && state.output.isEmpty then throw "missing original operation codomain"
  if state.afterComma && state.meaning.isEmpty then throw "missing original Meaning refinement"
  return ⟨state.input,if state.afterArrow then state.output else state.input,
    if state.afterComma then some state.meaning else none⟩

end QleisliKernel.SourceTypes.OperationPorts
