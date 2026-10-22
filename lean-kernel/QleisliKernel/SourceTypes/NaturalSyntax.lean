import QleisliKernel.SourceTypes.Lexer
import QleisliKernel.Semantics.SourceNatural

/-! Original existing Nat syntax only. One token pass retains precedence,
left association, complete paths and positional helper arguments. Binding,
affine normalization and generic helper obligations are separate checks.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.NaturalSyntax
open Semantics.SourceNatural

private structure Node where
  expression : Expr
  depth : Nat

private inductive Operator where
  | add | sub | mul
  deriving BEq

private def Operator.level : Operator → Nat
  | .add | .sub => 1
  | .mul => 2

private def combine (op : Operator) (values : List Node) : Except String (List Node) := do
  let b :: a :: rest := values | throw "missing natural operand"
  let depth := 1 + max a.depth b.depth
  if depth > 128 then throw "natural expression depth capacity"
  let expression := match op with
    | .add => Expr.add a.expression b.expression
    | .sub => Expr.sub a.expression b.expression
    | .mul => Expr.mul a.expression b.expression
  return ⟨expression,depth⟩ :: rest

private inductive FrameKind where
  | parenthesis | arguments (path : Path)

private structure Frame where
  kind : FrameKind
  values : List Node
  operators : List Operator
  arguments : List Node := []

private structure Call where
  path : Path
  arguments : List Node

private structure Scan where
  values : List Node := []
  operators : List Operator := []
  frames : List Frame := []
  operand : Bool := true
  pending : Path := [] -- reversed, while reading a possibly qualified name
  qualifier : Bool := false
  runtimeOpen : Option Call := none
  runtimeClose : Option Call := none

private def push (s : Scan) (node : Node) : Except String Scan := do
  if !s.operand then throw "missing natural operator"
  return {s with values := node :: s.values,operand := false}

private def flush (s : Scan) : Except String Scan := do
  if s.qualifier then throw "incomplete natural path"
  if s.pending.isEmpty then return s
  let next ← push {s with pending := []} ⟨.name s.pending.reverse,1⟩
  return next

private def reduce (s : Scan) (level : Nat) : Except String Scan := do
  let (operators,rest) := s.operators.span (fun op => op.level ≥ level)
  let values ← operators.foldlM (fun values op => combine op values) s.values
  return {s with values,operators := rest}

private def finish (s : Scan) : Except String Node := do
  if s.operand then throw "incomplete natural expression"
  let s ← reduce s 0
  let [value] := s.values | throw "incomplete natural reduction"
  return value

private def callNode (call : Call) : Except String Node := do
  let depth := 1 + (call.arguments.map Node.depth).foldl max 0
  if depth > 128 then throw "natural call depth capacity"
  return ⟨.call call.path (call.arguments.map Node.expression),depth⟩

/-- Read the canonical original decimal token, before any arithmetic. This is
an i128 literal bound, not the physical width or the final u32 field bound. -/
def decimal (literal : String) : Except String Nat := do
  let chars := literal.toList
  if chars.isEmpty || (chars != ['0'] && chars.head? == some '0') then
    throw "noncanonical natural literal"
  chars.foldlM (fun value char => do
    if char < '0' || char > '9' then throw "invalid natural literal"
    let next := value * 10 + (char.toNat - '0'.toNat)
    if next > 170141183460469231731687303715884105727 then
      throw "natural literal exceeds i128"
    return next) 0

private def openFrame (s : Scan) (kind : FrameKind) : Except String Scan := do
  if !s.operand then throw "unexpected natural group"
  if s.frames.length ≥ 64 then throw "natural nesting capacity"
  return {s with frames := ⟨kind,s.values,s.operators,[]⟩ :: s.frames,values := [],operators := [],pending := [],qualifier := false}

private def restore (s : Scan) (frame : Frame) (rest : List Frame) : Scan :=
  {s with values := frame.values,operators := frame.operators,frames := rest,operand := true}

private def step (s : Scan) (token : String) : Except String Scan := do
  if let some call := s.runtimeOpen then
    if token != "(" then throw "natural call requires empty runtime arguments"
    return {s with runtimeOpen := none,runtimeClose := some call}
  if let some call := s.runtimeClose then
    if token != ")" then throw "natural call requires empty runtime arguments"
    push {s with runtimeClose := none} (← callNode call)
  else
    -- A name remains pending until qualification, call syntax or an operator
    -- determines its role. There is never a failed-category fallback here.
    if !s.pending.isEmpty then
      if s.qualifier then
        if !identifier token && !(s.pending == ["std"] && ["basis","observe","classical"].contains token) then
          throw "invalid natural qualifier"
        return {s with pending := token :: s.pending,qualifier := false}
      if token == "::" then return {s with qualifier := true}
      if token == "[" then
        return ← openFrame {s with pending := []} (.arguments s.pending.reverse)
      if token == "(" then
        return {s with pending := [],runtimeClose := some ⟨s.pending.reverse,[]⟩}
    let s ← flush s
    if token == "(" then return ← openFrame s .parenthesis
    if token == "," then
      let frame :: rest := s.frames | throw "unexpected natural argument separator"
      let .arguments _ := frame.kind | throw "unexpected natural tuple"
      let argument ← finish s
      return {s with values := [],operators := [],operand := true,frames := {frame with arguments := argument :: frame.arguments} :: rest}
    if token == ")" || token == "]" then
      let frame :: rest := s.frames | throw "unmatched natural delimiter"
      match frame.kind with
      | .parenthesis =>
        if token != ")" then throw "mismatched natural delimiter"
        push (restore s frame rest) (← finish s)
      | .arguments path =>
        if token != "]" then throw "mismatched natural delimiter"
        let args ← if s.operand then
            if s.values.isEmpty && s.operators.isEmpty && frame.arguments.isEmpty then pure []
            else throw "incomplete natural arguments"
          else pure ((← finish s) :: frame.arguments)
        return {restore s frame rest with runtimeOpen := some ⟨path,args.reverse⟩}
    else if token == "+" || token == "-" || token == "*" then
      if s.operand then throw "missing natural operand"
      let op := if token == "+" then Operator.add else if token == "-" then .sub else .mul
      let s ← reduce s op.level
      return {s with operators := op :: s.operators,operand := true}
    else
      if !s.operand then throw "missing natural operator"
      -- Every atom occupies one common parser nesting level, including leaves.
      if s.frames.length ≥ 64 then throw "natural nesting capacity"
      if identifier token then return {s with pending := [token]}
      push s ⟨.number (← decimal token),1⟩

/-- Consume the complete expression; brackets describe static call arguments,
parentheses group arithmetic or form the mandatory empty runtime call list. -/
def read (tokens : List String) : Except String Expr := do
  let s ← tokens.foldlM step {}
  if !s.frames.isEmpty || s.runtimeOpen.isSome || s.runtimeClose.isSome then
    throw "incomplete natural group/call"
  let s ← flush s
  return (← finish s).expression

end QleisliKernel.SourceTypes.NaturalSyntax
