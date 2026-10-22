import QleisliKernel.SourceTypes.Lexer

/-! Original transparent import paths. Reversed paths share their prefixes;
the common grouped-import copy/nesting bounds still apply before expansion.
No alias gains a target, visibility or semantic authority from this parser.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.Imports

inductive Position where
  | item | segment | separator | groupEnd
  deriving BEq, Repr

private structure Group where
  names : List String
  count : Nat
  bytes : Nat
  nonempty : Bool := false

private structure Scan where
  position : Position := .item
  names : List String := []
  count : Nat := 0
  bytes : Nat := 0
  groups : List Group := []
  paths : List (List String) := []
  copiedIdentifiers : Nat := 0
  copiedBytes : Nat := 0

private def finish (s : Scan) : Except String Scan := do
  if s.count < 2 then throw "imports require a module and declaration"
  let groups := match s.groups with
    | [] => []
    | first :: rest => {first with nonempty := true} :: rest
  return {s with paths := s.names :: s.paths,groups}

private def reset (s : Scan) : Scan :=
  match s.groups with
  | [] => {s with names := [],count := 0,bytes := 0,position := .item}
  | group :: _ => {s with names := group.names,count := group.count,bytes := group.bytes,position := .item}

private def step (s : Scan) (token : String) : Except String Scan := do
  if token == "{" then
    if s.position != .item && s.position != .separator then throw "unexpected import group"
    if s.groups.length ≥ 64 then throw "import nesting capacity"
    return {s with groups := ⟨s.names,s.count,s.bytes,false⟩ :: s.groups,position := .item}
  if token == "," || token == "}" then
    if s.groups.isEmpty then throw "unexpected import separator"
    let s ← if s.position == .segment then finish s else pure s
    if s.position != .segment && s.position != .groupEnd && s.position != .item then
      throw "incomplete import path"
    let group :: rest := s.groups | throw "missing import group"
    if !group.nonempty then throw "empty import group/member"
    if token == "," then
      if s.position == .item then throw "empty import member"
      return reset s
    let groups := match rest with
      | [] => []
      | first :: tail => {first with nonempty := true} :: tail
    return {reset {s with groups} with position := .groupEnd}
  if token == "::" then
    if s.position != .segment then throw "unexpected import qualifier"
    return {s with position := .separator}
  if s.position != .item && s.position != .separator then throw "missing import separator"
  if !identifier token && !(s.names == ["std"] && ["basis","observe","classical"].contains token) then
    throw "invalid import identifier"
  let copiedIdentifiers := s.copiedIdentifiers + if s.position == .item then s.count else 0
  let copiedBytes := s.copiedBytes + if s.position == .item then s.bytes else 0
  if copiedIdentifiers > 65536 || copiedBytes > 1048576 then throw "import prefix capacity"
  return {s with names := token :: s.names,count := s.count+1,bytes := s.bytes+token.utf8ByteSize,position := .segment,copiedIdentifiers := copiedIdentifiers,copiedBytes := copiedBytes}

/-- Declaration order, with each path reversed: its bound spelling is the head.
Only a visited binding needs to materialize its complete qualified path. -/
def read (tokens : List String) : Except String (List (List String)) := do
  let s ← tokens.foldlM step {}
  if !s.groups.isEmpty then throw "unclosed import group"
  let s ← if s.position == .segment then finish s
    else if s.position == .groupEnd then pure s else throw "incomplete import"
  return s.paths.reverse

end QleisliKernel.SourceTypes.Imports
