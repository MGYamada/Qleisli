import QleisliKernel.SourceTypes.CallSyntax
import QleisliKernel.SourceTypes.CallName
import QleisliKernel.SourceTypes.NaturalSyntax
import QleisliKernel.SourceTypes.StatementSyntax
import QleisliKernel.Semantics.Finite

/-! Original ordered `ctrl`/`excl` call syntax. Owner and callee resolution,
selector evaluation and the actual Raw interval are separate obligations.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.AccessSyntax

open QleisliKernel.SourceTypes
abbrev Natural := Semantics.SourceNatural.Expr

inductive Role where
  | ctrl | excl
  deriving BEq, Repr

inductive Selection where
  | whole
  | index (axis : Natural)
  | slice (start stop : Natural)

private def readRole (token : LocatedToken) : Except String Role :=
  match token.text with
  | "ctrl" => .ok .ctrl
  | "excl" => .ok .excl
  | _ => .error "original quantum access requires ctrl or excl"

private def readSelection (tokens : List LocatedToken) : Except String Selection := do
  if tokens.isEmpty then return .whole
  let opening :: tail := tokens | throw "missing original selector"
  let closing :: reversed := tail.reverse | throw "missing selector closing bracket"
  if opening.text != "[" || closing.text != "]" then throw "invalid original selector brackets"
  let inside := reversed.reverse
  let (first,rest) := inside.span (fun token => token.text != ".")
  let start ← NaturalSyntax.read (first.map (·.text))
  if rest.isEmpty then return .index start
  let left :: right :: stop := rest | throw "incomplete original slice delimiter"
  if left.text != "." || right.text != "." || left.span.endByte != right.span.startByte then
    throw "invalid original slice delimiter"
  return .slice start (← NaturalSyntax.read (stop.map (·.text)))

structure Argument (tokens : List LocatedToken) where
  marker : LocatedToken
  owner : LocatedToken
  selector : List LocatedToken
  original : marker :: owner :: selector = tokens
  role : Role
  roleRead : readRole marker = .ok role
  ownerName : identifier owner.text = true
  selection : Selection
  selectionRead : readSelection selector = .ok selection

def readArgument (tokens : List LocatedToken) : Except String (Argument tokens) := do
  let marker :: owner :: selector := tokens | throw "incomplete original access argument"
  if ownerName : identifier owner.text = true then
    match roleRead : readRole marker, selectionRead : readSelection selector with
    | .ok role, .ok selection => return ⟨marker,owner,selector,rfl,role,roleRead,ownerName,selection,selectionRead⟩
    | .error error, _ | _, .error error => throw error
  else throw "original access requires a lexical owner name"

inductive Callee (tokens : List LocatedToken) where
  | named (name : CallName.Name tokens)
  | specialized (applied : CallSyntax.StaticChecked tokens) (name : CallName.Name applied.call.callee)

structure CheckedCall (tokens : List LocatedToken) where
  parsed : CallSyntax.Checked tokens
  callee : Callee parsed.call.callee
  arguments : List (Sigma Argument)
  original : arguments.map Sigma.fst = parsed.call.arguments.map (·.tokens)

def readCall (tokens : List LocatedToken) : Except String (CheckedCall tokens) := do
  let parsed ← CallSyntax.read tokens
  let callee ← (match CallSyntax.readStatic parsed.call.callee with
    | .ok applied => (CallName.readName applied.call.callee).map (Callee.specialized applied)
    | .error _ => (CallName.readName parsed.call.callee).map Callee.named)
  let arguments := parsed.call.arguments.map (·.tokens)
  if arguments.isEmpty || arguments.length > 64 then throw "original access call arity"
  -- The current access syntax has no trailing comma.
  if (parsed.call.arguments.getLast?.bind (·.followingComma)).isSome then
    throw "trailing comma in original access call"
  let checked ← arguments.mapM fun tokens => do
    return ⟨tokens,← readArgument tokens⟩
  if original : checked.map Sigma.fst = arguments then return ⟨parsed,callee,checked,original⟩
  else throw "original access argument order changed"

structure Adjacent (tokens : List LocatedToken) where
  first : StatementSyntax.Cut ";" tokens
  second : StatementSyntax.Cut ";" first.suffix
  before : CheckedCall first.leading
  after : CheckedCall second.leading

/-- Read the first two written access statements in order, retaining the exact
suffix for the caller to check. No statement is skipped to find a later call. -/
def readAdjacent (tokens : List LocatedToken) : Except String (Adjacent tokens) := do
  let prepared := StatementSyntax.prepare (tokens.length + 1)
  let first ← StatementSyntax.cutPrepared prepared ";" tokens
  let second ← StatementSyntax.cutPrepared prepared ";" first.suffix
  return ⟨first,second,← readCall first.leading,← readCall second.leading⟩

theorem Adjacent.original {tokens} (checked : Adjacent tokens) :
    checked.before.parsed.call.render ++ [checked.first.delimiter] ++
      (checked.after.parsed.call.render ++ [checked.second.delimiter] ++ checked.second.suffix) = tokens := by
  rw [checked.before.parsed.original,checked.after.parsed.original,checked.second.original]
  exact checked.first.original

/-- An owner in the caller's ordered frame. The consumer must establish this
entry from the original binding and the actual native scope. -/
structure Owner where
  binder : LocatedToken
  basis : Semantics.Finite.Basis
  wires : List Nat
  deriving BEq, Repr

structure Place where
  role : Role
  owner : Owner
  basis : Semantics.Finite.Basis
  axes : List Nat
  whole : Bool
  deriving BEq, Repr

open Semantics.SourceNatural in
/-- Instantiate a written selector in an explicit static environment and keep
the caller's ordered wire labels, including owners with no physical axes. -/
def Argument.place {tokens} (argument : Argument tokens) (lookup : String → Option Owner)
    (names : Names) (calls : Calls) : Option Place := do
  let owner ← lookup argument.owner.text
  if owner.binder.text != argument.owner.text ||
      Semantics.Finite.width owner.basis != owner.wires.length then none else
  match argument.selection with
  | .whole => some ⟨argument.role,owner,owner.basis,owner.wires,true⟩
  | .index index => do
    let [.bits _] := owner.basis | none
    let axis ← evaluate (argument.selector.length+1) names calls index
    let wire ← owner.wires[axis]?
    return ⟨argument.role,owner,[.bit],[wire],false⟩
  | .slice start stop => do
    let [.bits n] := owner.basis | none
    let i ← evaluate (argument.selector.length+1) names calls start
    let j ← evaluate (argument.selector.length+1) names calls stop
    if i ≤ j && j ≤ n then
      some ⟨argument.role,owner,[.bits (j-i)],(owner.wires.drop i).take (j-i),false⟩
    else none

def CheckedCall.places {tokens} (checked : CheckedCall tokens) (lookup : String → Option Owner)
    (names : Semantics.SourceNatural.Names) (calls : Semantics.SourceNatural.Calls) : Option (List Place) :=
  checked.arguments.mapM (fun written => written.2.place lookup names calls)

/-- Two coherent controls may share coordinates. Any exclusive access must be
disjoint from the other call's axes and cannot exchange authority over the
same whole owner, even when its wire list is empty. -/
def Place.compatible (left right : Place) : Bool :=
  (left.role == .ctrl && right.role == .ctrl) ||
    (!(left.owner.binder == right.owner.binder && (left.whole || right.whole)) &&
      left.axes.all (fun axis => !right.axes.contains axis))

def compatible (left right : List Place) : Bool :=
  left.all (fun first => right.all first.compatible)

private theorem exclusive_pair (first second : Place) (pair : first.compatible second = true)
    (exclusive : first.role = .excl ∨ second.role = .excl) :
    (!(first.owner.binder == second.owner.binder && (first.whole || second.whole))) = true ∧
      first.axes.all (fun axis => !second.axes.contains axis) = true := by
  have different : (Role.excl == Role.ctrl) = false := rfl
  simp only [Place.compatible,Bool.or_eq_true,Bool.and_eq_true] at pair
  rcases pair with both | separated
  · rcases exclusive with role | role <;> simp [role,different] at both
  · exact separated

theorem exclusive_disjoint (left right : List Place) (ok : compatible left right = true)
    (first second : Place) (inLeft : first ∈ left) (inRight : second ∈ right)
    (exclusive : first.role = .excl ∨ second.role = .excl) (axis : Nat)
    (inFirst : axis ∈ first.axes) : axis ∉ second.axes := by
  have pair := List.all_eq_true.mp (List.all_eq_true.mp ok first inLeft) second inRight
  simpa using List.all_eq_true.mp (exclusive_pair first second pair exclusive).2 axis inFirst

theorem exclusive_keeps_whole_owner_distinct (left right : List Place) (ok : compatible left right = true)
    (first second : Place) (inLeft : first ∈ left) (inRight : second ∈ right)
    (exclusive : first.role = .excl ∨ second.role = .excl)
    (whole : first.whole = true ∨ second.whole = true) : first.owner.binder ≠ second.owner.binder := by
  have pair := List.all_eq_true.mp (List.all_eq_true.mp ok first inLeft) second inRight
  have separated := (exclusive_pair first second pair exclusive).1
  intro same
  rcases whole with access | access <;> simp [same,access] at separated

end QleisliKernel.SourceTypes.AccessSyntax
