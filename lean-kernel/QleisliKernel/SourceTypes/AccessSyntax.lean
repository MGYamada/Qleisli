import QleisliKernel.SourceTypes.CallSyntax
import QleisliKernel.SourceTypes.CallName
import QleisliKernel.SourceTypes.NaturalSyntax
import QleisliKernel.SourceTypes.StatementSyntax
import QleisliKernel.SourceTypes.QuantumMoves
import QleisliKernel.SourceTypes.ParameterPatterns
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

abbrev MarkedSlot := Nat × Role

inductive Selection where
  | whole
  | index (axis : Natural)
  | slice (start stop : Natural)

private def readRole (token : LocatedToken) : Except String Role :=
  match token.text with
  | "ctrl" => .ok .ctrl
  | "excl" => .ok .excl
  | _ => .error "original quantum access requires ctrl or excl"

private def startsDeclaredAccess : List LocatedToken → Bool
  | marker :: quantum :: _ => (readRole marker).isOk && quantum.text == "Q"
  | _ => false

def hasDeclaredTypes (types : List (List String)) : Bool :=
  types.any fun
    | mode :: "Q" :: _ => mode == "ctrl" || mode == "excl"
    | _ => false

private def ownerTypeShape : List LocatedToken → Bool
  | quantum :: opening :: rest =>
    quantum.text == "Q" && opening.text == "<" && rest.getLast?.map (·.text) == some ">" &&
      !rest.dropLast.isEmpty &&
      match splitMembersWith (·.text) rest.dropLast with
      | .ok [basis] => basis == rest.dropLast
      | _ => false
  | _ => false

/-- A written access parameter retains the exact owner binder, marker and
complete type tokens. The underlying basis is interpreted by later typing. -/
structure DeclaredAccess (clause : ParameterPatterns.Clause) where
  owner : LocatedToken
  marker : LocatedToken
  typeTokens : List LocatedToken
  role : Role
  ownerPattern : clause.pattern = [owner]
  ownerName : identifier owner.text = true
  originalType : clause.typeTokens = marker :: typeTokens
  ownerType : ownerTypeShape typeTokens = true
  roleRead : readRole marker = .ok role

inductive DeclaredParameter (clause : ParameterPatterns.Clause) where
  | ordinary (unmarked : startsDeclaredAccess clause.typeTokens = false)
  | access (written : DeclaredAccess clause)

private def readDeclaredParameter (ordinaryOnly : Bool) (clause : ParameterPatterns.Clause) :
    Except String (DeclaredParameter clause) := do
  if marked : startsDeclaredAccess clause.typeTokens = true then
    if ordinaryOnly then throw "quantum access parameters require a runtime function"
    match pattern : clause.pattern, written : clause.typeTokens with
    | [owner], marker :: ty =>
      if name : identifier owner.text = true then
        if shape : ownerTypeShape ty = true then
          match role : readRole marker with
          | .ok value => return .access ⟨owner,marker,ty,value,pattern,name,written,shape,role⟩
          | .error error => throw error
        else throw "quantum access parameter requires one complete Q type"
      else throw "quantum access parameter requires one named owner"
    | _,_ => throw "quantum access parameter requires one named owner"
  else return .ordinary (Bool.eq_false_iff.mpr marked)

structure DeclaredParameters {sources owner name}
    (original : OrdinarySignature.Original sources owner name) where
  clauses : List ParameterPatterns.Clause
  located : ParameterPatterns.readClauses original = .ok clauses
  parameters : List (Sigma DeclaredParameter)
  ordered : parameters.map Sigma.fst = clauses

def DeclaredParameters.markedSlots {sources owner name} {original : OrdinarySignature.Original sources owner name}
    (declared : DeclaredParameters original) : List MarkedSlot :=
  declared.parameters.zipIdx.filterMap fun (parameter,slot) =>
    match parameter.2 with
    | .ordinary _ => none
    | .access written => some (slot,written.role)

/-- Inspect declared access roles as original header syntax. The existing
signature and execution readers still consume the complete marked type clause. -/
def readDeclaredParameters {sources owner name} (original : OrdinarySignature.Original sources owner name) :
    Except String (DeclaredParameters original) := do
  match located : ParameterPatterns.readClauses original with
  | .error error => throw error
  | .ok clauses =>
    let parameters ← clauses.mapM fun clause => do
      return ⟨clause,← readDeclaredParameter original.parsedHeader.ordinaryOnly clause⟩
    if ordered : parameters.map Sigma.fst = clauses then
      return ⟨clauses,located,parameters,ordered⟩
    else throw "original access parameter order changed"

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

private def readAccessHead (tokens : List LocatedToken) :
    Except String (Σ parsed : CallSyntax.Checked tokens, Callee parsed.call.callee) := do
  let parsed ← CallSyntax.read tokens
  let callee ← (match CallSyntax.readStatic parsed.call.callee with
    | .ok applied => (CallName.readName applied.call.callee).map (Callee.specialized applied)
    | .error _ => (CallName.readName parsed.call.callee).map Callee.named)
  let arguments := parsed.call.arguments
  if arguments.isEmpty || arguments.length > 64 then throw "original access call arity"
  if (arguments.getLast?.bind (·.followingComma)).isSome then
    throw "trailing comma in original access call"
  return ⟨parsed,callee⟩

structure CheckedCall (tokens : List LocatedToken) where
  parsed : CallSyntax.Checked tokens
  callee : Callee parsed.call.callee
  arguments : List (Sigma Argument)
  original : arguments.map Sigma.fst = parsed.call.arguments.map (·.tokens)

def readCall (tokens : List LocatedToken) : Except String (CheckedCall tokens) := do
  let ⟨parsed,callee⟩ ← readAccessHead tokens
  let arguments := parsed.call.arguments.map (·.tokens)
  let checked ← arguments.mapM fun tokens => do
    return ⟨tokens,← readArgument tokens⟩
  if original : checked.map Sigma.fst = arguments then return ⟨parsed,callee,checked,original⟩
  else throw "original access argument order changed"

inductive UnitSyntax (tokens : List LocatedToken) where
  | literal (written : CallSyntax.CheckedGroup tokens) (empty : written.group.arguments = [])
  | bound (token : LocatedToken) (original : tokens = [token])
      (name : String) (parsed : QuantumMoves.parse 65 [token.text] = .ok [.name name])

def readUnitSyntax (tokens : List LocatedToken) : Except String (UnitSyntax tokens) := do
  match tokens with
  | [token] =>
    match parsed : QuantumMoves.parse 65 [token.text] with
    | .ok [.name name] => return .bound token rfl name parsed
    | _ => throw "ordinary Unit argument requires a lexical name or ()"
  | [opening,closing] =>
    let written ← CallSyntax.readGroup [opening,closing]
    if empty : written.group.arguments = [] then return .literal written empty
    else throw "ordinary Unit argument requires a lexical name or ()"
  | _ => throw "ordinary Unit argument requires a lexical name or ()"

/-- A marker is contextual and must be followed by a lexical owner name. -/
def startsAccess : List LocatedToken → Bool
  | marker :: owner :: _ => (marker.text == "ctrl" || marker.text == "excl") && identifier owner.text
  | _ => false

inductive ArgumentSlot (tokens : List LocatedToken) where
  /-- An ordinary slot retains its tokens for the expression reader. -/
  | ordinary (unmarked : startsAccess tokens = false)
  | access (written : Argument tokens)

def ArgumentSlot.isAccess {tokens} : ArgumentSlot tokens → Bool
  | .ordinary _ => false
  | .access _ => true

def readArgumentSlot (tokens : List LocatedToken) : Except String (ArgumentSlot tokens) := do
  if marked : startsAccess tokens = true then
    return .access (← readArgument tokens)
  else
    return .ordinary (Bool.eq_false_iff.mpr marked)

structure CheckedAccessCall (tokens : List LocatedToken) where
  parsed : CallSyntax.Checked tokens
  callee : Callee parsed.call.callee
  slots : List (Sigma ArgumentSlot)
  original : slots.map Sigma.fst = parsed.call.arguments.map (·.tokens)
  hasAccess : slots.any (fun slot => slot.2.isAccess) = true

/-- Recognize original access slots anywhere in a call. Ordinary expression
typing and replay remain the responsibility of the caller. -/
def readAccessCall (tokens : List LocatedToken) : Except String (CheckedAccessCall tokens) := do
  let ⟨parsed,callee⟩ ← readAccessHead tokens
  let arguments := parsed.call.arguments.map (·.tokens)
  let slots ← arguments.mapM fun tokens => do
    return ⟨tokens,← readArgumentSlot tokens⟩
  if original : slots.map Sigma.fst = arguments then
    if hasAccess : slots.any (fun slot => slot.2.isAccess) = true then
      return ⟨parsed,callee,slots,original,hasAccess⟩
    else throw "source call has no original access argument"
  else throw "original access argument order changed"

theorem CheckedAccessCall.slotAt {tokens} (checked : CheckedAccessCall tokens) (ordinal : Nat)
    {slot : Sigma ArgumentSlot} (selected : checked.slots[ordinal]? = some slot) :
    checked.parsed.call.arguments[ordinal]?.map (·.tokens) = some slot.1 := by
  have original := congrArg (fun arguments : List (List LocatedToken) => arguments[ordinal]?) checked.original
  simpa only [List.getElem?_map,selected,Option.map_some] using original.symm

def CheckedAccessCall.arguments {tokens} (call : CheckedAccessCall tokens) : List (Sigma Argument) :=
  call.slots.filterMap fun
    | ⟨tokens,.access argument⟩ => some ⟨tokens,argument⟩
    | ⟨_,.ordinary _⟩ => none

def CheckedAccessCall.hasOrdinary {tokens} (call : CheckedAccessCall tokens) : Bool :=
  !call.slots.all (fun slot => slot.2.isAccess)

def CheckedAccessCall.markedSlots {tokens} (call : CheckedAccessCall tokens) : List MarkedSlot :=
  call.slots.zipIdx.filterMap fun (argument,slot) =>
    match argument.2 with
    | .ordinary _ => none
    | .access written => some (slot,written.role)

def CheckedAccessCall.exclusive {tokens} (call : CheckedAccessCall tokens) : Bool :=
  call.arguments.all (fun argument => argument.2.role == .excl)

def CheckedAccessCall.wholeExclusive {tokens} (call : CheckedAccessCall tokens) : Bool :=
  !call.hasOrdinary && call.arguments.all (fun argument => argument.2.role == .excl &&
    match argument.2.selection with | .whole => true | _ => false)

def CheckedAccessCall.ownerNames {tokens} (call : CheckedAccessCall tokens) : List String :=
  call.arguments.map (fun argument => argument.2.owner.text)

private def fillSlots {α : Type} (readOrdinary : List LocatedToken → Except String α)
    (slots : List (Sigma ArgumentSlot)) (marked : List α) : Except String (List α) := do
  let missing := "access values do not fill the original marked argument slots"
  let (remaining,reversed) ← slots.foldlM (fun (remaining,reversed) ⟨tokens,slot⟩ => do
    match slot with
    | .ordinary _ => return (remaining,(← readOrdinary tokens) :: reversed)
    | .access _ =>
      let value :: tail := remaining | .error missing
      return (tail,value :: reversed)) (marked,[])
  if remaining.isEmpty then return reversed.reverse else throw missing

/-- Reinsert the actual marked values at their original argument positions.
Ordinary values come from the corresponding unmodified located tokens. -/
def CheckedAccessCall.fillArguments {tokens} {α : Type} (call : CheckedAccessCall tokens)
    (marked : List α) (readOrdinary : List LocatedToken → Except String α) : Except String (List α) :=
  fillSlots readOrdinary call.slots marked

def CheckedCall.exclusive {tokens : List LocatedToken} (call : CheckedCall tokens) : Bool :=
  call.arguments.all fun argument => argument.2.role == .excl

/-- A whole exclusive argument covers the complete original owner. -/
def CheckedCall.wholeExclusive {tokens : List LocatedToken} (call : CheckedCall tokens) : Bool :=
  call.arguments.all fun arg => arg.2.role == .excl &&
    match arg.2.selection with | .whole => true | _ => false

def CheckedCall.ownerNames {tokens : List LocatedToken} (call : CheckedCall tokens) : List String :=
  call.arguments.map fun arg => arg.2.owner.text

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
  range : Option (Nat × Nat)
  deriving BEq, Repr

def Place.whole (place : Place) : Bool := place.range.isNone

open Semantics.SourceNatural in
/-- Instantiate a written selector in an explicit static environment and keep
the caller's ordered wire labels, including owners with no physical axes. -/
def Argument.place {tokens} (argument : Argument tokens) (lookup : String → Option Owner)
    (names : Names) (calls : Calls) : Option Place := do
  let owner ← lookup argument.owner.text
  if owner.binder.text != argument.owner.text ||
      Semantics.Finite.width owner.basis != owner.wires.length then none else
  match argument.selection with
  | .whole => some ⟨argument.role,owner,owner.basis,owner.wires,none⟩
  | .index index => do
    let [.bits _] := owner.basis | none
    let axis ← evaluate (argument.selector.length+1) names calls index
    let wire ← owner.wires[axis]?
    return ⟨argument.role,owner,[.bit],[wire],some (axis,axis+1)⟩
  | .slice start stop => do
    let [.bits n] := owner.basis | none
    let i ← evaluate (argument.selector.length+1) names calls start
    let j ← evaluate (argument.selector.length+1) names calls stop
    if i ≤ j && j ≤ n then
      some ⟨argument.role,owner,[.bits (j-i)],(owner.wires.drop i).take (j-i),some (i,j)⟩
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
