import QleisliKernel.SourceTypes.SymbolicTypes
import QleisliKernel.SourceTypes.QuantumMoves

/-! Symbolic original runtime types and linear value shapes. Quantum product
bases remain atomic owners; ordinary structural tuples retain their shape.
Opaque Basis parameters are never reflected or decomposed by a selected value.
This is an additional source obligation, not a native acceptance route.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.GenericValues
open Finite Semantics.SymbolicBasis

inductive Atom where
  | owner (basis : Code)
  | ordinary (basis : Code)
  | tuple (arity : Nat)
  deriving BEq, DecidableEq, Repr

abbrev Value := List Atom

structure Cell where
  name : String
  value : Value
  binding : Nat
  deriving BEq, DecidableEq, Repr

abbrev Environment := List Cell

def hasOwner (value : Value) : Bool := value.any fun atom => match atom with | .owner _ => true | _ => false

def codeFields (code : Code) : Nat := code.foldl (fun size atom => size+match atom with
  | .parameter binderKey => binderKey.moduleName.utf8ByteSize+binderKey.declarationName.utf8ByteSize+2
  | .bits width => width.coefficients.length+2
  | .fixed (.enumeration origin names) | .fixed (.record origin names) =>
    origin.moduleName.utf8ByteSize+origin.declarationName.utf8ByteSize+origin.source.utf8ByteSize+
      (names.map String.utf8ByteSize).sum+2
  | _ => 1) 0

def valueFields (value : Value) : Nat := value.foldl (fun size atom => size+match atom with
  | .owner code | .ordinary code => codeFields code+1
  | .tuple _ => 1) 0

private def children : Semantics.SymbolicBasis.Atom → Option Nat
  | .fixed atom => Semantics.FiniteCarrier.children atom
  | _ => some 0

private def spanCode : Nat → Nat → Code → Code → Except String (Code × Code) :=
  Nat.rec (fun _ _ _ => throw "incomplete symbolic basis") (fun _ next pending rest reversed => do
    if pending == 0 then return (reversed.reverse,rest)
    let atom :: tail := rest | throw "missing symbolic basis node"
    let some count := children atom | throw "invalid symbolic basis node"
    next (pending-1+count) tail (atom :: reversed))

def splitCode (code : Code) : Except String (Code × Code) := spanCode (code.length+1) 1 code []

def pairCodes (code : Code) : Except String (Code × Code) := do
  let .fixed .pair :: rest := code | throw "opaque or non-pair quantum basis"
  let (left,rest) ← splitCode rest
  let (right,rest) ← splitCode rest
  if !rest.isEmpty then throw "trailing symbolic pair fields"
  pure (left,right)

private def ordinaryNode : Nat → Code → Except String (Value × Code) :=
  Nat.rec (fun _ => throw "ordinary symbolic tuple nesting") (fun _ next code => do
    let atom :: tail := code | throw "missing ordinary symbolic type"
    match atom with
    | .fixed .pair | .fixed (.tuple _) =>
      let some count := children atom | throw "invalid ordinary tuple type"
      let (values,tail) ← (List.range count).foldlM (fun (values,rest) _ => do
        let (value,tail) ← next rest
        pure (values ++ value,tail)) ([],tail)
      pure (.tuple count :: values,tail)
    | _ =>
      let (basis,tail) ← splitCode code
      pure ([.ordinary basis],tail))

def ordinaryValue (code : Code) : Except String Value := do
  let (value,rest) ← ordinaryNode (code.length+1) code
  if !rest.isEmpty then throw "trailing ordinary symbolic type"
  pure value

private def spanValue : Nat → Nat → Value → Value → Except String (Value × Value) :=
  Nat.rec (fun _ _ _ => throw "incomplete symbolic runtime value") (fun _ next pending rest reversed => do
    if pending == 0 then return (reversed.reverse,rest)
    let atom :: tail := rest | throw "missing symbolic runtime value"
    let count := match atom with | .tuple arity => arity | _ => 0
    next (pending-1+count) tail (atom :: reversed))

def splitValue (value : Value) : Except String (Value × Value) := spanValue (value.length+1) 1 value []

def take (name : String) (environment : Environment) : Except String (Value × Environment) :=
  (environment.foldr (fun cell (rest,result) =>
    (cell :: rest,if cell.name == name then
      .ok (cell.value,if hasOwner cell.value then rest else cell :: rest)
      else result.map fun (value,remaining) => (value,cell :: remaining)))
    ([],throw "undefined or consumed symbolic source value")).2

private def moveNode : Nat → QuantumMoves.Term → Environment → Except String (QuantumMoves.Term × Value × Environment) :=
  Nat.rec (fun _ _ => throw "symbolic source move nesting") (fun _ next term environment => do
    let atom :: rest := term | throw "missing symbolic source move"
    match atom with
    | .name name =>
      let (value,remaining) ← take name environment
      pure (rest,value,remaining)
    | .wildcard => throw "wildcard is not a source value"
    | .tuple count =>
      let (term,values,remaining) ← (List.range count).foldlM (fun (term,values,current) _ => do
        let (term,value,remaining) ← next term current
        pure (term,values ++ value,remaining)) (rest,[],environment)
      pure (term,.tuple count :: values,remaining))

def move (term : QuantumMoves.Term) (environment : Environment) : Except String (Value × Environment) := do
  let (rest,value,remaining) ← moveNode (term.length+1) term environment
  if !rest.isEmpty then throw "trailing symbolic source move"
  pure (value,remaining)

private def bindNode (binding : Nat) : Nat → QuantumMoves.Term → Value → Environment →
    Except String (QuantumMoves.Term × Value × Environment) :=
  Nat.rec (fun _ _ _ => throw "symbolic source binding nesting") (fun _ next term value environment => do
    let atom :: rest := term | throw "missing symbolic source pattern"
    match atom with
    | .name name =>
      let (selected,tail) ← splitValue value
      if environment.any (fun cell => cell.name == name && hasOwner cell.value) then
        throw "shadowing a live symbolic owner"
      pure (rest,tail,⟨name,selected,binding⟩ :: environment.filter (·.name != name))
    | .wildcard =>
      let (selected,tail) ← splitValue value
      if hasOwner selected then throw "implicit symbolic owner discard"
      pure (rest,tail,environment)
    | .tuple count =>
      let .tuple arity :: tail := value | throw "tuple pattern on an opaque owner/value"
      if arity != count then throw "symbolic tuple pattern arity"
      (List.range count).foldlM (fun (term,value,current) _ => next term value current) (rest,tail,environment))

def bind (tokens : List String) (value : Value) (environment : Environment) (binding : Nat := 0) : Except String Environment := do
  let term ← QuantumMoves.parse 65 tokens
  let names := term.filterMap fun atom => match atom with | .name name => some name | _ => none
  if !decide names.Nodup then throw "duplicate symbolic binding"
  let (rest,value,environment) ← bindNode binding (term.length+1) term value environment
  if !rest.isEmpty || !value.isEmpty then throw "incomplete symbolic binding"
  pure environment

def seed (patterns : List (List String)) (values : List Value) : Except String Environment := do
  if patterns.length != values.length then throw "symbolic parameter count"
  (patterns.zip values).foldlM (fun environment (pattern,value) => do
    let term ← QuantumMoves.parse 65 pattern
    let names := term.filterMap fun atom => match atom with | .name name => some name | _ => none
    if names.any (fun name => environment.any (·.name == name)) then throw "duplicate symbolic parameter binding"
    bind pattern value environment) []

private def adapt {α : Type} (value : Except String α) : WorkM α := lift (value.mapError fun _ => .request)

structure TypeRead where
  value : Value
  rows : List (String × String)

def readType {sources : Sources} (state : GenericLexicalNatural.SomeEnvironment sources) :
    Nat → List String → WorkM TypeRead :=
  Nat.rec (fun _ => throw .limit) (fun _ next tokens => do
    let scope := state.prepared.original.header.formals.map (·.name)
    let ordinal := scope.length
    match tokens with
    | "Q" :: _ =>
      let inner ← adapt (QuantumSignatureCore.quantumTokens tokens)
      let query ← SymbolicTypes.read state scope ordinal inner
      pure ⟨[.owner query.result.code],query.result.rows⟩
    | "(" :: rest =>
      guard (rest.getLast? == some ")" && rest.dropLast.getLast? != some ",") .request
      let parts ← adapt (splitMembers rest.dropLast)
      guard (2 ≤ parts.length && parts.length ≤ 64) .limit
      let fields ← parts.mapM next
      pure ⟨.tuple parts.length :: fields.flatMap (·.value),fields.flatMap (·.rows)⟩
    | _ =>
      let query ← SymbolicTypes.read state scope ordinal tokens
      let value ← adapt (ordinaryValue query.result.code)
      pure ⟨value,query.result.rows⟩)

def expect {sources : Sources} (state : GenericLexicalNatural.SomeEnvironment sources)
    (actual expected : Value) : WorkM Unit := do
  guard (actual.length == expected.length) .request
  for (actual,expected) in actual.zip expected do
    match actual,expected with
    | .owner a,.owner b | .ordinary a,.ordinary b =>
      let _ ← SymbolicTypes.equate state a b
      pure ()
    | .tuple a,.tuple b => guard (a == b) .request
    | _,_ => throw .request

def substitute (variables : Nat) (bases : List (Parameter × Code)) (naturals : List Semantics.SourceAffine.Form)
    (value : Value) : WorkM Value := do
  let parts ← value.mapM fun atom => do
    match atom with
    | .owner code => pure [Atom.owner (← SymbolicTypes.substitute variables bases naturals code).code]
    | .ordinary code =>
      adapt (ordinaryValue (← SymbolicTypes.substitute variables bases naturals code).code)
    | .tuple arity => pure [.tuple arity]
  pure parts.flatten

end QleisliKernel.SourceTypes.GenericValues
