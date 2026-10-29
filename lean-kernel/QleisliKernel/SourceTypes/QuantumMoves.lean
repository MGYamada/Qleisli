import QleisliKernel.Semantics.SourceOwners
import QleisliKernel.SourceTypes

/-! Structural source moves before a focused quantum operation. Quantum
product owners remain atomic; ordinary tuples only collect separate values.
Calls, allocation and general expressions require their separate checked rules.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.QuantumMoves
open Semantics.SourceOwners

inductive TermAtom where
  | name (value : String)
  | tuple (arity : Nat)
  | wildcard
  deriving BEq, DecidableEq, Repr

abbrev Term := List TermAtom

def parse : Nat → List String → Except String Term :=
  Nat.rec (fun _ => throw "structural source expression depth") (fun _ next tokens => do
    match tokens with
    | [name] =>
      if name == "_" then return [.wildcard]
      if identifier name then return [.name name]
      throw "expected an original binding name"
    | "(" :: rest =>
      if rest.getLast? != some ")" then throw "unclosed structural source expression"
      let inner := rest.dropLast
      let parts ← splitMembers inner
      if parts.length > 128 then throw "structural source tuple capacity"
      if parts.length == 1 && inner.getLast? != some "," then
        let [part] := parts | throw "missing grouped expression"
        next part
      else
        let children ← parts.mapM next
        return .tuple children.length :: children.flatten
    | _ => throw "structural owner expression requires its original checked rule")

private def takeScan (name : String) (environment : Environment) :
    Environment × Except String (Value × Environment) :=
  environment.foldr (fun cell (rest,result) =>
    (cell :: rest,if cell.name = name then .ok (cell.value,rest)
      else result.map fun (value,remaining) => (value,cell :: remaining)))
    ([],throw "undefined or consumed quantum binding")

def take (name : String) (environment : Environment) : Except String (Value × Environment) :=
  (takeScan name environment).2

private theorem takeScan_environment (name : String) (environment : Environment) :
    (takeScan name environment).1 = environment := by
  induction environment with
  | nil => rfl
  | cons cell rest ih =>
    change cell :: (takeScan name rest).1 = cell :: rest
    rw [ih]

theorem take_cons (name : String) (cell : Cell) (rest : Environment) :
    take name (cell :: rest) =
      if cell.name = name then .ok (cell.value,rest)
      else (take name rest).map fun (value,remaining) => (value,cell :: remaining) := by
  change (if cell.name = name then .ok (cell.value,(takeScan name rest).1)
    else (takeScan name rest).2.map fun (value,remaining) => (value,cell :: remaining)) = _
  rw [takeScan_environment]
  rfl

private def spanValue : Nat → Nat → Value → Value → Except String (Value × Value) :=
  Nat.rec (fun _ _ _ => throw "incomplete structural value") (fun _ next pending rest reversed => do
    if pending == 0 then return (reversed.reverse,rest)
    let atom :: tail := rest | throw "missing structural value atom"
    let children := match atom with | .owner _ => 0 | .tuple arity => arity
    if children > 128 then throw "structural value capacity"
    next (pending-1+children) tail (atom :: reversed))

def splitValue (value : Value) : Except String (Value × Value) :=
  spanValue (value.length+1) 1 value []

private def evalNode : Nat → Term → Environment → Except String (Value × Term × Environment) :=
  Nat.rec (fun _ _ => throw "structural source evaluation depth") (fun _ next term environment => do
    let atom :: rest := term | throw "missing structural source expression"
    match atom with
    | .wildcard => throw "wildcard is not a value"
    | .name name =>
      let (value,remaining) ← take name environment
      return (value,rest,remaining)
    | .tuple arity =>
      if arity > 128 then throw "structural source tuple capacity"
      let (values,remaining,current) ← (List.range arity).foldlM (fun (values,remaining,current) _ => do
        let (value,tail,after) ← next remaining current
        return (value :: values,tail,after)) ([],rest,environment)
      return (.tuple arity :: values.reverse.flatten,remaining,current))

def eval (tokens : List String) (environment : Environment) : Except String (Value × Environment) := do
  let term ← parse 65 tokens
  let (value,rest,remaining) ← evalNode 65 term environment
  if !rest.isEmpty || value.length > 128 then throw "unconsumed or oversized source value"
  return (value,remaining)

private def bindNode : Nat → Term → Value → Environment → Except String (Term × Value × Environment) :=
  Nat.rec (fun _ _ _ => throw "structural source pattern depth") (fun _ next term value environment => do
    let atom :: rest := term | throw "missing structural source pattern"
    match atom with
    | .name name =>
      let (selected,tail) ← splitValue value
      if environment.any (·.name == name) then throw "shadowing a live owner binding"
      return (rest,tail,⟨name,selected⟩ :: environment)
    | .wildcard =>
      let (selected,tail) ← splitValue value
      if !(valueOwners selected).isEmpty then throw "implicit quantum discard in wildcard"
      return (rest,tail,environment)
    | .tuple arity =>
      let .tuple count :: tail := value | throw "a quantum product owner cannot be destructured"
      if arity != count || arity > 128 then throw "structural pattern shape mismatch"
      (List.range arity).foldlM (fun (remaining,values,current) _ => next remaining values current)
        (rest,tail,environment))

def bind (tokens : List String) (value : Value) (environment : Environment) : Except String Environment := do
  let term ← parse 65 tokens
  let (patterns,values,result) ← bindNode 65 term value environment
  if !patterns.isEmpty || !values.isEmpty || result.length > 128 then throw "incomplete source pattern binding"
  return result

/-- Only completely checked structural lets are traversed. An unfinished
`let pattern =` may surround the focused operation; no unknown prefix is skipped. -/
def replay : Nat → Environment → List String → Except String Environment :=
  Nat.rec (fun _ _ => throw "source prefix capacity") (fun _ next environment tokens => do
    match tokens with
    | [] => return environment
    | "let" :: rest =>
      let pattern := rest.takeWhile (· != "=")
      let "=" :: tail := rest.drop pattern.length | throw "missing source let assignment"
      let _ ← parse 65 pattern
      if tail.isEmpty then return environment
      let expression := tail.takeWhile (· != ";")
      let ";" :: remaining := tail.drop expression.length | throw "incomplete structural source let"
      let (value,current) ← eval expression environment
      let after ← bind pattern value current
      if (owners environment).Perm (owners after) then next after remaining
      else throw "source let changes the live owner multiset"
    | _ => throw "source prefix requires its original checked expression rule")

theorem take_move (name : String) (environment : Environment) (value : Value) (remaining : Environment)
    (ok : take name environment = .ok (value,remaining)) : Move environment name value remaining := by
  induction environment generalizing remaining with
  | nil => simp [take,takeScan] at ok
  | cons cell rest ih =>
    rcases cell with ⟨cellName,cellValue⟩
    simp only [take_cons] at ok
    split at ok
    next same =>
      have pair := Except.ok.inj ok
      have values : cellValue = value := congrArg Prod.fst pair
      have tails : rest = remaining := congrArg Prod.snd pair
      subst value
      subst remaining
      simpa only [same] using (Move.head cellName cellValue rest)
    next different =>
      cases moved : take name rest with
      | error error => simp [moved,Except.map] at ok
      | ok result =>
        rcases result with ⟨selected,after⟩
        simp only [moved,Except.map,Except.ok.injEq,Prod.mk.injEq] at ok
        rw [ok.1] at moved
        rw [← ok.2]
        exact .tail ⟨cellName,cellValue⟩ rest name value after different (ih after moved)

end QleisliKernel.SourceTypes.QuantumMoves
