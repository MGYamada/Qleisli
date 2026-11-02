import QleisliKernel.SourceTypes.QuantumMoves
import QleisliKernel.SourceTypes.RuntimeSignature
import QleisliKernel.Raw.OwnerFlow
import QleisliKernel.Semantics.SourceOrdinary

/-! Typed symbolic runtime values for complete original-body traversal.
Ordinary values copy; any value containing a logical quantum owner moves.
Measurement symbols preserve original callee origins and the full call path.
These values are source-checking metadata, not simulator states or receipts.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceRuntimeValues
open QleisliKernel QleisliKernel.Semantics.SourceOwners
open QleisliKernel.Semantics.FiniteCarrier

abbrev Site := Semantics.SourceOrdinary.Site
abbrev Expression := Semantics.SourceOrdinary.Expression

namespace Expression
@[match_pattern] abbrev input := Semantics.SourceOrdinary.Expression.input
@[match_pattern] abbrev basisInput := Semantics.SourceOrdinary.Expression.basisInput
@[match_pattern] abbrev unit := Semantics.SourceOrdinary.Expression.unit
@[match_pattern] abbrev bit := Semantics.SourceOrdinary.Expression.bit
@[match_pattern] abbrev ordinal := Semantics.SourceOrdinary.Expression.ordinal
@[match_pattern] abbrev measured := Semantics.SourceOrdinary.Expression.measured
@[match_pattern] abbrev project := Semantics.SourceOrdinary.Expression.project
@[match_pattern] abbrev combine := Semantics.SourceOrdinary.Expression.combine
@[match_pattern] abbrev field := Semantics.SourceOrdinary.Expression.field
@[match_pattern] abbrev not := Semantics.SourceOrdinary.Expression.not
@[match_pattern] abbrev xor := Semantics.SourceOrdinary.Expression.xor
@[match_pattern] abbrev and := Semantics.SourceOrdinary.Expression.and
@[match_pattern] abbrev choose := Semantics.SourceOrdinary.Expression.choose
end Expression

abbrev Atom := Semantics.SourceOrdinary.Atom
abbrev Value := Semantics.SourceOrdinary.Value

namespace Atom
@[match_pattern] abbrev owner := Semantics.SourceOrdinary.Atom.owner
@[match_pattern] abbrev ordinary := Semantics.SourceOrdinary.Atom.ordinary
@[match_pattern] abbrev tuple := Semantics.SourceOrdinary.Atom.tuple
end Atom

inductive BindingOrigin where
  | parameter (ordinal : Nat)
  | letBinding (offset : Nat)
  | basis (offset : Nat)
  deriving BEq, DecidableEq, Repr

structure Cell where
  name : String
  value : Value
  origin : BindingOrigin
  deriving BEq, DecidableEq, Repr

abbrev Environment := List Cell

def valueOwners (value : Value) : List Owner :=
  value.filterMap fun atom => match atom with | .owner owner => some owner | _ => none

def owners (environment : Environment) : List Owner := environment.flatMap (valueOwners ∘ Cell.value)

def ordinary (value : Value) : List (Basis × Expression) :=
  value.filterMap fun atom => match atom with | .ordinary basis term => some (basis,term) | _ => none

def typeOf (value : Value) : Semantics.RuntimeType.Tree := value.flatMap fun atom => match atom with
  | .owner owner => Semantics.RuntimeType.owner owner.basis
  | .ordinary basis _ => Semantics.RuntimeType.ordinary basis
  | .tuple arity => [.finite (if arity == 2 then .pair else .tuple arity)]

private def spanValue : Nat → Nat → Value → Value → Except String (Value × Value) :=
  Nat.rec (fun _ _ _ => throw "incomplete runtime source value") (fun _ recurse pending rest reversed => do
    if pending == 0 then return (reversed.reverse,rest)
    let atom :: tail := rest | throw "missing runtime source value"
    let children := match atom with | .tuple arity => arity | _ => 0
    if children > 128 then throw "runtime source tuple capacity"
    recurse (pending-1+children) tail (atom :: reversed))

def splitValue (value : Value) : Except String (Value × Value) :=
  spanValue (value.length+1) 1 value []

/-- Copying a wholly ordinary tuple retains its binding. A mixed tuple moves
as a whole and cannot be used to read or duplicate its quantum-containing part. -/
def take (name : String) (environment : Environment) : Except String (Value × Environment) :=
  (environment.foldr (fun cell (rest,result) =>
    (cell :: rest,if cell.name == name then
      .ok (cell.value,if (valueOwners cell.value).isEmpty then cell :: rest else rest)
      else result.map fun (value,remaining) => (value,cell :: remaining)))
    ([],throw "undefined or consumed runtime source binding")).2

private def finiteSpan : Nat → Nat → Semantics.RuntimeType.Tree → Basis →
    Except String (Basis × Semantics.RuntimeType.Tree) :=
  Nat.rec (fun _ _ _ => throw "incomplete runtime finite tree")
    (fun _ recurse pending rest reversed => do
      if pending == 0 then return (reversed.reverse,rest)
      let .finite atom :: tail := rest | throw "quantum marker inside a finite source basis"
      let children := (Semantics.FiniteCarrier.children atom).getD 0
      recurse (pending-1+children) tail (atom :: reversed))

def pairBases (basis : Basis) : Except String (Basis × Basis) := do
  let .pair :: fields := basis | throw "source basis is not an exact pair"
  let tree := fields.map Semantics.RuntimeType.Atom.finite
  let (first,rest) ← finiteSpan (tree.length+1) 1 tree []
  let (second,rest) ← finiteSpan (rest.length+1) 1 rest []
  if !rest.isEmpty then throw "source pair basis has trailing fields"
  return (first,second)

private def seedNode : Nat → Semantics.RuntimeType.Tree → Nat → Nat →
    Except String (Value × Semantics.RuntimeType.Tree × Nat × Nat) :=
  Nat.rec (fun _ _ _ => throw "runtime source parameter nesting")
    (fun _ recurse tree nextOwner nextOrdinary => do
      let atom :: rest := tree | throw "empty runtime source parameter"
      match atom with
      | .quantum =>
        let (basis,tail) ← finiteSpan (rest.length+1) 1 rest []
        return ([.owner ⟨nextOwner,basis⟩],tail,nextOwner+1,nextOrdinary)
      | .finite (.pair) | .finite (.tuple _) =>
        let .finite finite := atom | throw "runtime source tuple marker"
        let some count := Semantics.FiniteCarrier.children finite | throw "runtime source tuple arity"
        let (children,tail,owner,ordinary) ← (List.range count).foldlM
          (fun (values,tail,owner,ordinary) _ => do
            let (value,tail,owner,ordinary) ← recurse tail owner ordinary
            return (values ++ value,tail,owner,ordinary)) ([],rest,nextOwner,nextOrdinary)
        return (.tuple count :: children,tail,owner,ordinary)
      | .finite _ =>
        let (basis,tail) ← finiteSpan (tree.length+1) 1 tree []
        return ([.ordinary basis (.input nextOrdinary)],tail,nextOwner,nextOrdinary+1))

def seedValues {sources : Sources} (parameters : List (RuntimeSignature.Part sources)) :
    Except String (List Value × Nat × Nat) := do
  parameters.foldlM (fun (values,owner,ordinary) parameter => do
    let (value,rest,owner,ordinary) ← seedNode 65 parameter.tree owner ordinary
    if !rest.isEmpty then throw "runtime source parameter has trailing type nodes"
    return (values ++ [value],owner,ordinary)) ([],0,0)

private def bindNode (origin : BindingOrigin) : Nat → QuantumMoves.Term → Value → Environment →
    Except String (QuantumMoves.Term × Value × Environment) :=
  Nat.rec (fun _ _ _ => throw "runtime source pattern nesting")
    (fun _ recurse term value environment => do
      let atom :: rest := term | throw "missing runtime source pattern"
      match atom with
      | .name name =>
        let (selected,tail) ← splitValue value
        if environment.any (fun cell => cell.name == name && !(valueOwners cell.value).isEmpty) then
          throw "shadowing a live runtime quantum binding"
        return (rest,tail,⟨name,selected,origin⟩ :: environment.filter (·.name != name))
      | .wildcard =>
        let (selected,tail) ← splitValue value
        if !(valueOwners selected).isEmpty then throw "implicit runtime quantum discard"
        return (rest,tail,environment)
      | .tuple count =>
        let .tuple arity :: tail := value | throw "runtime tuple pattern on an atomic owner/value"
        if arity != count then throw "runtime source pattern tuple shape"
        (List.range count).foldlM (fun (term,value,current) _ => recurse term value current)
          (rest,tail,environment))

def bind (pattern : List String) (value : Value) (environment : Environment)
    (origin : BindingOrigin := .letBinding 0) : Except String Environment := do
  let term ← QuantumMoves.parse 65 pattern
  let names := term.filterMap fun atom => match atom with | .name name => some name | _ => none
  if !decide names.Nodup then throw "duplicate binding in one runtime pattern"
  let (term,value,result) ← bindNode origin 65 term value environment
  if !term.isEmpty || !value.isEmpty || result.length > 128 then throw "incomplete runtime source binding"
  return result

def seed (patterns : List (List String)) (values : List Value) : Except String Environment := do
  if patterns.length != values.length then throw "runtime source parameter count"
  ((patterns.zip values).zipIdx).foldlM (fun environment ((pattern,value),index) => do
    let term ← QuantumMoves.parse 65 pattern
    let names := term.filterMap fun atom => match atom with | .name name => some name | _ => none
    if names.any (fun name => environment.any (·.name == name)) then throw "duplicate runtime parameter binding"
    bind pattern value environment (.parameter index)) []

def mappedOwner (actuals : List Owner) (owner : Owner) : Except String Owner := do
  let some actual := actuals[owner.ordinal]? | throw "runtime call owner ordinal"
  if actual.basis != owner.basis then throw "runtime call owner nominal type"
  return actual

private def expressionTransport (site : Site) (actuals : List Owner) (ordinary : List (Basis × Expression)) :
    Expression → Except String Expression
  | .input ordinal => do
    let some (_,actual) := ordinary[ordinal]? | throw "runtime call ordinary ordinal"
    return actual
  | .basisInput ordinal => pure (.basisInput ordinal)
  | .unit => pure .unit
  | .bit value => pure (.bit value)
  | .ordinal value => pure (.ordinal value)
  | .measured origin calls owner => do return .measured origin (site :: calls) (← mappedOwner actuals owner)
  | .project value ordinal => do return .project (← expressionTransport site actuals ordinary value) ordinal
  | .combine stride first second => do
    return .combine stride (← expressionTransport site actuals ordinary first)
      (← expressionTransport site actuals ordinary second)
  | .field stride dimension receiver => do
    return .field stride dimension (← expressionTransport site actuals ordinary receiver)
  | .not value => do return .not (← expressionTransport site actuals ordinary value)
  | .xor first second => do
    let first ← expressionTransport site actuals ordinary first
    let second ← expressionTransport site actuals ordinary second
    return .xor first second
  | .and first second => do
    let first ← expressionTransport site actuals ordinary first
    let second ← expressionTransport site actuals ordinary second
    return .and first second
  | .choose condition thenValue elseValue => do
    return .choose (← expressionTransport site actuals ordinary condition)
      (← expressionTransport site actuals ordinary thenValue)
      (← expressionTransport site actuals ordinary elseValue)

/-- Size is derived from actual expression structure; the 65 source nesting
bound cannot accidentally cap long flat helper/call chains during transport. -/
def expressionSize : Expression → Nat
  | .project value _ | .field _ _ value | .not value => 1+expressionSize value
  | .xor first second | .and first second | .combine _ first second => 1+expressionSize first+expressionSize second
  | .choose condition thenValue elseValue =>
    1+expressionSize condition+expressionSize thenValue+expressionSize elseValue
  | _ => 1

def siteFields (site : Site) : Nat :=
  site.moduleName.utf8ByteSize+site.functionName.utf8ByteSize+2

def expressionFields : Expression → Nat
  | .measured origin calls owner =>
    1+siteFields origin+(calls.map siteFields).sum+Raw.OwnerFlow.fields [owner]
  | .project value _ | .field _ _ value | .not value => 1+expressionFields value
  | .xor first second | .and first second | .combine _ first second => 1+expressionFields first+expressionFields second
  | .choose condition thenValue elseValue =>
    1+expressionFields condition+expressionFields thenValue+expressionFields elseValue
  | _ => 1

def valueFields (value : Value) : Nat := value.foldl (fun count atom => count+match atom with
  | .owner owner => Raw.OwnerFlow.fields [owner]
  | .ordinary basis expression => Raw.OwnerFlow.fields [⟨0,basis⟩]+expressionFields expression
  | .tuple _ => 1) 0

def transport (site : Site) (actuals : List Owner) (inputs : List (Basis × Expression))
    (value : Value) : Except String Value :=
  value.mapM fun atom => do
    match atom with
    | .owner owner => return .owner (← mappedOwner actuals owner)
    | .ordinary basis expression =>
      return .ordinary basis (← expressionTransport site actuals inputs expression)
    | .tuple arity => return .tuple arity

end QleisliKernel.SourceTypes.SourceRuntimeValues
