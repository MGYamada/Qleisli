import QleisliKernel.SourceTypes.SourceRuntimeValues
import QleisliKernel.SourceTypes.StaticApplication
import QleisliKernel.SourceTypes.PhaseApplication
import QleisliKernel.SourceTypes.NaturalRows

/-! Existing ordinary prepend and quantum register repartition applications.
Static arguments use the same original Nat syntax, symbolic validation and
closed lexical reader. Exact native wire order and coefficient +1 remain
separate from these source port/owner checks.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceRegisterApplication
open QleisliKernel QleisliKernel.SourceTypes SourceRuntimeValues Finite

def selected : CallName.Primitive → Bool
  | .prependBit | .takeBit | .putBit => true
  | _ => false

structure Natural (sources : Sources) (caller : String) (naturals : PhaseApplication.Naturals sources)
    (scope : List String) where
  argument : CallSyntax.Argument
  written : StaticBindings.Natural argument.tokens
  validated : ∃ before after,
    (PhaseApplication.validateNatural sources caller naturals scope written.expression).run before = (.ok (),after)
  closed : LexicalNatural.Checked sources caller naturals.helpers.val naturals.environment scope written.expression
  rows : List (String × String)
  originalRows : ∃ before after,
    (NaturalRows.bindings sources caller naturals.helpers.val closed.bindings.val).run before = (.ok rows,after)

def Natural.value {sources caller naturals scope} (natural : @Natural sources caller naturals scope) : Nat :=
  natural.closed.result.value

private def readNatural (sources : Sources) (caller : String) (naturals : PhaseApplication.Naturals sources)
    (scope : List String) (argument : CallSyntax.Argument) : WorkM (Natural sources caller naturals scope) := do
  let written ← lift ((StaticBindings.natural argument.tokens).mapError fun _ => .request)
  let validated ← NaturalAffine.witness (PhaseApplication.validateNatural sources caller naturals scope written.expression)
  let closed ← LexicalNatural.read sources caller naturals.helpers.val naturals.environment scope written.expression
  let rows ← NaturalAffine.witness (NaturalRows.bindings sources caller naturals.helpers.val closed.bindings.val)
  have unit : validated.val = () := by cases validated.val; rfl
  return ⟨argument,written,by with_reducible simpa only [unit] using validated.property,
    closed,rows.val,by with_reducible exact rows.property⟩

def validateIndex {sources caller naturals scope} (kind : CallName.Primitive)
    (arguments : List (@Natural sources caller naturals scope)) : WorkM Unit := do
  if kind == .takeBit || kind == .putBit then
    let [width,index] := arguments | throw .request
    match naturals.generic with
    | none => pure ()
    | some state =>
      let width ← GenericLexicalNatural.read state.prepared state.environment scope width.written.expression
      let index ← GenericLexicalNatural.read state.prepared state.environment scope index.written.expression
      let _ ← NaturalPredicates.implies state.environment.context index.normalized.form .lt width.normalized.form
      pure ()

def valid (kind : CallName.Primitive) (values : List Nat) : Bool :=
  match kind,values with
  | .prependBit,[width] => width < 12
  | .takeBit,[width,index] | .putBit,[width,index] => width ≤ 12 && index < width
  | _,_ => false

structure Checked (sources : Sources) (caller : String) (naturals : PhaseApplication.Naturals sources)
    (scope : List String) {tokens : List LocatedToken} (written : StaticApplication.Syntax tokens)
    (kind : CallName.Primitive) where
  arguments : List (Natural sources caller naturals scope)
  original : arguments.map (·.argument) = written.arguments
  bounded : valid kind (arguments.map (·.value)) = true
  originalIndex : ∃ before after,(validateIndex kind arguments).run before = (.ok (),after)

def read (sources : Sources) (caller : String) (naturals : PhaseApplication.Naturals sources)
    (scope : List String) {tokens} (written : StaticApplication.Syntax tokens) (kind : CallName.Primitive) :
    WorkM (Checked sources caller naturals scope written kind) := do
  exactWork (Exact.charge (64*((tokens.map fun token => token.text.utf8ByteSize+4).sum+1)))
  guard (selected kind) .request
  let arguments ← written.arguments.mapM (readNatural sources caller naturals scope)
  if original : arguments.map (·.argument) = written.arguments then
    if bounded : valid kind (arguments.map (·.value)) = true then
      let index ← NaturalAffine.witness (validateIndex kind arguments)
      have unit : index.val = () := by cases index.val; rfl
      return ⟨arguments,original,bounded,by with_reducible simpa only [unit] using index.property⟩
    else throw .request
  else throw .request

def apply (kind : CallName.Primitive) (naturals : List Nat) (arguments : List Value) (nextOrdinal : Nat) :
    Except String (Value × List Semantics.SourceOwners.Owner × List Semantics.SourceOwners.Owner × Nat) := do
  if !valid kind naturals then throw "register primitive original static arguments"
  match kind,naturals,arguments with
  | .prependBit,[width],[[.ordinary bit head],[.ordinary bits tail]] =>
    if bit != [.bit] || bits != [.bits width] then throw "prepend exact ordinary Bit/Bits types"
    return ([.ordinary [.bits (width+1)] (.combine 2 head tail)],[],[],nextOrdinal)
  | .takeBit,[width,_],[[.owner input]] =>
    if input.basis != [.bits width] then throw "take_bit exact original register type"
    let bit : Semantics.SourceOwners.Owner := ⟨nextOrdinal,[.bit]⟩
    let rest : Semantics.SourceOwners.Owner := ⟨nextOrdinal+1,[.bits (width-1)]⟩
    return ([.tuple 2,.owner bit,.owner rest],[bit,rest],[input],nextOrdinal+2)
  | .putBit,[width,_],[[.owner bit],[.owner rest]] =>
    if bit.ordinal == rest.ordinal || bit.basis != [.bit] || rest.basis != [.bits (width-1)] then
      throw "put_bit exact nonaliased Bit/register owners"
    let output : Semantics.SourceOwners.Owner := ⟨nextOrdinal,[.bits width]⟩
    return ([.owner output],[output],[bit,rest],nextOrdinal+1)
  | _,_,_ => throw "register primitive original runtime argument shape"

end QleisliKernel.SourceTypes.SourceRegisterApplication
