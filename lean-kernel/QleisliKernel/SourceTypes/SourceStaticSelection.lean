import QleisliKernel.SourceTypes.SourceStaticControlSyntax
import QleisliKernel.SourceTypes.PhaseApplication
import QleisliKernel.SourceTypes.NaturalRows

/-! Closed selection of an original static comparison after symbolic operand
validation. This is preparation only: original typing/effect/access checking of
both source arms remains mandatory before a body gate may use the selection.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceStaticSelection
open Finite

def validate (sources : Sources) (caller : String) (naturals : PhaseApplication.Naturals sources)
    (scope : List String) (predicate : Semantics.SourceNatural.Predicate) : WorkM Unit := do
  PhaseApplication.validateNatural sources caller naturals scope predicate.left
  PhaseApplication.validateNatural sources caller naturals scope predicate.right

def assumeSelected (caller : String) {sources : Sources} (naturals : PhaseApplication.Naturals sources)
    (scope : List String) (predicate : Semantics.SourceNatural.Predicate) (selected : Bool) :
    WorkM (Option (GenericLexicalNatural.SomeEnvironment sources)) :=
  match naturals.generic with
  | none => pure none
  | some state => do return some (← GenericLexicalNatural.assume state caller scope predicate selected)

structure Checked (sources : Sources) (caller : String) (naturals : PhaseApplication.Naturals sources)
    (scope : List String) {tokens : List LocatedToken} (written : SourceStaticControlSyntax.Checked tokens) where
  validated : ∃ before after,(validate sources caller naturals scope written.predicate).run before = (.ok (),after)
  condition : LexicalNatural.PredicateChecked sources caller naturals.helpers.val naturals.environment scope written.predicate
  conditionRead : ∃ before after,
    (LexicalNatural.readPredicate sources caller naturals.helpers.val naturals.environment scope written.predicate).run before =
      (.ok condition,after)
  generic : Option (GenericLexicalNatural.SomeEnvironment sources)
  genericRead : ∃ before after,
    (assumeSelected caller naturals scope written.predicate condition.value).run before = (.ok generic,after)
  rows : List (String × String)
  rowsRead : ∃ before after,
    (NaturalRows.bindings sources caller naturals.helpers.val condition.bindings.val).run before = (.ok rows,after)

def Checked.selected {sources caller naturals scope tokens written}
    (checked : @Checked sources caller naturals scope tokens written) : Bool := checked.condition.value

def Checked.naturals {sources caller naturals scope tokens written}
    (checked : @Checked sources caller naturals scope tokens written) : PhaseApplication.Naturals sources :=
  {naturals with generic := checked.generic,sourceRows := naturals.sourceRows ++ checked.rows}

def read (sources : Sources) (caller : String) (naturals : PhaseApplication.Naturals sources)
    (scope : List String) {tokens : List LocatedToken} (written : SourceStaticControlSyntax.Checked tokens) :
    WorkM (Checked sources caller naturals scope written) := do
  exactWork (Exact.charge (64*((tokens.map fun token => token.text.utf8ByteSize+4).sum+1)))
  let validated ← NaturalAffine.witness (validate sources caller naturals scope written.predicate)
  let condition ← NaturalAffine.witness
    (LexicalNatural.readPredicate sources caller naturals.helpers.val naturals.environment scope written.predicate)
  let generic ← NaturalAffine.witness (assumeSelected caller naturals scope written.predicate condition.val.value)
  let rows ← NaturalAffine.witness (NaturalRows.bindings sources caller naturals.helpers.val condition.val.bindings.val)
  have validatedUnit : validated.val = () := by cases validated.val; rfl
  return ⟨by with_reducible simpa only [validatedUnit] using validated.property,
    condition.val,by with_reducible exact condition.property,
    generic.val,by with_reducible exact generic.property,rows.val,by with_reducible exact rows.property⟩

end QleisliKernel.SourceTypes.SourceStaticSelection
