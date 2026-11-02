import QleisliKernel.SourceTypes.SourceMatchSyntax
import QleisliKernel.SourceTypes.SourceNominal
import QleisliKernel.SourceTypes.NaturalRows

/-! Complete original ordinary enum-match labels. Every label retains its own
original nominal query and visibility route; equal cardinalities never identify
different enum declarations.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceMatchLabels
open QleisliKernel QleisliKernel.SourceTypes Finite Semantics.FiniteCarrier

structure Label (sources : Sources) (caller : String) (scope : List String) (basis : Basis)
    (arm : SourceMatchSyntax.Arm) where
  reference : SourceNominal.Variant sources caller scope arm.label
  sameType : reference.nominal.query.basis = basis
  rows : List (String × String)

inductive Labels (sources : Sources) (caller : String) (scope : List String) (basis : Basis) :
    List SourceMatchSyntax.Arm → Type where
  | nil : Labels sources caller scope basis []
  | cons {arm rest} (label : Label sources caller scope basis arm)
      (tail : Labels sources caller scope basis rest) : Labels sources caller scope basis (arm :: rest)

def Labels.ordinals {sources caller scope basis} :
    {arms : List SourceMatchSyntax.Arm} → Labels sources caller scope basis arms → List Nat
  | _,.nil => []
  | _,.cons label rest => label.reference.ordinal :: rest.ordinals

def Labels.sourceRows {sources caller scope basis} :
    {arms : List SourceMatchSyntax.Arm} → Labels sources caller scope basis arms → List (String × String)
  | _,.nil => []
  | _,.cons label rest => label.rows ++ rest.sourceRows

private def readLabels (sources : Sources) (caller : String) (helpers : List NaturalHelpers.Entry)
    (scope : List String) (basis : Basis) :
    (arms : List SourceMatchSyntax.Arm) → WorkM (Labels sources caller scope basis arms)
  | [] => pure .nil
  | arm :: rest => do
    let reference ← SourceNominal.readVariant sources caller scope arm.label
    if sameType : reference.nominal.query.basis = basis then
      let rows ← NaturalRows.typeRead sources caller helpers scope
        (arm.label.typeTokens.map (·.text)) reference.nominal.query
      return .cons ⟨reference,sameType,rows⟩ (← readLabels sources caller helpers scope basis rest)
    else throw .request

structure Checked (sources : Sources) (caller : String) (scope : List String)
    {tokens : List LocatedToken} (written : SourceMatchSyntax.Checked tokens) (basis : Basis) where
  origin : Origin
  names : List String
  enumeration : basis = [.enumeration origin names]
  labels : Labels sources caller scope basis written.parts.arms
  complete : labels.ordinals.Perm (List.range names.length)

def read (sources : Sources) (caller : String) (helpers : List NaturalHelpers.Entry)
    (scope : List String) {tokens} (written : SourceMatchSyntax.Checked tokens) (basis : Basis) :
    WorkM (Checked sources caller scope written basis) := do
  exactWork (Exact.charge (64*((tokens.map fun token => token.text.utf8ByteSize+4).sum+1)))
  match enumeration : basis with
  | [.enumeration origin names] =>
    let labels ← readLabels sources caller helpers scope [.enumeration origin names] written.parts.arms
    if complete : labels.ordinals.Perm (List.range names.length) then
      return ⟨origin,names,rfl,labels,complete⟩
    else throw .request
  | _ => throw .request

end QleisliKernel.SourceTypes.SourceMatchLabels
