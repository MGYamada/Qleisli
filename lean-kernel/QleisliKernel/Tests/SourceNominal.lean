import QleisliKernel.SourceTypes.SourceNominal

/-! Original member identity and zero-width privacy controls. Data-level
references do not authenticate a caller site or issue a runtime handle.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceNominal
open QleisliKernel QleisliKernel.SourceTypes

private def sources : Sources :=
  #[("main","use lib::Box;use lib::Open;use lib::Tag;"),
    ("lib","pub enum Tag{Off,On}pub struct Box{pub shown:Bit,hidden:Unit}pub struct Open{pub first:Bit,pub last:Unit}")]

private def recordView (caller text : String) (scope : List String := []) : Finite.WorkM (List String) := do
  let tokens ← Finite.lift ((lexLocated text).mapError fun _ => .request)
  let written ← Finite.lift ((SourceNominalSyntax.readRecord tokens).mapError fun _ => .request)
  let reference ← SourceNominal.readRecord sources caller scope written
  return reference.fields.map (fun (field : MemberFields.Field) => field.member.name.text)

#guard ((recordView "main" "Open{last:(),first:1}").run 10000000).1.toOption = some ["last","first"]
#guard ((recordView "lib" "Box{hidden:(),shown:1}").run 10000000).1.toOption = some ["hidden","shown"]
#guard ((recordView "main" "Box{hidden:(),shown:1}").run 10000000).1.toOption.isNone
#guard ((recordView "main" "Open{first:1,first:0}").run 10000000).1.toOption.isNone
#guard ((recordView "main" "Open{first:1}").run 10000000).1.toOption.isNone
#guard ((recordView "main" "Open{last:(),first:1}" ["Open"]).run 10000000).1.toOption.isNone

private def variantView (text : String) := do
  let tokens ← Finite.lift ((lexLocated text).mapError fun _ => .request)
  let written ← Finite.lift ((SourceNominalSyntax.readVariant tokens).mapError fun _ => .request)
  let reference ← SourceNominal.readVariant sources "main" [] written
  return (reference.origin.moduleName,reference.origin.declarationName,reference.ordinal)
#guard ((variantView "Tag::On").run 10000000).1.toOption = some ("lib","Tag",1)
#guard ((variantView "Tag::Missing").run 10000000).1.toOption.isNone

private def projectionView (caller text : String) (alterOrigin : Bool := false) :
    Finite.WorkM Semantics.FiniteCarrier.Basis := do
  let query ← typeExpressionWithSources sources "main" ["Box"]
  let basis : Semantics.FiniteCarrier.Basis := if alterOrigin then query.basis.map (fun atom => match atom with
    | .record origin names => .record {origin with source := origin.source ++ " "} names
    | _ => atom) else query.basis
  let tokens ← Finite.lift ((lexLocated text).mapError fun _ => .request)
  let written ← Finite.lift ((SourceNominalSyntax.readProjection tokens).mapError fun _ => .request)
  let reference ← SourceNominal.readProjection sources caller basis written
  return reference.field.basis
#guard ((projectionView "main" "value.shown").run 10000000).1.toOption = some [.bit]
#guard ((projectionView "lib" "value.hidden").run 10000000).1.toOption = some [.unit]
#guard ((projectionView "main" "value.hidden").run 10000000).1.toOption.isNone
#guard ((projectionView "main" "value.shown" true).run 10000000).1.toOption.isNone

#print axioms QleisliKernel.SourceTypes.SourceNominal.readVariant
#print axioms QleisliKernel.SourceTypes.SourceNominal.readRecord
#print axioms QleisliKernel.SourceTypes.SourceNominal.readProjection
end QleisliKernel.Tests.SourceNominal
