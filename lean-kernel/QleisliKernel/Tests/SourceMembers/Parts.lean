import QleisliKernel.SourceTypes.Members

/-! Validation probes for original member-part consumption and ordered syntax facts.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace MemberPartsProbes
open QleisliKernel QleisliKernel.SourceTypes QleisliKernel.SourceTypes.Members

example (sources : Sources) (moduleName declarationName : String)
    (result : Catalogue) (work left : Nat)
    (ok : (readOriginal sources moduleName declarationName).run work = (.ok result,left)) :
    OriginalMemberParts result.occurrence result.members :=
  readOriginal_memberParts sources moduleName declarationName result work left ok

example (sources : Sources) (moduleName declarationName : String)
    (result : Catalogue) (work left : Nat)
    (ok : (readOriginal sources moduleName declarationName).run work = (.ok result,left)) :
    Boundary sources moduleName declarationName result ∧
      ReaderBindings sources result ∧ OriginalMemberParts result.occurrence result.members :=
  ⟨(readOriginal_facts sources moduleName declarationName result work left ok).1,
   (readOriginal_facts sources moduleName declarationName result work left ok).2,
   readOriginal_memberParts sources moduleName declarationName result work left ok⟩

private def zeroName : LocatedToken := ⟨"zero",⟨0,4⟩⟩
private def zeroColon : LocatedToken := ⟨":",⟨4,5⟩⟩
private def unitToken : LocatedToken := ⟨"Unit",⟨6,10⟩⟩
private def commaToken : LocatedToken := ⟨",",⟨10,11⟩⟩
private def bitName : LocatedToken := ⟨"bit",⟨11,14⟩⟩
private def bitColon : LocatedToken := ⟨":",⟨14,15⟩⟩
private def bitToken : LocatedToken := ⟨"Bit",⟨16,19⟩⟩
private def zeroPart := [zeroName,zeroColon,unitToken]
private def bitPart := [bitName,bitColon,bitToken]
private def zeroMember : Member := ⟨zeroName,false,some [unitToken],⟨0,10⟩⟩
private def bitMember : Member := ⟨bitName,false,some [bitToken],⟨11,19⟩⟩

-- The Unit field has no carrier bit but still occupies its original position.
example : PartSequence (zeroPart ++ (commaToken :: bitPart)) [zeroPart,bitPart] [] :=
  .cons (.comma zeroPart commaToken bitPart rfl) (.cons (.final bitPart) (.nil []))

example : Exact.ListRel (PartMember false) [zeroPart,bitPart] [zeroMember,bitMember] := by
  exact ⟨.hidden zeroName zeroColon [unitToken] unitToken rfl (by simp) (by simp),
    .hidden bitName bitColon [bitToken] bitToken rfl (by simp) (by simp),trivial⟩

-- Omitting the zero-width field cannot preserve the ordered member relation.
example : ¬ Exact.ListRel (PartMember false) [zeroPart,bitPart] [bitMember] := by
  simp [Exact.ListRel]

-- Invert generic record syntax before specializing to concrete token strings.
private theorem record_fields (tokens : List LocatedToken) (item : Member)
    (facts : PartMember false tokens item) :
    (tokens.drop (if item.isPublic then 1 else 0)).head? = some item.name ∧
      item.typeTokens = some (tokens.drop (if item.isPublic then 3 else 2)) := by
  cases facts <;> exact ⟨rfl,rfl⟩

-- Reusing the wrong field's type tokens or swapping the members is rejected.
example : ¬ PartMember false zeroPart bitMember := by
  intro wrong
  have names := (record_fields _ _ wrong).1
  change (some zeroName : Option LocatedToken) = some bitName at names
  have texts := congrArg LocatedToken.text (Option.some.inj names)
  exact (by decide : ("zero" : String) ≠ "bit") texts

example : ¬ PartMember false zeroPart {zeroMember with typeTokens := some [bitToken]} := by
  intro wrong
  have types := (record_fields _ _ wrong).2
  change (some [bitToken] : Option (List LocatedToken)) = some [unitToken] at types
  have texts := congrArg (List.map LocatedToken.text) (Option.some.inj types)
  exact (by decide : (["Bit"] : List String) ≠ ["Unit"]) texts

-- Print the actual theorem signatures and their axiom dependencies during validation.
#check @readOriginal_memberParts
#check @originalMemberParts_ordered
#print axioms locateParts_consumes
#print axioms readSyntax_originalParts
#print axioms readOriginal_memberParts
#print axioms originalMemberParts_ordered
end MemberPartsProbes
