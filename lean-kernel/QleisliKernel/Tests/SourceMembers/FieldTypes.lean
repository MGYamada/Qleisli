import QleisliKernel.SourceTypes.MemberFields

/-! Uncompiled exact statement probes; not a completed audit. -/
open QleisliKernel QleisliKernel.SourceTypes QleisliKernel.SourceTypes.MemberFields
open QleisliKernel.Semantics.FiniteCarrier

example (sources : Sources) (moduleName declarationName : String) (result : Record)
    (work left : Nat)
    (ok : (readOriginalFields sources moduleName declarationName).run work = (.ok result,left)) :
    Boundary sources moduleName declarationName result ∧ ReaderBindings sources result :=
  readOriginalFields_facts sources moduleName declarationName result work left ok

example (sources : Sources) (moduleName : String) (rest : List String) (result : Basis)
    (work left : Nat)
    (ok : (typeExpression sources moduleName ("Bits" :: "<" :: rest)).run work = (.ok result,left)) :
    ∃ width, result = [.bits width] ∧ rest.getLast? = some ">" ∧
      NaturalWidthMeaning sources moduleName rest.dropLast width :=
  typeExpression_bits sources moduleName rest result work left ok

example (sources : Sources) (moduleName : String) (member : Members.Member) (field : Field)
    (bound : FieldReaderBinding sources moduleName member field)
    (tokens : List LocatedToken) (original : member.typeTokens = some tokens)
    (rest : List String) (text : tokens.map LocatedToken.text = "Bits" :: "<" :: rest) :
    ∃ width, field.basis = [.bits width] ∧ rest.getLast? = some ">" ∧
      NaturalWidthMeaning sources moduleName rest.dropLast width :=
  field_bits sources moduleName member field bound tokens original rest text

#print axioms QleisliKernel.SourceTypes.typeExpression_unit
#print axioms QleisliKernel.SourceTypes.typeExpression_bit
#print axioms QleisliKernel.SourceTypes.typeExpression_bits
#print axioms QleisliKernel.SourceTypes.MemberFields.readOriginalFields_facts
#print axioms QleisliKernel.SourceTypes.MemberFields.field_unit
#print axioms QleisliKernel.SourceTypes.MemberFields.field_bit
#print axioms QleisliKernel.SourceTypes.MemberFields.field_bits
