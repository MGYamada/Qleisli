import QleisliKernel.SourceTypes.Members

/-! Source-only candidate: exact ordered original field subtrees.
This uses the existing original member/type/carrier readers. It returns no
accepted handle and authorizes no constructor or projection. General source
expression preservation and caller-site authentication remain separate duties.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.MemberFields
open Semantics.FiniteCarrier

structure Field where
  member : Members.Member
  basis : Basis
  deriving BEq, DecidableEq, Repr

structure Record where
  original : Members.Catalogue
  fields : List Field
  deriving BEq, DecidableEq, Repr

/-- Structural cells and complete nominal string metadata compared by Atom BEq.
No source string is treated as a constant-cost nominal identity. -/
private def comparisonWork (basis : Basis) : Nat :=
  (basis.map fun atom => match atom with
    | .enumeration origin names | .record origin names =>
      1 + FiniteCarrier.originBytes origin + names.length + (names.map String.utf8ByteSize).sum
    | _ => 1).sum

private def readField (sources : Sources) (moduleName : String) (member : Members.Member) :
    Finite.WorkM Field := do
  let some tokens := member.typeTokens | throw .request
  let basis ← typeExpression sources moduleName (tokens.map LocatedToken.text)
  let _ ← FiniteCarrier.read basis
  return ⟨member,basis⟩

/-- Independently re-read each complete field type in its canonical declaring
module, then compare the full ordered subtree concatenation to the original
whole-record reader. Empty records and zero-width logical nodes are retained. -/
def readOriginalFields (sources : Sources) (moduleName declarationName : String) :
    Finite.WorkM Record := do
  let original ← Members.readOriginal sources moduleName declarationName
  Finite.guard (original.occurrence.declaration.kind == "struct") .request
  let fields ← original.members.mapM (readField sources original.origin.moduleName)
  Finite.exactWork (Exact.charge (comparisonWork original.basis +
    (fields.map (fun field => comparisonWork field.basis)).sum +
    FiniteCarrier.originBytes original.origin +
    (original.members.map (fun member => member.name.text.utf8ByteSize + 1)).sum +
    fields.length + 1))
  let expected := Atom.record original.origin
    (original.members.map (fun member => member.name.text)) :: fields.flatMap (·.basis)
  Finite.guard (original.basis == expected) .request
  return ⟨original,fields⟩

/-- Data-level field facts, independent of source-reader success predicates. -/
structure FieldBoundary (member : Members.Member) (field : Field) : Prop where
  exactMember : field.member = member
  logicalLayout : ∃ shape, Semantics.FiniteCarrier.layout field.basis = some shape

/-- Reader provenance is deliberately separate from independent type-tree
facts: this binds the exact original located tokens and canonical module to
actual existing type reading. Atomic semantic consequences are proved below. -/
def FieldReaderBinding (sources : Sources) (moduleName : String)
    (member : Members.Member) (field : Field) : Prop :=
  ∃ tokens, member.typeTokens = some tokens ∧ ∃ work left,
    (typeExpression sources moduleName (tokens.map LocatedToken.text)).run work =
      (.ok field.basis,left)

structure Boundary (sources : Sources) (moduleName declarationName : String)
    (result : Record) : Prop where
  original : Members.Boundary sources moduleName declarationName result.original
  parts : Members.OriginalMemberParts result.original.occurrence result.original.members
  recordKind : result.original.occurrence.declaration.kind = "struct"
  orderedFields : Exact.ListRel FieldBoundary result.original.members result.fields
  wholeTree : result.original.basis = Atom.record result.original.origin
    (result.original.members.map (fun member => member.name.text)) :: result.fields.flatMap (·.basis)

structure ReaderBindings (sources : Sources) (result : Record) : Prop where
  original : Members.ReaderBindings sources result.original
  fields : Exact.ListRel (FieldReaderBinding sources result.original.origin.moduleName)
    result.original.members result.fields

private theorem readField_facts (sources : Sources) (moduleName : String)
    (member : Members.Member) (field : Field) (work left : Nat)
    (ok : (readField sources moduleName member).run work = (.ok field,left)) :
    FieldBoundary member field ∧ FieldReaderBinding sources moduleName member field := by
  cases tokens : member.typeTokens with
  | none =>
    simp only [readField,tokens] at ok
    cases ok
  | some original =>
    simp only [readField,tokens] at ok
    obtain ⟨basis,a,read,h⟩ := Finite.bind_success _ _ _ _ _ ok
    obtain ⟨shape,b,layoutRead,h⟩ := Finite.bind_success _ _ _ _ _ h
    have same := (Finite.pure_success _ _ _ _ h).1
    subst field
    exact ⟨⟨rfl,⟨shape,FiniteCarrier.read_reference _ _ _ _ layoutRead⟩⟩,
      original,tokens,work,a,read⟩

/-- Finite.WorkM specialization of the existing Exact.work_map_relation proof.
The two work monads have distinct error types; no computation is added. -/
private theorem map_relation {α β : Type} (step : α → Finite.WorkM β) (p : α → β → Prop)
    (preserve : ∀ a b work left, (step a).run work = (.ok b,left) → p a b)
    (xs : List α) (ys : List β) (work left : Nat)
    (ok : (xs.mapM step).run work = (.ok ys,left)) : Exact.ListRel p xs ys := by
  induction xs generalizing ys work left with
  | nil =>
    simp only [List.mapM_nil] at ok
    obtain ⟨same,_⟩ := Finite.pure_success [] ys work left ok
    subst ys
    trivial
  | cons first rest ih =>
    simp only [List.mapM_cons] at ok
    obtain ⟨head,middle,headRead,h⟩ := Finite.bind_success _ _ _ _ _ ok
    obtain ⟨tail,after,tailRead,h⟩ := Finite.bind_success _ _ _ _ _ h
    obtain ⟨same,_⟩ := Finite.pure_success (head :: tail) ys after left h
    subst ys
    exact ⟨preserve first head work middle headRead,ih tail middle after tailRead⟩

theorem readOriginalFields_facts (sources : Sources) (moduleName declarationName : String)
    (result : Record) (work left : Nat)
    (ok : (readOriginalFields sources moduleName declarationName).run work = (.ok result,left)) :
    Boundary sources moduleName declarationName result ∧ ReaderBindings sources result := by
  unfold readOriginalFields at ok
  obtain ⟨original,a,originalRead,h⟩ := Finite.bind_success _ _ _ _ _ ok
  obtain ⟨_,b,kind,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨fields,c,fieldReads,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨_,d,_,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨_,e,whole,h⟩ := Finite.bind_success _ _ _ _ _ h
  have same := (Finite.pure_success _ _ _ _ h).1
  subst result
  obtain ⟨originalFacts,originalBindings⟩ :=
    Members.readOriginal_facts sources moduleName declarationName original work a originalRead
  have partFacts := Members.readOriginal_memberParts sources moduleName declarationName
    original work a originalRead
  have ordered := map_relation (readField sources original.origin.moduleName) FieldBoundary
    (fun member field before after read => (readField_facts _ _ _ _ _ _ read).1)
    original.members fields b c fieldReads
  have bound := map_relation (readField sources original.origin.moduleName)
    (FieldReaderBinding sources original.origin.moduleName)
    (fun member field before after read => (readField_facts _ _ _ _ _ _ read).2)
    original.members fields b c fieldReads
  exact ⟨⟨originalFacts,partFacts,beq_iff_eq.mp (Finite.guard_success _ _ _ _ kind).1,
    ordered,beq_iff_eq.mp (Finite.guard_success _ _ _ _ whole).1⟩,
    ⟨originalBindings,bound⟩⟩

/-- Expose the exact original type-token list for an indexed returned field.
The companion Boundary retains original parts and declaration order. -/
theorem readerBindings_field (sources : Sources) (result : Record)
    (bindings : ReaderBindings sources result) (index : Nat)
    (within : index < result.original.members.length) :
    ∃ sameLength : result.fields.length = result.original.members.length,
      FieldReaderBinding sources result.original.origin.moduleName
        (result.original.members[index]'within)
        (result.fields[index]'(by rw [sameLength]; exact within)) := by
  exact ⟨Exact.listRel_length _ _ _ bindings.fields,
    Exact.listRel_getElem _ _ _ bindings.fields index within⟩

theorem field_unit (sources : Sources) (moduleName : String)
    (member : Members.Member) (field : Field)
    (bound : FieldReaderBinding sources moduleName member field)
    (tokens : List LocatedToken) (original : member.typeTokens = some tokens)
    (text : tokens.map LocatedToken.text = ["Unit"]) : field.basis = [.unit] := by
  obtain ⟨readTokens,readOriginal,work,left,read⟩ := bound
  have same : readTokens = tokens := Option.some.inj (readOriginal.symm.trans original)
  subst readTokens
  rw [text] at read
  exact typeExpression_unit _ _ _ _ _ read

theorem field_bit (sources : Sources) (moduleName : String)
    (member : Members.Member) (field : Field)
    (bound : FieldReaderBinding sources moduleName member field)
    (tokens : List LocatedToken) (original : member.typeTokens = some tokens)
    (text : tokens.map LocatedToken.text = ["Bit"]) : field.basis = [.bit] := by
  obtain ⟨readTokens,readOriginal,work,left,read⟩ := bound
  have same : readTokens = tokens := Option.some.inj (readOriginal.symm.trans original)
  subst readTokens
  rw [text] at read
  exact typeExpression_bit _ _ _ _ _ read

theorem field_bits (sources : Sources) (moduleName : String)
    (member : Members.Member) (field : Field)
    (bound : FieldReaderBinding sources moduleName member field)
    (tokens : List LocatedToken) (original : member.typeTokens = some tokens)
    (rest : List String) (text : tokens.map LocatedToken.text = "Bits" :: "<" :: rest) :
    ∃ width, field.basis = [.bits width] ∧ rest.getLast? = some ">" ∧
      NaturalWidthMeaning sources moduleName rest.dropLast width := by
  obtain ⟨readTokens,readOriginal,work,left,read⟩ := bound
  have same : readTokens = tokens := Option.some.inj (readOriginal.symm.trans original)
  subst readTokens
  rw [text] at read
  exact typeExpression_bits _ _ _ _ _ _ read

/-- Conditional policy fact only. `caller` is supplied data, not an authenticated
original expression site. Import aliases do not change the canonical owner.
This proposition is not an executable access checker or acceptance route. -/
def VisibleFrom (caller : String) (origin : Origin) (member : Members.Member) : Prop :=
  member.isPublic = true ∨ caller = origin.moduleName

theorem hidden_visible_iff_owner (caller : String) (origin : Origin) (member : Members.Member)
    (hidden : member.isPublic = false) : VisibleFrom caller origin member ↔ caller = origin.moduleName := by
  simp [VisibleFrom,hidden]

end QleisliKernel.SourceTypes.MemberFields
