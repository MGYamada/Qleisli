import QleisliKernel.SourceTypes
import QleisliKernel.SourceTypes.LocatedFacts

/-! Candidate: original nominal-member syntax with exact byte locations.
The existing lexical, declaration, member splitting and carrier readers are
reused. This catalogue does not authorize a call or a private-field operation,
check an expression tree, accept a runtime program or prove source preservation.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.Members
open Semantics.FiniteCarrier

/-- `none` is a fieldless enum variant. A record retains its complete type-token
sequence; its elaborated tree is also present in the catalogue's whole basis.
No field type is inferred from bit width. -/
structure Member where
  name : LocatedToken
  isPublic : Bool
  typeTokens : Option (List LocatedToken)
  span : SourceSpan
  deriving BEq, DecidableEq, Repr

structure Catalogue where
  origin : Origin
  occurrence : BodyOccurrence
  members : List Member
  basis : Basis
  deriving BEq, DecidableEq, Repr

private def adapt {α : Type} (value : Except String α) : Finite.WorkM α :=
  Finite.lift (value.mapError fun _ => .request)

/-- Recover locations by exact sequential consumption of the existing splitter's
parts. This is not another type/member grammar. A comma is consumed only at the
boundary already chosen by `splitMembers`, including its optional final comma. -/
private def locateParts (tokens : List LocatedToken) :
    Except String (List (List LocatedToken)) := do
  let parts ← splitMembers (tokens.map LocatedToken.text)
  let (remaining,located) ← parts.foldlM (fun (remaining,result) part => do
    let selected := remaining.take part.length
    if selected.map LocatedToken.text != part then throw "member token alignment"
    let tail := remaining.drop part.length
    let tail ← match tail with
      | [] => pure []
      | comma :: rest =>
        if comma.text != "," then throw "member separator alignment"
        pure rest
    pure (tail,selected :: result)) (tokens,[])
  if !remaining.isEmpty then throw "unconsumed member tokens"
  return located.reverse

private def member (enumeration : Bool) (tokens : List LocatedToken) : Except String Member := do
  if enumeration then
    let [name] := tokens | throw "variant must be fieldless"
    if !identifier name.text then throw "invalid variant name"
    return ⟨name,true,none,name.span⟩
  let isPublic := tokens.head?.map (·.text) == some "pub"
  let rest := if isPublic then tokens.drop 1 else tokens
  let name :: colon :: ty := rest | throw "missing field type"
  if !identifier name.text || colon.text != ":" || ty.isEmpty then
    throw "invalid record field"
  let some first := tokens.head? | throw "missing field start"
  let some last := ty.getLast? | throw "missing field type end"
  return ⟨name,isPublic,some ty,⟨first.span.startByte,last.span.endByte⟩⟩

/-- Syntax-only extraction. The original whole-carrier reader subsequently
checks semantic types, closed sizes, recursion, unique names and finite limits. -/
private def readSyntax (source : String) (occurrence : BodyOccurrence) : Except String (List Member) := do
  let decl := occurrence.declaration
  if decl.kind != "enum" && decl.kind != "struct" then throw "not a nominal declaration"
  let expected := (if decl.isPublic then ["pub"] else []) ++ [decl.kind,decl.name]
  if occurrence.header.map LocatedToken.text != expected then
    let directive := ["#","!","[","no_implicit_prelude","]"]
    if occurrence.header.map LocatedToken.text != directive ++ expected then
      throw "unsupported original nominal header"
    -- Permit exactly the real initial module directive, not a matching prefix
    -- copied from another site or arbitrary skipped tokens. Reuse this lexer.
    let initial ← lexLocated source
    if initial.take directive.length != occurrence.header.take directive.length then
      throw "nominal header directive is not initial"
  if occurrence.body.map LocatedToken.text != decl.body then
    throw "original nominal body mismatch"
  let parts ← locateParts occurrence.body
  if parts.length > 64 then throw "nominal member capacity"
  let members ← parts.mapM (member (decl.kind == "enum"))
  let names := members.map (fun item => item.name.text)
  if !FiniteCarrier.namesValid names || (decl.kind == "enum" && names.isEmpty) then
    throw "invalid or duplicate nominal members"
  return members

/-- Factor the same fresh catalogue scan, without a supplied occurrence table. -/
private def selectOccurrence (source : String) (decl : Declaration) : Except String BodyOccurrence := do
  let catalogue ← sourceCatalogue source
  let [occurrence] := catalogue.bodies.filter (fun body => body.declaration == decl)
    | throw "missing/ambiguous original body occurrence"
  return occurrence

/-- This is exactly the previous final branch guard, factored for a direct
refinement proof. It changes no supported nominal root or member order. -/
private def matchingHead (decl : Declaration) (origin : Origin) (members : List Member)
    (basis : Basis) : Bool :=
  let names := members.map (fun item => item.name.text)
  match basis.head? with
  | some (.enumeration original variants) =>
    (decl.kind == "enum" && original == origin) && variants == names
  | some (.record original fields) =>
    (decl.kind == "struct" && original == origin) && fields == names
  | _ => false

/-- Read one canonical original declaration. This is catalogue lookup only:
there is deliberately no caller-module argument and no access verdict. A future
site checker must derive its calling context from a checked original expression
and resolve its path using the existing `resolveReference` function. -/
def readOriginal (sources : Sources) (moduleName declarationName : String) :
    Finite.WorkM Catalogue := do
  Finite.guard (sources.size ≤ 128) .limit
  let bytes := (sources.toList.map fun row => row.1.utf8ByteSize + row.2.utf8ByteSize).sum
  Finite.guard (bytes ≤ 1048576) .limit
  Finite.exactWork (Exact.charge (4*bytes+moduleName.utf8ByteSize+declarationName.utf8ByteSize+1))
  let (source,decl) ← adapt (originalBinding sources moduleName declarationName)
  let occurrence ← adapt (selectOccurrence source decl)
  -- These checks apply only to this new catalogue API. The existing lexical
  -- and declaration APIs keep their success/error behavior unchanged.
  let envelope := occurrence.header ++ [occurrence.openBrace] ++
    occurrence.body ++ [occurrence.closeBrace]
  Finite.exactWork (Exact.charge (2*source.utf8ByteSize+envelope.length+1))
  Finite.guard (LocatedFacts.checkOrdered source.toUTF8 0 envelope) .request
  Finite.guard (((occurrence.nameToken.text == decl.name &&
    occurrence.header.contains occurrence.nameToken) &&
    occurrence.openBrace.text == "{") && occurrence.closeBrace.text == "}") .request
  Finite.exactWork (Exact.charge (source.utf8ByteSize*65+1))
  let members ← adapt (readSyntax source occurrence)
  let origin : Origin := ⟨moduleName,declarationName,source⟩
  let basis ← nominal sources origin
  let _ ← FiniteCarrier.read basis
  Finite.guard (matchingHead decl origin members basis) .request
  return ⟨origin,occurrence,members,basis⟩

/-- Independent exact member shape. Public/private markers, full type token
lists and original name/covering spans are data, not successful parser calls. -/
inductive PartMember : Bool → List LocatedToken → Member → Prop
  | variant (name : LocatedToken) :
      PartMember true [name] ⟨name,true,none,name.span⟩
  | hidden (name colon : LocatedToken) (ty : List LocatedToken) (last : LocatedToken)
      (colonText : colon.text = ":") (nonempty : ty ≠ []) (lastToken : ty.getLast? = some last) :
      PartMember false (name :: colon :: ty)
        ⟨name,false,some ty,⟨name.span.startByte,last.span.endByte⟩⟩
  | publicField (marker name colon : LocatedToken) (ty : List LocatedToken) (last : LocatedToken)
      (markerText : marker.text = "pub") (colonText : colon.text = ":")
      (nonempty : ty ≠ []) (lastToken : ty.getLast? = some last) :
      PartMember false (marker :: name :: colon :: ty)
        ⟨name,true,some ty,⟨marker.span.startByte,last.span.endByte⟩⟩

/-- Candidate refinement of the actual extraction operation, for arbitrary input
parts and arbitrary successful output. This is not merely a sample constructor. -/
theorem member_refines (enumeration : Bool) (tokens : List LocatedToken) (item : Member)
    (ok : member enumeration tokens = .ok item) : PartMember enumeration tokens item := by
  dsimp only [member, bind, Except.bind, pure, Except.pure, Functor.map, Except.map,
    throw, throwThe] at ok
  cases enumeration with
  | true =>
    cases tokens with
    | nil => simp_all
    | cons name rest =>
      cases rest with
      | cons extra rest => simp_all
      | nil =>
        cases valid : identifier name.text with
        | false => simp_all
        | true =>
          have resultEq : (⟨name,true,none,name.span⟩ : Member) = item := by
            simp_all
          subst item
          exact .variant name
  | false =>
    cases tokens with
    | nil => simp_all
    | cons first rest =>
      by_cases marker : first.text = "pub"
      · cases rest with
        | nil => simp_all
        | cons name rest =>
          cases rest with
          | nil => simp_all
          | cons colon ty =>
            cases ty with
            | nil => simp_all
            | cons firstTy tail =>
              cases valid : identifier name.text with
              | false => simp_all
              | true =>
                by_cases colonText : colon.text = ":"
                · cases lastToken : (firstTy :: tail).getLast? with
                  | none => simp at lastToken
                  | some last =>
                    have resultEq : (⟨name,true,some (firstTy :: tail),
                        ⟨first.span.startByte,last.span.endByte⟩⟩ : Member) = item := by
                      simp_all
                    subst item
                    exact .publicField first name colon (firstTy :: tail) last
                      marker colonText (by simp) lastToken
                · simp_all
      · have notPublic : (first.text == "pub") = false := beq_eq_false_iff_ne.mpr marker
        cases rest with
        | nil => simp_all
        | cons colon ty =>
          cases ty with
          | nil => simp_all
          | cons firstTy tail =>
            cases valid : identifier first.text with
            | false => simp_all
            | true =>
              by_cases colonText : colon.text = ":"
              · cases lastToken : (firstTy :: tail).getLast? with
                | none => simp at lastToken
                | some last =>
                  have resultEq : (⟨first,false,some (firstTy :: tail),
                      ⟨first.span.startByte,last.span.endByte⟩⟩ : Member) = item := by
                    simp_all
                    rw [beq_eq_false_iff_ne.mpr marker] at ok
                    exact ok
                  subst item
                  exact .hidden first colon (firstTy :: tail) last colonText (by simp) lastToken
              · simp_all

/-- Independent observable facts about an actual returned catalogue. This
relation calls no source/member reader or acceptance decision. It does not say
that the complete body is a valid AST, or authorize a private-field operation. -/
structure Boundary (sources : Sources) (moduleName declarationName : String)
    (result : Catalogue) : Prop where
  moduleNameExact : result.origin.moduleName = moduleName
  declarationNameExact : result.origin.declarationName = declarationName
  sourceRows : sources.toList.filter (fun row => row.1 == moduleName) =
    [(moduleName,result.origin.source)]
  sourceCount : sources.size ≤ 128
  sourceBytes : (sources.toList.map (fun row => row.1.utf8ByteSize + row.2.utf8ByteSize)).sum ≤ 1048576
  originalName : result.occurrence.declaration.name = declarationName
  nameBytes : result.occurrence.nameToken.text = declarationName
  nameInHeader : result.occurrence.nameToken ∈ result.occurrence.header
  located : LocatedFacts.OrderedSlices result.origin.source.toUTF8 0
    (result.occurrence.header ++ [result.occurrence.openBrace] ++
      result.occurrence.body ++ [result.occurrence.closeBrace])
  opening : result.occurrence.openBrace.text = "{"
  closing : result.occurrence.closeBrace.text = "}"
  nominalHead : (result.occurrence.declaration.kind = "enum" ∧
      result.basis.head? = some (.enumeration result.origin (result.members.map (fun item => item.name.text)))) ∨
    (result.occurrence.declaration.kind = "struct" ∧
      result.basis.head? = some (.record result.origin (result.members.map (fun item => item.name.text))))
  logicalLayout : ∃ layoutValue, Semantics.FiniteCarrier.layout result.basis = some layoutValue

/-- Actual subordinate-reader provenance for the same returned source, occurrence
and complete basis. Kept separate from the independent data-level Boundary.
Neither field calls readOriginal or assumes caller privilege/AST fidelity. -/
structure ReaderBindings (sources : Sources) (result : Catalogue) : Prop where
  original : originalBinding sources result.origin.moduleName result.origin.declarationName =
    .ok (result.origin.source,result.occurrence.declaration)
  wholeBasis : ∃ work left,
    (nominal sources result.origin).run work = (.ok result.basis,left)

private theorem adapt_value {α : Type} (value : Except String α) (result : α) (work left : Nat)
    (ok : (adapt value).run work = (.ok result,left)) : value = .ok result := by
  have bound := (Finite.lift_success _ _ _ _ ok).1
  cases value <;> simp_all [Except.mapError]

/-- The source row and name facts follow from the actual original lookup. No
caller-supplied source identity, success flag or privilege is a premise. -/
private theorem originalBinding_rows (sources : Sources) (moduleName name source : String)
    (decl : Declaration) (ok : originalBinding sources moduleName name = .ok (source,decl)) :
    sources.toList.filter (fun row => row.1 == moduleName) = [(moduleName,source)] ∧
      decl.name = name := by
  dsimp only [originalBinding, bind, Except.bind, pure, Except.pure, Functor.map, Except.map,
    throw, throwThe] at ok
  cases rows : sources.toList.filter (fun row => row.1 == moduleName) with
  | nil => simp_all
  | cons row rest =>
    cases rest with
    | cons second rest => simp_all
    | nil =>
      rcases row with ⟨owner,original⟩
      have present : (owner,original) ∈ sources.toList.filter (fun row => row.1 == moduleName) := by
        simp [rows]
      have sameOwner : owner = moduleName := by
        simpa using (List.mem_filter.mp present).2
      subst owner
      cases declarationsRead : declarations original with
      | error error => simp_all
      | ok items =>
        cases selected : items.filter (fun item => item.name == name) with
        | nil => simp_all
        | cons item tail =>
          cases tail with
          | cons other tail => simp_all
          | nil =>
            have same : (original,item) = (source,decl) := by
              simp_all
            have sameSource : original = source := congrArg Prod.fst same
            have sameDeclaration : item = decl := congrArg Prod.snd same
            subst source
            subst decl
            have member : item ∈ items.filter (fun item => item.name == name) := by
              simp [selected]
            exact ⟨rfl,by simpa using (List.mem_filter.mp member).2⟩

private theorem selectOccurrence_original (source : String) (decl : Declaration)
    (occurrence : BodyOccurrence) (ok : selectOccurrence source decl = .ok occurrence) :
    occurrence.declaration = decl := by
  dsimp only [selectOccurrence, bind, Except.bind, pure, Except.pure, Functor.map, Except.map,
    throw, throwThe] at ok
  cases catalogueRead : sourceCatalogue source with
  | error error => simp_all
  | ok catalogue =>
    cases selected : catalogue.bodies.filter (fun body => body.declaration == decl) with
    | nil => simp_all
    | cons body tail =>
      cases tail with
      | cons other tail => simp_all
      | nil =>
        have same : body = occurrence := by
          simp_all
        subst occurrence
        have member : body ∈ catalogue.bodies.filter (fun body => body.declaration == decl) := by
          simp [selected]
        simpa using (List.mem_filter.mp member).2

private theorem matchingHead_facts (decl : Declaration) (origin : Origin)
    (members : List Member) (basis : Basis)
    (ok : matchingHead decl origin members basis = true) :
    (decl.kind = "enum" ∧ basis.head? = some (.enumeration origin (members.map (fun item => item.name.text)))) ∨
      (decl.kind = "struct" ∧ basis.head? = some (.record origin (members.map (fun item => item.name.text)))) := by
  cases head : basis.head? with
  | none => simp [matchingHead,head] at ok
  | some atom =>
    cases atom <;> simp only [matchingHead,head] at ok
    all_goals try contradiction
    case enumeration original variants =>
      have facts := Bool.and_eq_true_iff.mp ok
      have first := Bool.and_eq_true_iff.mp facts.1
      have kind : decl.kind = "enum" := beq_iff_eq.mp first.1
      have sameOrigin : original = origin := beq_iff_eq.mp first.2
      have names : variants = members.map (fun item => item.name.text) := beq_iff_eq.mp facts.2
      exact Or.inl ⟨kind,by simp [sameOrigin,names]⟩
    case record original fields =>
      have facts := Bool.and_eq_true_iff.mp ok
      have first := Bool.and_eq_true_iff.mp facts.1
      have kind : decl.kind = "struct" := beq_iff_eq.mp first.1
      have sameOrigin : original = origin := beq_iff_eq.mp first.2
      have names : fields = members.map (fun item => item.name.text) := beq_iff_eq.mp facts.2
      exact Or.inr ⟨kind,by simp [sameOrigin,names]⟩

/-- Candidate proof from the actual successful computation to original bytes,
real source/name identity, ordered locations and the actual whole-basis layout.
No field-subtree, full member grammar, caller privilege or source preservation
is claimed by this deliberately smaller proof target. -/
theorem readOriginal_facts (sources : Sources) (moduleName declarationName : String)
    (result : Catalogue) (work left : Nat)
    (ok : (readOriginal sources moduleName declarationName).run work = (.ok result,left)) :
    Boundary sources moduleName declarationName result ∧ ReaderBindings sources result := by
  unfold readOriginal at ok
  obtain ⟨_,w₁,count,h⟩ := Finite.bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,bytes,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨_,w₃,_,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨entry,w₄,original,h⟩ := Finite.bind_success _ _ _ _ _ h
  rcases entry with ⟨source,decl⟩
  obtain ⟨occurrence,w₅,selected,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨_,w₆,_,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨_,w₇,located,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨_,w₈,named,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨_,w₉,_,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨members,w₁₀,_,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨basis,w₁₁,nominalRead,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨layoutValue,w₁₂,layoutRead,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨_,w₁₃,head,h⟩ := Finite.bind_success _ _ _ _ _ h
  have sameResult := (Finite.pure_success _ _ _ _ h).1
  subst result
  have originalRead := adapt_value _ _ _ _ original
  have rowFacts := originalBinding_rows _ _ _ _ _ originalRead
  have selectedRead := adapt_value _ _ _ _ selected
  have sameDeclaration := selectOccurrence_original _ _ _ selectedRead
  have tokenFacts := Bool.and_eq_true_iff.mp (Finite.guard_success _ _ _ _ named).1
  have openFacts := Bool.and_eq_true_iff.mp tokenFacts.1
  have nameFacts := Bool.and_eq_true_iff.mp openFacts.1
  constructor
  · refine ⟨rfl,rfl,rowFacts.1,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · exact of_decide_eq_true (Finite.guard_success _ _ _ _ count).1
    · exact of_decide_eq_true (Finite.guard_success _ _ _ _ bytes).1
    · simpa only [sameDeclaration] using rowFacts.2
    · exact (beq_iff_eq.mp nameFacts.1).trans rowFacts.2
    · exact List.contains_iff_mem.mp nameFacts.2
    · exact LocatedFacts.checkOrdered_sound _ _ _ (Finite.guard_success _ _ _ _ located).1
    · exact beq_iff_eq.mp openFacts.2
    · exact beq_iff_eq.mp tokenFacts.2
    · rw [sameDeclaration]
      exact matchingHead_facts _ _ _ _ (Finite.guard_success _ _ _ _ head).1
    · exact ⟨layoutValue,FiniteCarrier.read_reference _ _ _ _ layoutRead⟩

  · refine ⟨?_,w₁₀,w₁₁,nominalRead⟩
    change originalBinding sources moduleName declarationName = .ok (source,occurrence.declaration)
    rw [sameDeclaration]
    exact originalRead

/-- Direct independent byte/name/layout consequence, derived from the real reader. -/
theorem readOriginal_boundary (sources : Sources) (moduleName declarationName : String)
    (result : Catalogue) (work left : Nat)
    (ok : (readOriginal sources moduleName declarationName).run work = (.ok result,left)) :
    Boundary sources moduleName declarationName result :=
  (readOriginal_facts sources moduleName declarationName result work left ok).1


/-- One exact prefix, followed only by the splitter-selected comma or EOF.
No token, span, field name or type token is synthesized by this relation. -/
inductive PartSlice : List LocatedToken → List LocatedToken → List LocatedToken → Prop
  | final (part : List LocatedToken) : PartSlice part part []
  | comma (part : List LocatedToken) (separator : LocatedToken) (remaining : List LocatedToken)
      (isComma : separator.text = ",") :
      PartSlice (part ++ (separator :: remaining)) part remaining

/-- Ordered consumption of original tokens. An empty final remainder rules out
omitted tokens. Only comma separators may be omitted between retained parts. -/
inductive PartSequence : List LocatedToken → List (List LocatedToken) → List LocatedToken → Prop
  | nil (remaining : List LocatedToken) : PartSequence remaining [] remaining
  | cons {tokens part following remaining : List LocatedToken} {parts : List (List LocatedToken)}
      (first : PartSlice tokens part following) (rest : PartSequence following parts remaining) :
      PartSequence tokens (part :: parts) remaining

private theorem partSequence_append {tokens middle remaining : List LocatedToken}
    {firstParts restParts : List (List LocatedToken)}
    (first : PartSequence tokens firstParts middle)
    (rest : PartSequence middle restParts remaining) :
    PartSequence tokens (firstParts ++ restParts) remaining := by
  induction first generalizing restParts remaining with
  | nil _ => exact rest
  | cons head tail ih => exact .cons head (ih rest)

/-- String-error specialization of the existing Finite/Exact success lemma.
It describes the actual Except result and adds no accepting computation. -/
private theorem string_bind_success {α β : Type} (first : Except String α)
    (next : α → Except String β) (result : β) (ok : (first >>= next) = .ok result) :
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first with
  | error error => simp [bind,Except.bind] at ok
  | ok value => exact ⟨value,rfl,ok⟩

private theorem string_fold_invariant {α β : Type} (step : β → α → Except String β)
    (property : β → Prop)
    (preserve : ∀ before item after, property before → step before item = .ok after → property after)
    (items : List α) (initial result : β) (start : property initial)
    (ok : items.foldlM step initial = .ok result) : property result := by
  induction items generalizing initial with
  | nil =>
    simp only [List.foldlM_nil,pure,Except.pure,Except.ok.injEq] at ok
    simpa [← ok] using start
  | cons item items ih =>
    simp only [List.foldlM_cons] at ok
    obtain ⟨next,stepOk,tailOk⟩ := string_bind_success _ _ _ ok
    exact ih next (preserve initial item next start stepOk) tailOk

private theorem string_map_relation {α β : Type} (step : α → Except String β)
    (relation : α → β → Prop)
    (preserve : ∀ item value, step item = .ok value → relation item value)
    (items : List α) (values : List β) (ok : items.mapM step = .ok values) :
    Exact.ListRel relation items values := by
  induction items generalizing values with
  | nil =>
    simp only [List.mapM_nil,pure,Except.pure,Except.ok.injEq] at ok
    subst values
    trivial
  | cons item items ih =>
    simp only [List.mapM_cons] at ok
    obtain ⟨value,stepOk,h⟩ := string_bind_success _ _ _ ok
    obtain ⟨rest,tailOk,h⟩ := string_bind_success _ _ _ h
    simp only [pure,Except.pure,Except.ok.injEq] at h
    subst values
    exact ⟨preserve item value stepOk,ih rest tailOk⟩

/-- The actual located splitter consumes the original token list in order.
This proves its local prefix/separator behavior; it does not prove the lexical
reader complete, or independently validate a full source expression grammar. -/
theorem locateParts_consumes (tokens : List LocatedToken) (parts : List (List LocatedToken))
    (ok : locateParts tokens = .ok parts) : PartSequence tokens parts [] := by
  unfold locateParts at ok
  obtain ⟨textParts,_,h⟩ := string_bind_success _ _ _ ok
  obtain ⟨state,foldOk,h⟩ := string_bind_success _ _ _ h
  rcases state with ⟨remaining,reversed⟩
  cases remaining with
  | cons token remaining =>
    change (Except.error "unconsumed member tokens" : Except String (List (List LocatedToken))) =
      .ok parts at h
    cases h
  | nil =>
    have same : reversed.reverse = parts := by
      change (Except.ok reversed.reverse : Except String (List (List LocatedToken))) = .ok parts at h
      exact Except.ok.inj h
    rw [← same]
    refine string_fold_invariant _
      (fun state : List LocatedToken × List (List LocatedToken) =>
        PartSequence tokens state.2.reverse state.1) ?_
      textParts (tokens,[]) ([],reversed) (.nil tokens) foldOk
    intro before part after beforeOk stepOk
    rcases before with ⟨suffix,previous⟩
    dsimp only at beforeOk stepOk ⊢
    dsimp only [bind,Except.bind,pure,Except.pure,Functor.map,Except.map,
      throw,throwThe] at stepOk
    by_cases aligned : (suffix.take part.length).map LocatedToken.text = part
    · cases dropped : suffix.drop part.length with
      | nil =>
        have sameAfter : ([],suffix.take part.length :: previous) = after := by
          simpa [aligned,dropped] using stepOk
        subst after
        have sliced : PartSlice (suffix.take part.length ++ suffix.drop part.length)
            (suffix.take part.length) [] := by
          rw [dropped]
          simpa only [List.append_nil] using (PartSlice.final (suffix.take part.length))
        have original : PartSlice suffix (suffix.take part.length) [] := by
          simpa only [List.take_append_drop] using sliced
        simpa only [List.reverse_cons] using
          (partSequence_append beforeOk (.cons original (.nil [])))
      | cons separator rest =>
        by_cases isComma : separator.text = ","
        · have sameAfter : (rest,suffix.take part.length :: previous) = after := by
            simpa [aligned,dropped,isComma] using stepOk
          subst after
          have sliced : PartSlice (suffix.take part.length ++ suffix.drop part.length)
              (suffix.take part.length) rest := by
            rw [dropped]
            exact .comma (suffix.take part.length) separator rest isComma
          have original : PartSlice suffix (suffix.take part.length) rest := by
            simpa only [List.take_append_drop] using sliced
          simpa only [List.reverse_cons] using
            (partSequence_append beforeOk (.cons original (.nil rest)))
        · simp [aligned,dropped,isComma] at stepOk
    · simp only [List.map_take] at aligned
      simp [aligned] at stepOk

/-- Each returned member retains its exact original token part at the same
position. PartMember fixes full typeTokens, pub markers, names and covering spans;
PartSequence fixes original token identity, order and complete consumption. -/
def OriginalMemberParts (occurrence : BodyOccurrence) (members : List Member) : Prop :=
  ∃ parts, PartSequence occurrence.body parts [] ∧
    Exact.ListRel (PartMember (occurrence.declaration.kind == "enum")) parts members

private theorem readSyntax_member_runs (source : String) (occurrence : BodyOccurrence)
    (members : List Member) (ok : readSyntax source occurrence = .ok members) :
    ∃ parts, locateParts occurrence.body = .ok parts ∧
      parts.mapM (member (occurrence.declaration.kind == "enum")) = .ok members := by
  cases located : locateParts occurrence.body with
  | error error =>
    dsimp only [readSyntax,bind,Except.bind,pure,Except.pure,Functor.map,Except.map,
      throw,throwThe] at ok
    simp only [located] at ok
    repeat first
      | contradiction
      | simp_all (config := { failIfUnchanged := true }) only [bind,Except.bind,pure,Except.pure,Functor.map,Except.map,
          throw,throwThe,Except.ok.injEq]
      | split at ok
  | ok parts =>
    cases mapped : parts.mapM (member (occurrence.declaration.kind == "enum")) with
    | error error =>
      dsimp only [readSyntax,bind,Except.bind,pure,Except.pure,Functor.map,Except.map,
        throw,throwThe] at ok
      simp only [located,mapped] at ok
      repeat first
        | contradiction
        | simp_all (config := { failIfUnchanged := true }) only [Except.ok.injEq]
        | split at ok
    | ok selected =>
      have same : selected = members := by
        dsimp only [readSyntax,bind,Except.bind,pure,Except.pure,Functor.map,Except.map,
          throw,throwThe] at ok
        simp only [located,mapped] at ok
        repeat first
          | contradiction
          | simp_all (config := { failIfUnchanged := true }) only [Except.ok.injEq]
          | split at ok
      subst members
      exact ⟨parts,rfl,mapped⟩

/-- Lift the actual per-part extraction proof through the actual mapM run. -/
theorem readSyntax_originalParts (source : String) (occurrence : BodyOccurrence)
    (members : List Member) (ok : readSyntax source occurrence = .ok members) :
    OriginalMemberParts occurrence members := by
  obtain ⟨parts,located,mapped⟩ := readSyntax_member_runs source occurrence members ok
  exact ⟨parts,locateParts_consumes _ _ located,
    string_map_relation _ _ (member_refines _) _ _ mapped⟩

/-- Actual readOriginal success yields ordered exact member parts for that same
returned occurrence. This retains the discarded syntax bind from the existing
boundary proof; it assumes no caller privilege, AST fidelity or success receipt. -/
theorem readOriginal_memberParts (sources : Sources) (moduleName declarationName : String)
    (result : Catalogue) (work left : Nat)
    (ok : (readOriginal sources moduleName declarationName).run work = (.ok result,left)) :
    OriginalMemberParts result.occurrence result.members := by
  unfold readOriginal at ok
  obtain ⟨_,w₁,_,h⟩ := Finite.bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,_,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨_,w₃,_,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨entry,w₄,_,h⟩ := Finite.bind_success _ _ _ _ _ h
  rcases entry with ⟨source,decl⟩
  obtain ⟨occurrence,w₅,_,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨_,w₆,_,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨_,w₇,_,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨_,w₈,_,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨_,w₉,_,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨members,w₁₀,syntaxRun,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨basis,w₁₁,_,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨layoutValue,w₁₂,_,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨_,w₁₃,_,h⟩ := Finite.bind_success _ _ _ _ _ h
  have sameResult := (Finite.pure_success _ _ _ _ h).1
  subst result
  exact readSyntax_originalParts source occurrence members (adapt_value _ _ _ _ syntaxRun)

/-- Exact indexed consequence, using the existing kernel ListRel lemmas. The
complete logical field subtree is still a separate, unproved elaboration link. -/
theorem originalMemberParts_ordered (occurrence : BodyOccurrence) (members : List Member)
    (facts : OriginalMemberParts occurrence members) :
    ∃ parts, PartSequence occurrence.body parts [] ∧ ∃ sameLength : members.length = parts.length,
      ∀ (index : Nat) (within : index < parts.length),
        PartMember (occurrence.declaration.kind == "enum") (parts[index]'within)
          (members[index]'(by rw [sameLength]; exact within)) := by
  obtain ⟨parts,consumed,related⟩ := facts
  refine ⟨parts,consumed,Exact.listRel_length _ _ _ related,?_⟩
  intro index within
  exact Exact.listRel_getElem _ _ _ related index within

end QleisliKernel.SourceTypes.Members
