import QleisliKernel.SourceTypes.Imports
import QleisliKernel.Finite
import QleisliKernel.Semantics.SourceResolution

/-! Original declaration bodies and canonical module bindings. A category is
checked after resolution; imports cannot change its origin or visibility.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes

private structure Items where
  leading : List LocatedToken := []
  nameToken : Option LocatedToken := none
  openBrace : Option LocatedToken := none
  locatedBody : List LocatedToken := []
  occurrences : List BodyOccurrence := []
  depth : Nat := 0
  isPublic : Bool := false
  kind : String := ""
  name : String := ""
  staticPrefix : Bool := false
  header : List String := []
  body : List String := []
  declarations : List Declaration := []
  importing : Bool := false
  importTokens : List String := []

private def item (s : Items) (located : LocatedToken) : Except String Items := do
  let token := located.text
  let s := if s.depth == 0 then {s with leading := located :: s.leading} else s
  if s.depth > 0 then
    if token == "{" then return {s with depth := s.depth+1,body := token :: s.body,locatedBody := located :: s.locatedBody}
    if token == "}" then
      if s.depth == 1 then
        let declarations := if s.kind == "enum" || s.kind == "struct" then
            ⟨s.name,s.isPublic,s.kind,s.body.reverse⟩ :: s.declarations
          else if s.kind == "static-fn" then
            ⟨s.name,s.isPublic,s.kind,s.header.reverse ++ ["{"] ++ s.body.reverse ++ ["}"]⟩ :: s.declarations
          else s.declarations
        let occurrences ← if ["enum","struct","fn","static-fn"].contains s.kind then do
          let some nameToken := s.nameToken | throw "missing original declaration name token"
          let some openBrace := s.openBrace | throw "missing original declaration opening brace"
          let body := if s.kind == "enum" || s.kind == "struct" then s.body.reverse
            else if s.kind == "static-fn" then s.header.reverse ++ ["{"] ++ s.body.reverse ++ ["}"]
            else []
          let decl : Declaration := ⟨s.name,s.isPublic,s.kind,body⟩
          pure (⟨decl,nameToken,s.leading.reverse.dropLast,openBrace,
            s.locatedBody.reverse,located⟩ :: s.occurrences)
        else pure s.occurrences
        return {s with
          depth := 0
          isPublic := false
          kind := ""
          name := ""
          body := []
          header := []
          staticPrefix := false
          declarations
          leading := []
          nameToken := none
          openBrace := none
          locatedBody := []
          occurrences}
      return {s with depth := s.depth-1,body := token :: s.body,locatedBody := located :: s.locatedBody}
    return {s with
      body := if s.kind.isEmpty then [] else token :: s.body
      locatedBody := if s.kind.isEmpty then [] else located :: s.locatedBody}
  if s.importing then
    if token != ";" then return {s with importTokens := token :: s.importTokens}
    let paths ← Imports.read s.importTokens.reverse
    let declarations ← paths.foldlM (fun declarations path => do
      let name :: _ := path | throw "empty import path"
      pure (⟨name,s.isPublic,"import",path⟩ :: declarations)) s.declarations
    return {s with importing := false,importTokens := [],isPublic := false,staticPrefix := false,declarations,leading := []}
  if token == "}" then throw "unmatched source brace"
  if !s.kind.isEmpty && s.name.isEmpty then
    if !identifier token then throw "invalid declaration name"
    let declarations := if s.kind == "fn" || s.kind == "meaning" then
        ⟨token,s.isPublic,s.kind,[]⟩ :: s.declarations else s.declarations
    return {s with name := token,nameToken := some located,declarations}
  if token == "{" then
    if (s.kind == "enum" || s.kind == "struct") && s.name.isEmpty then
      throw "missing type name"
    return {s with depth := 1,body := [],openBrace := some located,locatedBody := []}
  if s.kind == "static-fn" && !s.name.isEmpty then
    if token == ";" then throw "static helper requires an expression body"
    return {s with header := token :: s.header}
  if token == ";" then return {s with kind := "",name := "",isPublic := false,staticPrefix := false,header := [],leading := [],nameToken := none}
  if token == "pub" then return {s with isPublic := true}
  if token == "static" && s.kind.isEmpty then return {s with staticPrefix := true}
  if token == "use" then return {s with importing := true,importTokens := []}
  if ["enum","struct","fn","meaning"].contains token then
    if s.staticPrefix && token != "fn" then throw "invalid static declaration category"
    return {s with kind := if s.staticPrefix then "static-fn" else token,name := "",nameToken := none,header := []}
  -- Only a brace may follow a fieldless enum/record name in this profile.
  if s.kind == "enum" || s.kind == "struct" then throw "unsupported type declaration header"
  return s

def sourceCatalogue (source : String) : Except String SourceCatalogue := do
  let s ← (← lexLocated source).foldlM item {}
  if s.depth != 0 || s.importing || s.kind == "enum" || s.kind == "struct" ||
      s.kind == "static-fn" || s.staticPrefix then
    throw "incomplete source declaration"
  return ⟨s.declarations.reverse,s.occurrences.reverse⟩

/-- Original import/type consumers share the same declaration scan. -/
def declarations (source : String) : Except String (List Declaration) :=
  (sourceCatalogue source).map SourceCatalogue.declarations

theorem sourceCatalogue_erases (source : String) :
    (sourceCatalogue source).map SourceCatalogue.declarations = declarations source := rfl

abbrev Sources := Array (String × String)

def originalBinding (sources : Sources) (moduleName name : String) : Except String (String × Declaration) := do
  let [(_,source)] := sources.toList.filter (fun entry => entry.1 == moduleName)
    | throw "missing/ambiguous original source module"
  let [decl] := (← declarations source).filter (fun decl => decl.name == name)
    | throw "missing/ambiguous original type declaration"
  return (source,decl)

private def path (tokens : List String) : Except String (List String) := do
  let (names,separator) ← tokens.foldlM (fun (names,separator) token => do
    if separator then
      if token != "::" then throw "unsupported source type expression"
      return (names,false)
    if !identifier token && !(names == ["std"] && ["basis","observe","classical"].contains token) then
      throw "unsupported source type expression"
    return (token :: names,true)) ([],false)
  if !separator then throw "incomplete source type path"
  return names.reverse

private def adapt {α : Type} (value : Except String α) : Finite.WorkM α :=
  Finite.lift (value.mapError fun _ => .request)

structure Resolved where
  moduleName : String
  source : String
  declaration : Declaration
  /-- Actual original lookups, in query-to-terminal order. Endpoint consumers
  retain their existing fields; a trace is not supplied by the caller. -/
  visited : List Semantics.SourceResolution.Binding

private def resolveBinding : Nat → Sources → String → String → String → Bool →
    List (String × String) → Finite.WorkM Resolved :=
  Nat.rec (fun _ _ _ _ _ _ => throw .limit) (fun _ recurse sources caller moduleName name localImports active => do
    Finite.exactWork (Exact.charge ((moduleName.utf8ByteSize+name.utf8ByteSize+1)*(active.length+1)))
    Finite.guard (!active.contains (moduleName,name)) .request
    -- Charge the lookup and retained binding/list cell before constructing
    -- either. Source strings and declarations are shared with that lookup.
    Finite.exactWork (Exact.charge ((sources.toList.map fun row =>
      row.1.utf8ByteSize+row.2.utf8ByteSize).sum+name.utf8ByteSize+moduleName.utf8ByteSize+3))
    let (source,decl) ← adapt (originalBinding sources moduleName name)
    if decl.kind != "import" then
      Finite.guard (decl.isPublic || moduleName == caller) .request
      return ⟨moduleName,source,decl,[⟨moduleName,source,decl⟩]⟩
    Finite.guard (decl.kind == "import" && (localImports || decl.isPublic)) .request
    -- Import bodies retain reversed original paths, not foreign target IDs.
    let target :: modules := decl.body | throw .request
    Finite.guard (target == decl.name && !modules.isEmpty) .request
    Finite.exactWork (Exact.charge ((decl.body.map String.utf8ByteSize).sum+decl.body.length+1))
    let owner := String.intercalate "::" modules.reverse
    let original ← recurse sources moduleName owner target false ((moduleName,name)::active)
    -- A public export requires an original public declaration, even if the
    -- importing module could otherwise see its own private declaration.
    Finite.guard (!decl.isPublic || original.declaration.isPublic) .request
    Finite.guard (original.declaration.isPublic || original.moduleName == caller) .request
    return {original with visited := ⟨moduleName,source,decl⟩ :: original.visited})

def resolveReference (sources : Sources) (caller : String) (tokens : List String) :
    Finite.WorkM Resolved := do
  let names ← adapt (path tokens)
  let some name := names.getLast? | throw .request
  let localName := names.length == 1
  let moduleName := if localName then caller else String.intercalate "::" names.dropLast
  -- An import retains its final spelling; a noncyclic chain cannot visit more
  -- modules than the already bounded original source table.
  resolveBinding sources.size sources caller moduleName name localName []


/-- Success of the existing error adapter retains the original result. -/
private theorem resolverAdapt_value {α : Type} (value : Except String α)
    (result : α) (work left : Nat)
    (ok : (adapt value).run work = (.ok result,left)) : value = .ok result := by
  have bound := (Finite.lift_success _ _ _ _ ok).1
  cases value <;> simp_all [Except.mapError]

private theorem resolverOriginalBinding_rows (sources : Sources) (moduleName name source : String)
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

/-- Actual recursive lookup retains its terminal original declaration. Caller
visibility is read from the final guard at each level, including import chains. -/
private theorem resolveBinding_facts (fuel : Nat) (sources : Sources)
    (caller moduleName name : String) (localImports : Bool)
    (active : List (String × String)) (result : Resolved) (work left : Nat)
    (ok : (resolveBinding fuel sources caller moduleName name localImports active).run work =
      (.ok result,left)) :
    (result.declaration.isPublic = true ∨ result.moduleName = caller) ∧
      originalBinding sources result.moduleName result.declaration.name =
        .ok (result.source,result.declaration) := by
  induction fuel generalizing sources caller moduleName name localImports active result work left with
  | zero => cases ok
  | succ fuel ih =>
    obtain ⟨_,w₁,_,h⟩ := Finite.bind_success _ _ _ _ _ ok
    obtain ⟨_,w₂,_,h⟩ := Finite.bind_success _ _ _ _ _ h
    obtain ⟨_,w₃,_,h⟩ := Finite.bind_success _ _ _ _ _ h
    obtain ⟨entry,w₄,original,h⟩ := Finite.bind_success _ _ _ _ _ h
    rcases entry with ⟨source,decl⟩
    have originalRead := resolverAdapt_value _ _ _ _ original
    -- Reduce the bound pair match and the early-return continuation before
    -- splitting the actual import condition; no resolver step is replaced.
    simp only [pure_bind] at h
    split at h
    · obtain ⟨_,w₅,visible,h⟩ := Finite.bind_success _ _ _ _ _ h
      have sameResult := (Finite.pure_success _ _ _ _ h).1
      subst result
      have permission := (Finite.guard_success _ _ _ _ visible).1
      have sameName := (resolverOriginalBinding_rows _ _ _ _ _ originalRead).2
      constructor
      · simpa only [Bool.or_eq_true_iff,beq_iff_eq] using permission
      · simpa only [sameName] using originalRead
    · obtain ⟨_,w₅,_,h⟩ := Finite.bind_success _ _ _ _ _ h
      cases body : decl.body with
      | nil =>
        simp only [body] at h
        cases h
      | cons target modules =>
        simp only [body] at h
        obtain ⟨_,w₆,_,h⟩ := Finite.bind_success _ _ _ _ _ h
        obtain ⟨_,w₇,_,h⟩ := Finite.bind_success _ _ _ _ _ h
        obtain ⟨resolved,w₈,recursive,h⟩ := Finite.bind_success _ _ _ _ _ h
        obtain ⟨_,w₉,_,h⟩ := Finite.bind_success _ _ _ _ _ h
        obtain ⟨_,w₁₀,visible,h⟩ := Finite.bind_success _ _ _ _ _ h
        have sameResult := (Finite.pure_success _ _ _ _ h).1
        subst result
        have provenance := ih sources moduleName
          (String.intercalate "::" modules.reverse) target false
          ((moduleName,name)::active) resolved w₇ w₈ recursive
        have permission := (Finite.guard_success _ _ _ _ visible).1
        exact ⟨by simpa only [Bool.or_eq_true_iff,beq_iff_eq] using permission,provenance.2⟩

/-- A successful executable reference lookup returns its exact canonical
original binding and satisfies the lookup's visibility guard for the supplied
caller. The caller argument is not authenticated to an original source site by
this theorem; it establishes neither field access nor source/native acceptance. -/
theorem resolveReference_facts (sources : Sources) (caller : String) (tokens : List String)
    (result : Resolved) (work left : Nat)
    (ok : (resolveReference sources caller tokens).run work = (.ok result,left)) :
    (result.declaration.isPublic = true ∨ result.moduleName = caller) ∧
      originalBinding sources result.moduleName result.declaration.name =
        .ok (result.source,result.declaration) := by
  unfold resolveReference at ok
  obtain ⟨names,w₁,_,h⟩ := Finite.bind_success _ _ _ _ _ ok
  cases last : names.getLast? with
  | none =>
    simp only [last] at h
    cases h
  | some name =>
    simp only [last] at h
    exact resolveBinding_facts _ _ _ _ _ _ _ _ _ _ h


/-! Resolution trace from the actual reader. OriginalLookups records exact
subordinate originalBinding computations in addition to the independent data
route; it is not a scanner/source-preservation theorem. Caller-site and original
import-envelope provenance remain separate obligations. -/

namespace ResolutionTrace

/-- Erase only checker packaging; retain canonical owner, original bytes and
all declaration data at each actual visited binding. -/
def resolvedView (resolved : Resolved) : Semantics.SourceResolution.Binding :=
  ⟨resolved.moduleName,resolved.source,resolved.declaration⟩

/-- Computational provenance, deliberately outside the independent semantics.
The route proof derives these facts from each actual original lookup. -/
def OriginalLookups (sources : Sources)
    (events : List Semantics.SourceResolution.Binding) : Prop :=
  ∀ entry, entry ∈ events →
    originalBinding sources entry.moduleName entry.declaration.name =
      .ok (entry.source,entry.declaration)

theorem originalBinding_data (sources : Sources) (moduleName name source : String)
    (decl : Declaration) (ok : originalBinding sources moduleName name = .ok (source,decl)) :
    Semantics.SourceResolution.LookupData sources moduleName name
      (resolvedView ⟨moduleName,source,decl,[]⟩) := by
  have facts := resolverOriginalBinding_rows sources moduleName name source decl ok
  exact ⟨rfl,facts.2,facts.1⟩

/-- The actual recursive resolver derives every route edge and original lookup;
there is no supplied resolution table or requested endpoint premise. -/
private theorem resolveBinding_route (fuel : Nat) (sources : Sources)
    (caller moduleName name : String) (localImports : Bool)
    (active : List (String × String)) (result : Resolved) (work left : Nat)
    (ok : (resolveBinding fuel sources caller moduleName name localImports active).run work =
      (.ok result,left)) :
    Semantics.SourceResolution.Route sources caller moduleName name localImports active
      result.visited (resolvedView result) ∧ OriginalLookups sources result.visited := by
  induction fuel generalizing sources caller moduleName name localImports active result work left with
  | zero => cases ok
  | succ fuel ih =>
    obtain ⟨_,w₁,_,h⟩ := Finite.bind_success _ _ _ _ _ ok
    obtain ⟨_,w₂,freshRead,h⟩ := Finite.bind_success _ _ _ _ _ h
    have fresh : (moduleName,name) ∉ active := by
      simpa using (Finite.guard_success _ _ _ _ freshRead).1
    obtain ⟨_,w₃,_,h⟩ := Finite.bind_success _ _ _ _ _ h
    obtain ⟨pair,w₄,original,h⟩ := Finite.bind_success _ _ _ _ _ h
    rcases pair with ⟨source,decl⟩
    have originalRead := resolverAdapt_value _ _ _ _ original
    have data := originalBinding_data sources moduleName name source decl originalRead
    have sameName : decl.name = name := data.nameExact
    let seen := resolvedView (⟨moduleName,source,decl,[]⟩ : Resolved)
    have seenLookup : originalBinding sources seen.moduleName seen.declaration.name =
        .ok (seen.source,seen.declaration) := by
      simpa only [seen,resolvedView,sameName] using originalRead
    simp only [pure_bind] at h
    split at h
    · rename_i terminal
      obtain ⟨_,w₅,visibleRead,h⟩ := Finite.bind_success _ _ _ _ _ h
      have sameResult := (Finite.pure_success _ _ _ _ h).1
      subst result
      have permission : decl.isPublic = true ∨ moduleName = caller := by
        simpa only [Bool.or_eq_true_iff,beq_iff_eq] using
          (Finite.guard_success _ _ _ _ visibleRead).1
      have notImport : decl.kind ≠ "import" := by
        simpa only [bne_iff_ne] using terminal
      refine ⟨?_,?_⟩
      · exact .direct caller moduleName name localImports active seen fresh data notImport permission
      · intro entry present
        have same : entry = seen := by simpa only [List.mem_singleton] using present
        subst entry
        exact seenLookup
    · obtain ⟨_,w₅,importRead,h⟩ := Finite.bind_success _ _ _ _ _ h
      have importFacts : decl.kind = "import" ∧
          (localImports = true ∨ decl.isPublic = true) := by
        simpa only [Bool.and_eq_true_iff,Bool.or_eq_true_iff,beq_iff_eq] using
          (Finite.guard_success _ _ _ _ importRead).1
      cases body : decl.body with
      | nil =>
        simp only [body] at h
        cases h
      | cons target modules =>
        simp only [body] at h
        obtain ⟨_,w₆,pathRead,h⟩ := Finite.bind_success _ _ _ _ _ h
        have spelling : target = decl.name ∧ modules ≠ [] := by
          simpa using (Finite.guard_success _ _ _ _ pathRead).1
        obtain ⟨_,w₇,_,h⟩ := Finite.bind_success _ _ _ _ _ h
        obtain ⟨resolved,w₈,recursive,h⟩ := Finite.bind_success _ _ _ _ _ h
        obtain ⟨_,w₉,exportRead,h⟩ := Finite.bind_success _ _ _ _ _ h
        obtain ⟨_,w₁₀,visibleRead,h⟩ := Finite.bind_success _ _ _ _ _ h
        have sameResult := (Finite.pure_success _ _ _ _ h).1
        subst result
        obtain ⟨route,lookups⟩ := ih sources moduleName
          (String.intercalate "::" modules.reverse) target false
          ((moduleName,name)::active) resolved w₇ w₈ recursive
        have publicExport : decl.isPublic = true → resolved.declaration.isPublic = true := by
          intro exported
          simpa only [exported,Bool.not_true,Bool.false_or] using
            (Finite.guard_success _ _ _ _ exportRead).1
        have callerVisible : resolved.declaration.isPublic = true ∨ resolved.moduleName = caller := by
          simpa only [Bool.or_eq_true_iff,beq_iff_eq] using
            (Finite.guard_success _ _ _ _ visibleRead).1
        refine ⟨?_,?_⟩
        · exact .throughImport caller moduleName name localImports active seen target modules
            resolved.visited (resolvedView resolved) fresh data importFacts.1 importFacts.2 body
            spelling.1 spelling.2 route publicExport callerVisible
        · intro entry present
          rcases List.mem_cons.mp present with same | member
          · subst entry
            exact seenLookup
          · exact lookups entry member

/-- The wrapper retains the actual supplied query's path parse, final name and
owner-selection expression together with the derived complete import route.
The independent Query theorem additionally needs path_spelling. -/
theorem resolveReference_retained_trace (sources : Sources) (caller : String) (tokens : List String)
    (result : Resolved) (work left : Nat)
    (ok : (resolveReference sources caller tokens).run work = (.ok result,left)) :
    ∃ (names : List String) (name : String),
      path tokens = .ok names ∧ names.getLast? = some name ∧
      Semantics.SourceResolution.Route sources caller
        (if names.length == 1 then caller else String.intercalate "::" names.dropLast)
        name (names.length == 1) [] result.visited (resolvedView result) ∧
      OriginalLookups sources result.visited := by
  unfold resolveReference at ok
  obtain ⟨names,w₁,pathRead,h⟩ := Finite.bind_success _ _ _ _ _ ok
  have parsed := resolverAdapt_value _ _ _ _ pathRead
  cases last : names.getLast? with
  | none =>
    simp only [last] at h
    cases h
  | some name =>
    simp only [last] at h
    obtain ⟨route,lookups⟩ := resolveBinding_route _ _ _ _ _ _ _ _ _ _ h
    exact ⟨names,name,parsed,last,route,lookups⟩

/-- Compatibility form of the route theorem. The existential witness is the
actual returned trace, rather than a separately reconstructed path. -/
theorem resolveReference_trace (sources : Sources) (caller : String) (tokens : List String)
    (result : Resolved) (work left : Nat)
    (ok : (resolveReference sources caller tokens).run work = (.ok result,left)) :
    ∃ (names : List String) (name : String) (events : List Semantics.SourceResolution.Binding),
      path tokens = .ok names ∧ names.getLast? = some name ∧
      Semantics.SourceResolution.Route sources caller
        (if names.length == 1 then caller else String.intercalate "::" names.dropLast)
        name (names.length == 1) [] events (resolvedView result) ∧
      OriginalLookups sources events := by
  obtain ⟨names,name,parsed,last,route,lookups⟩ :=
    resolveReference_retained_trace sources caller tokens result work left ok
  exact ⟨names,name,result.visited,parsed,last,route,lookups⟩

end ResolutionTrace

/-! Exact supplied-query spelling. The formatter below is proof-only data
reconstruction of the existing path accumulator, not another parser. All lexical
branches remain those of the actual private path definition. The conclusion
states token alternation and owner selection, not lexical adequacy or source-site
authentication. -/

namespace ResolutionTrace

private def pathPrefix (state : List String × Bool) : List String :=
  state.1.reverse.intersperse "::" ++
    if state.2 || state.1.isEmpty then [] else ["::"]

private def PathReady (state : List String × Bool) : Prop :=
  state.2 = true → state.1 ≠ []

private theorem intersperse_append_single (separator value : String) :
    ∀ (items : List String), items ≠ [] →
      (items ++ [value]).intersperse separator = items.intersperse separator ++ [separator,value] := by
  intro items
  induction items with
  | nil =>
    intro nonempty
    exact False.elim (nonempty rfl)
  | cons first rest ih =>
    intro _
    cases rest with
    | nil => rfl
    | cons second rest =>
      simp only [List.cons_append,List.intersperse_cons_cons]
      simpa only [List.cons_append] using
        congrArg (fun tail => first :: separator :: tail) (ih (by simp))

/-- A fold calculation used only after deriving advance from the actual parser
step. The public query theorem supplies no transition-faithfulness premise. -/
private theorem path_fold_accumulate
    (step : (List String × Bool) → String → Except String (List String × Bool))
    (advance : ∀ before token after, PathReady before → step before token = .ok after →
      PathReady after ∧ pathPrefix after = pathPrefix before ++ [token])
    (tokens : List String) (before after : List String × Bool)
    (ready : PathReady before) (ok : tokens.foldlM step before = .ok after) :
    PathReady after ∧ pathPrefix after = pathPrefix before ++ tokens := by
  induction tokens generalizing before with
  | nil =>
    change (Except.ok before : Except String (List String × Bool)) = .ok after at ok
    cases ok
    exact ⟨ready,by simp⟩
  | cons token tokens ih =>
    simp only [List.foldlM_cons] at ok
    cases next : step before token with
    | error error =>
      simp only [next,bind,Except.bind] at ok
      cases ok
    | ok middle =>
      have continued : tokens.foldlM step middle = .ok after := by
        simpa only [next,bind,Except.bind] using ok
      obtain ⟨middleReady,first⟩ := advance before token middle ready next
      obtain ⟨afterReady,rest⟩ := ih middle middleReady continued
      refine ⟨afterReady,?_⟩
      rw [rest,first]
      simp only [List.append_assoc,List.singleton_append]

private theorem path_spelling (tokens names : List String)
    (ok : path tokens = .ok names) : tokens = names.intersperse "::" ∧ names ≠ [] := by
  -- This is definitionally the existing path fold's lambda, retained locally
  -- only so the proof can name its successful transitions.
  let step : (List String × Bool) → String → Except String (List String × Bool) :=
    fun (names,separator) token => do
      if separator then
        if token != "::" then throw "unsupported source type expression"
        return (names,false)
      if !identifier token && !(names == ["std"] && ["basis","observe","classical"].contains token) then
        throw "unsupported source type expression"
      return (token :: names,true)
  have advance : ∀ before token after, PathReady before → step before token = .ok after →
      PathReady after ∧ pathPrefix after = pathPrefix before ++ [token] := by
    intro before token after ready accepted
    rcases before with ⟨reverseNames,separator⟩
    cases separator with
    | false =>
      change (if !identifier token &&
          !(reverseNames == ["std"] && ["basis","observe","classical"].contains token)
        then Except.error "unsupported source type expression"
        else Except.ok (token :: reverseNames,true)) = .ok after at accepted
      split at accepted
      · cases accepted
      · have same : (token :: reverseNames,true) = after := by
          simpa only [Except.ok.injEq] using accepted
        subst after
        constructor
        · intro _
          exact List.cons_ne_nil _ _
        · by_cases empty : reverseNames = []
          · subst reverseNames
            rfl
          · have encoded := intersperse_append_single "::" token reverseNames.reverse
              (by simpa using empty)
            simpa [pathPrefix,empty,List.reverse_cons,List.append_assoc] using encoded
    | true =>
      change (if token != "::" then Except.error "unsupported source type expression"
        else Except.ok (reverseNames,false)) = .ok after at accepted
      by_cases spelling : token = "::"
      · subst token
        have same : (reverseNames,false) = after := by simpa using accepted
        subst after
        constructor
        · intro impossible
          cases impossible
        · have nonempty : reverseNames ≠ [] := ready rfl
          simp [pathPrefix,nonempty]
      · simp [spelling] at accepted
  change (do
    let (reverseNames,separator) ← tokens.foldlM step ([],false)
    if !separator then throw "incomplete source type path"
    return reverseNames.reverse) = .ok names at ok
  cases folded : tokens.foldlM step ([],false) with
  | error error =>
    simp only [folded,bind,Except.bind] at ok
    cases ok
  | ok finalState =>
    rcases finalState with ⟨reverseNames,separator⟩
    have initialReady : PathReady ([],false) := by
      intro impossible
      cases impossible
    have reconstructed := path_fold_accumulate step advance tokens ([],false)
      (reverseNames,separator) initialReady folded
    simp only [folded,bind,Except.bind] at ok
    cases separator with
    | false => cases ok
    | true =>
      have same : reverseNames.reverse = names := by
        change (Except.ok reverseNames.reverse : Except String (List String)) = .ok names at ok
        exact Except.ok.inj ok
      have encoded : reverseNames.reverse.intersperse "::" = tokens := by
        simpa [pathPrefix] using reconstructed.2
      constructor
      · simpa only [same] using encoded.symm
      · have nonempty : reverseNames ≠ [] := reconstructed.1 rfl
        rw [← same]
        simpa using nonempty

/-- Actual reference resolution retains the independent exact token query and
its complete returned import route, plus each original lookup. No desired
endpoint, faithful source environment or supplied parse is a premise. -/
theorem resolveReference_retained_query (sources : Sources) (caller : String) (tokens : List String)
    (result : Resolved) (work left : Nat)
    (ok : (resolveReference sources caller tokens).run work = (.ok result,left)) :
    Semantics.SourceResolution.Query sources caller tokens result.visited (resolvedView result) ∧
      OriginalLookups sources result.visited := by
  obtain ⟨names,name,parsed,last,route,lookups⟩ :=
    resolveReference_retained_trace sources caller tokens result work left ok
  have spelling := path_spelling tokens names parsed
  obtain ⟨modules,namesExact⟩ := List.getLast?_eq_some_iff.mp last
  subst names
  refine ⟨?_,lookups⟩
  rw [spelling.1]
  cases modules with
  | nil =>
    have localRoute : Semantics.SourceResolution.Route sources caller caller name true []
        result.visited (resolvedView result) := by simpa using route
    exact .localName name result.visited (resolvedView result) localRoute
  | cons owner modules =>
    have notSingle : (((owner :: modules) ++ [name]).length == 1) = false := by
      apply beq_eq_false_iff_ne.mpr
      simp only [List.length_append,List.length_cons]
      omega
    have qualifiedRoute : Semantics.SourceResolution.Route sources caller
        (String.intercalate "::" (owner :: modules)) name false [] result.visited (resolvedView result) := by
      simpa only [notSingle, Bool.false_eq_true, if_false, List.dropLast_concat] using route
    exact .qualifiedName (owner :: modules) name result.visited (resolvedView result)
      (List.cons_ne_nil _ _) qualifiedRoute

/-- Existing endpoint theorem, witnessed by the actual returned trace. -/
theorem resolveReference_query (sources : Sources) (caller : String) (tokens : List String)
    (result : Resolved) (work left : Nat)
    (ok : (resolveReference sources caller tokens).run work = (.ok result,left)) :
    ∃ events, Semantics.SourceResolution.Query sources caller tokens events (resolvedView result) ∧
      OriginalLookups sources events :=
  ⟨result.visited,resolveReference_retained_query sources caller tokens result work left ok⟩

/-- The located adapter retains the exact supplied tokens. Their spans/caller
still require the original function-parser provenance theorem. -/
theorem resolveLocatedReference_query (sources : Sources) (caller : String)
    (tokens : List LocatedToken) (result : Resolved) (work left : Nat)
    (ok : (resolveReference sources caller (tokens.map (·.text))).run work = (.ok result,left)) :
    ∃ events, Semantics.SourceResolution.LocatedQuery sources caller tokens events (resolvedView result) ∧
      OriginalLookups sources events := by
  exact resolveReference_query sources caller (tokens.map LocatedToken.text) result work left ok

end ResolutionTrace

end QleisliKernel.SourceTypes
