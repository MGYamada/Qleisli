import QleisliKernel.SourceTypes.Imports
import QleisliKernel.Finite

/-! Original declaration bodies and canonical module bindings. A category is
checked after resolution; imports cannot change its origin or visibility.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes

structure Declaration where
  name : String
  isPublic : Bool
  kind : String
  body : List String
  deriving BEq, DecidableEq, Repr

deriving instance ReflBEq, LawfulBEq for Declaration

/-- A brace body found by the shared declaration scanner. The complete header
and inner tokens retain original locations. A function envelope is syntax data,
not proof that its header/body is well-typed or that it authorizes a caller. -/
structure BodyOccurrence where
  declaration : Declaration
  nameToken : LocatedToken
  header : List LocatedToken
  openBrace : LocatedToken
  body : List LocatedToken
  closeBrace : LocatedToken
  deriving BEq, DecidableEq, Repr

structure SourceCatalogue where
  declarations : List Declaration
  bodies : List BodyOccurrence
  deriving BEq, DecidableEq, Repr

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

private def resolveBinding : Nat → Sources → String → String → String → Bool →
    List (String × String) → Finite.WorkM Resolved :=
  Nat.rec (fun _ _ _ _ _ _ => throw .limit) (fun _ recurse sources caller moduleName name localImports active => do
    Finite.exactWork (Exact.charge ((moduleName.utf8ByteSize+name.utf8ByteSize+1)*(active.length+1)))
    Finite.guard (!active.contains (moduleName,name)) .request
    Finite.exactWork (Exact.charge ((sources.toList.map fun row =>
      row.1.utf8ByteSize+row.2.utf8ByteSize).sum+name.utf8ByteSize+moduleName.utf8ByteSize+1))
    let (source,decl) ← adapt (originalBinding sources moduleName name)
    if decl.kind != "import" then
      Finite.guard (decl.isPublic || moduleName == caller) .request
      return ⟨moduleName,source,decl⟩
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
    return original)

def resolveReference (sources : Sources) (caller : String) (tokens : List String) :
    Finite.WorkM Resolved := do
  let names ← adapt (path tokens)
  let some name := names.getLast? | throw .request
  let localName := names.length == 1
  let moduleName := if localName then caller else String.intercalate "::" names.dropLast
  -- An import retains its final spelling; a noncyclic chain cannot visit more
  -- modules than the already bounded original source table.
  resolveBinding sources.size sources caller moduleName name localName []

end QleisliKernel.SourceTypes
