import QleisliKernel.SourceTypes.Imports
import QleisliKernel.FiniteCarrier

/-! Reconstruct a nominal carrier from original top-level source declarations.
The independent reader preserves canonical declarations through explicit imports
and public reexports. General Nat expressions still refuse until their reader
is supplied. It grants neither source-body preservation nor a new guarantee.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes
open Semantics.FiniteCarrier

structure Declaration where
  name : String
  isPublic : Bool
  kind : String
  body : List String
  deriving BEq, DecidableEq, Repr

private structure Items where
  depth : Nat := 0
  isPublic : Bool := false
  kind : String := ""
  name : String := ""
  body : List String := []
  declarations : List Declaration := []
  importing : Bool := false
  importTokens : List String := []

private def item (s : Items) (token : String) : Except String Items := do
  if s.depth > 0 then
    if token == "{" then return {s with depth := s.depth+1,body := token :: s.body}
    if token == "}" then
      if s.depth == 1 then
        let declarations := if s.kind == "enum" || s.kind == "struct" then
            ⟨s.name,s.isPublic,s.kind,s.body.reverse⟩ :: s.declarations else s.declarations
        return {s with depth := 0,isPublic := false,kind := "",name := "",body := [],declarations}
      return {s with depth := s.depth-1,body := token :: s.body}
    return {s with body := if s.kind.isEmpty then [] else token :: s.body}
  if s.importing then
    if token != ";" then return {s with importTokens := token :: s.importTokens}
    let paths ← Imports.read s.importTokens.reverse
    let declarations ← paths.foldlM (fun declarations path => do
      let name :: _ := path | throw "empty import path"
      pure (⟨name,s.isPublic,"import",path⟩ :: declarations)) s.declarations
    return {s with importing := false,importTokens := [],isPublic := false,declarations}
  if token == "}" then throw "unmatched source brace"
  if !s.kind.isEmpty && s.name.isEmpty then
    if !identifier token then throw "invalid declaration name"
    let declarations := if s.kind == "fn" || s.kind == "meaning" then
        ⟨token,s.isPublic,s.kind,[]⟩ :: s.declarations else s.declarations
    return {s with name := token,declarations}
  if token == "{" then
    if (s.kind == "enum" || s.kind == "struct") && s.name.isEmpty then
      throw "missing type name"
    return {s with depth := 1,body := []}
  if token == ";" then return {s with kind := "",name := "",isPublic := false}
  if token == "pub" then return {s with isPublic := true}
  if token == "use" then return {s with importing := true,importTokens := []}
  if ["enum","struct","fn","meaning"].contains token then
    return {s with kind := token,name := ""}
  -- Only a brace may follow a fieldless enum/record name in this profile.
  if s.kind == "enum" || s.kind == "struct" then throw "unsupported type declaration header"
  return s

def declarations (source : String) : Except String (List Declaration) := do
  let s ← (← lex source).foldlM item {}
  if s.depth != 0 || s.importing || s.kind == "enum" || s.kind == "struct" then
    throw "incomplete source declaration"
  return s.declarations.reverse

private structure Parts where
  stack : List String := []
  current : List String := []
  parts : List (List String) := []

private def part (s : Parts) (token : String) : Except String Parts := do
  if token == "(" || token == "<" then
    return {s with stack := (if token == "(" then ")" else ">") :: s.stack,current := token :: s.current}
  if token == ")" || token == ">" then
    let expected :: rest := s.stack | throw "unmatched type delimiter"
    if token != expected then throw "mismatched type delimiter"
    return {s with stack := rest,current := token :: s.current}
  if token == "," && s.stack.isEmpty then
    if s.current.isEmpty then throw "empty member"
    return {s with current := [],parts := s.current.reverse :: s.parts}
  return {s with current := token :: s.current}

def splitMembers (tokens : List String) : Except String (List (List String)) := do
  let s ← tokens.foldlM part {}
  if !s.stack.isEmpty then throw "incomplete member type"
  return (if s.current.isEmpty then s.parts else s.current.reverse :: s.parts).reverse

abbrev Sources := Array (String × String)

private def binding (sources : Sources) (moduleName name : String) : Except String (String × Declaration) := do
  let [(_,source)] := sources.toList.filter (fun entry => entry.1 == moduleName)
    | throw "missing/ambiguous original source module"
  let [decl] := (← declarations source).filter (fun decl => decl.name == name)
    | throw "missing/ambiguous original type declaration"
  return (source,decl)

/-- Origin lookup is canonical: an alias never becomes a new declaration. -/
def lookup (sources : Sources) (moduleName name : String) : Except String (String × Declaration) := do
  let (source,decl) ← binding sources moduleName name
  if decl.kind != "enum" && decl.kind != "struct" then throw "source name is not a finite type"
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

private structure Readers where
  ty : Sources → String → List String → Finite.WorkM Basis
  decl : Sources → String → String → Finite.WorkM Basis

private def adapt {α : Type} (value : Except String α) : Finite.WorkM α :=
  Finite.lift (value.mapError fun _ => .request)

private def load (sources : Sources) (moduleName name : String) : Finite.WorkM (String × Declaration) := do
  Finite.exactWork (Exact.charge ((sources.toList.map fun row =>
    row.1.utf8ByteSize + row.2.utf8ByteSize).sum + name.utf8ByteSize + moduleName.utf8ByteSize + 1))
  adapt (lookup sources moduleName name)

private structure Resolved where
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
    let (source,decl) ← adapt (binding sources moduleName name)
    if decl.kind == "enum" || decl.kind == "struct" then
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

private def resolveReference (sources : Sources) (caller : String) (tokens : List String) :
    Finite.WorkM Resolved := do
  let names ← adapt (path tokens)
  let some name := names.getLast? | throw .request
  let localName := names.length == 1
  let moduleName := if localName then caller else String.intercalate "::" names.dropLast
  -- An import retains its final spelling; a noncyclic chain cannot visit more
  -- modules than the already bounded original source table.
  resolveBinding sources.size sources caller moduleName name localName []

private def combine (first second : Basis) : Finite.WorkM Basis := do
  Finite.guard (first.length + second.length ≤ 128) .limit
  pure (first ++ second)

/-- Direct decimal reading for the existing zero-to-six width profile. Bound
every prefix before extending it; leading zeroes retain their ordinary meaning.
This introduces no general Nat-expression or const-value language. -/
def literalWidth (literal : String) : Finite.WorkM Nat := do
  Finite.guard (!literal.isEmpty) .request
  Finite.exactWork (Exact.charge (literal.utf8ByteSize + 1))
  literal.toList.foldlM (fun value char => do
    Finite.guard ('0' ≤ char && char ≤ '9') .request
    let width := value * 10 + (char.toNat - '0'.toNat)
    Finite.guard (width ≤ 6) .limit
    pure width) 0

private def readers : Nat → Readers :=
  Nat.rec ⟨fun _ _ _ => throw .limit,fun _ _ _ => throw .limit⟩
    (fun _ recurse => ⟨fun sources current tokens => do
      match tokens with
      | ["Unit"] => return [.unit]
      | ["Bit"] => return [.bit]
      | ["Bits","<",width,">"] =>
        return [.bits (← literalWidth width)]
      | "(" :: rest =>
        if rest.getLast? != some ")" || rest.dropLast.getLast? == some "," then
          throw .request
        let parts ← adapt (splitMembers rest.dropLast)
        Finite.guard (2 ≤ parts.length && parts.length ≤ 64) .limit
        let children ← parts.foldlM (fun acc part => do combine acc (← recurse.ty sources current part)) []
        combine [if parts.length == 2 then Atom.pair else .tuple parts.length] children
      | _ =>
        let original ← resolveReference sources current tokens
        recurse.decl sources original.moduleName original.declaration.name,
      fun sources moduleName name => do
        let (source,decl) ← load sources moduleName name
        let origin : Origin := ⟨moduleName,name,source⟩
        let members ← adapt (splitMembers decl.body)
        Finite.guard (members.length ≤ 64) .limit
        if decl.kind == "enum" then
          let names ← members.mapM fun tokens => do
            let [name] := tokens | throw .request
            Finite.guard (identifier name) .request
            return name
          Finite.guard (!names.isEmpty && FiniteCarrier.namesValid names) .request
          return [.enumeration origin names]
        let (names,children) ← members.foldlM (fun (names,children) tokens => do
          let tokens := if tokens.head? == some "pub" then tokens.drop 1 else tokens
          let field :: ":" :: ty := tokens | throw .request
          Finite.guard (identifier field) .request
          return (names ++ [field],← combine children (← recurse.ty sources moduleName ty))) ([],[])
        Finite.guard (FiniteCarrier.namesValid names) .request
        combine [.record origin names] children⟩)

/-- Reconstruct from actual source, never by finding a matching producer row.
The existing carrier reader separately bounds the complete tree/code. -/
def nominal (sources : Sources) (origin : Origin) (nodes : Nat := 128) : Finite.WorkM Basis := do
  let (source,_) ← load sources origin.moduleName origin.declarationName
  Finite.exactWork (Exact.charge (origin.source.utf8ByteSize + 1))
  Finite.guard (source == origin.source) .request
  -- A matching subtree cannot contain more nodes than the supplied complete
  -- tree. Two reader steps per node suffice; the existing depth ceiling remains.
  (readers (min 65 (2*nodes+1))).decl sources origin.moduleName origin.declarationName

private def checkAtom (sources : Sources) (nodes : Nat) (remaining : Basis) (atom : Atom) :
    Finite.WorkM Basis := do
  match atom with
  | .enumeration origin _ | .record origin _ =>
    let original ← nominal sources origin nodes
    Finite.guard (remaining.take original.length == original) .request
  | _ => pure ()
  pure (remaining.drop 1)

/-- Compare every nominal subtree to its independently reconstructed source
tree. Prefix validation occurs first, so a neighbour cannot supply missing nodes. -/
def check (sources : Sources) (basis : Basis) : Finite.WorkM Unit := do
  Finite.guard (sources.size ≤ 128 && (sources.toList.map fun row =>
    row.1.utf8ByteSize + row.2.utf8ByteSize).sum ≤ 1048576) .limit
  let _ ← FiniteCarrier.read basis
  let _ ← basis.foldlM (checkAtom sources basis.length) basis
  pure ()

private theorem adapt_value {α : Type} (value : Except String α) (result : α) (work left : Nat)
    (ok : (adapt value).run work = (.ok result,left)) : value = .ok result := by
  have bound := (Finite.lift_success _ _ _ _ ok).1
  cases value <;> simp_all [Except.mapError]

private theorem load_value (sources : Sources) (moduleName name : String)
    (result : String × Declaration) (work left : Nat)
    (ok : (load sources moduleName name).run work = (.ok result,left)) :
    lookup sources moduleName name = .ok result := by
  obtain ⟨_,middle,_,bound⟩ := Finite.bind_success _ _ _ _ _ ok
  exact adapt_value _ _ _ _ bound

/-- Success names the original module/declaration lookup and exact source
bytes. It does not assert that the function body has its source meaning. -/
theorem nominal_original (sources : Sources) (origin : Origin) (nodes : Nat)
    (result : Basis) (work left : Nat)
    (ok : (nominal sources origin nodes).run work = (.ok result,left)) :
    ∃ decl, lookup sources origin.moduleName origin.declarationName = .ok (origin.source,decl) := by
  obtain ⟨entry,a,loaded,h⟩ := Finite.bind_success _ _ _ _ _ ok
  obtain ⟨_,b,_,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨_,c,same,_⟩ := Finite.bind_success _ _ _ _ _ h
  have equal := beq_iff_eq.mp (Finite.guard_success _ _ _ _ same).1
  refine ⟨entry.2,?_⟩
  have sameEntry : (origin.source,entry.2) = entry := by
    apply Prod.ext
    · exact equal.symm
    · rfl
  rw [sameEntry]
  exact load_value _ _ _ _ _ _ loaded

/-- Literal source-declaration identity only, not source-function correctness. -/
def OriginalDeclaration (sources : Sources) : Atom → Prop
  | .enumeration origin _ | .record origin _ =>
    ∃ decl, lookup sources origin.moduleName origin.declarationName = .ok (origin.source,decl)
  | _ => True

private theorem checkAtom_original (sources : Sources) (nodes : Nat) (remaining : Basis)
    (atom : Atom) (result : Basis) (work left : Nat)
    (ok : (checkAtom sources nodes remaining atom).run work = (.ok result,left)) :
    OriginalDeclaration sources atom := by
  cases atom <;> try trivial
  all_goals
    obtain ⟨original,after,read,_⟩ := Finite.bind_success _ _ _ _ _ ok
    exact nominal_original _ _ _ _ _ _ read

private theorem fold_original (sources : Sources) (nodes : Nat) (atoms remaining result : Basis)
    (work left : Nat)
    (ok : (atoms.foldlM (checkAtom sources nodes) remaining).run work = (.ok result,left)) :
    ∀ atom ∈ atoms, OriginalDeclaration sources atom := by
  induction atoms generalizing remaining work with
  | nil => simp
  | cons first rest ih =>
    simp only [List.foldlM_cons] at ok
    obtain ⟨next,after,head,tail⟩ := Finite.bind_success _ _ _ _ _ ok
    intro atom member
    rcases List.mem_cons.mp member with same | member
    · subst atom
      exact checkAtom_original _ _ _ _ _ _ _ head
    · exact ih next after tail atom member

theorem check_original_declarations (sources : Sources) (basis : Basis) (work left : Nat)
    (ok : (check sources basis).run work = (.ok (),left)) :
    ∀ atom ∈ basis, OriginalDeclaration sources atom := by
  obtain ⟨_,a,_,h⟩ := Finite.bind_success _ _ _ _ _ ok
  obtain ⟨_,b,_,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨remaining,c,fold,_⟩ := Finite.bind_success _ _ _ _ _ h
  exact fold_original sources basis.length basis basis remaining b c fold

end QleisliKernel.SourceTypes
