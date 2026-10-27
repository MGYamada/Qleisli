import QleisliKernel.Semantics.SourceSyntax

/-! Independent query/import-route data over original declarations. No checker
call, accepted handle or success bit defines these relations. The executable
resolver separately derives its route and every original lookup from success.
Original source parsing and caller-site authentication remain further duties.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Semantics.SourceResolution
open SourceTypes

abbrev SourceRows := Array (String × String)
abbrev Key := String × String

structure Binding where
  moduleName : String
  source : String
  declaration : Declaration

/-- Only data-level identity/uniqueness. Declaration extraction is deliberately
not asserted by a predicate that merely recognizes checker success. -/
structure LookupData (sources : SourceRows) (owner name : String)
    (entry : Binding) : Prop where
  ownerExact : entry.moduleName = owner
  nameExact : entry.declaration.name = name
  uniqueSource : sources.toList.filter (fun row => row.1 == owner) = [(owner,entry.source)]

/-- Preserve every visited alias and terminal binding, in order. Both the caller
used by each recursive step and the caller-visible terminal result are explicit. -/
inductive Route (sources : SourceRows) :
    String → String → String → Bool → List Key → List Binding → Binding → Prop
  | direct (caller owner name : String) (localImports : Bool)
      (active : List Key) (entry : Binding)
      (fresh : (owner,name) ∉ active)
      (lookup : LookupData sources owner name entry)
      (terminal : entry.declaration.kind ≠ "import")
      (visible : entry.declaration.isPublic = true ∨ owner = caller) :
      Route sources caller owner name localImports active [entry] entry
  | throughImport (caller owner name : String) (localImports : Bool)
      (active : List Key) (entry : Binding) (target : String) (modules : List String)
      (rest : List Binding) (result : Binding)
      (fresh : (owner,name) ∉ active)
      (lookup : LookupData sources owner name entry)
      (importKind : entry.declaration.kind = "import")
      (importVisible : localImports = true ∨ entry.declaration.isPublic = true)
      (reversePath : entry.declaration.body = target :: modules)
      (boundSpelling : target = entry.declaration.name)
      (qualified : modules ≠ [])
      (next : Route sources owner (String.intercalate "::" modules.reverse) target
        false ((owner,name) :: active) rest result)
      (publicExport : entry.declaration.isPublic = true → result.declaration.isPublic = true)
      (callerVisible : result.declaration.isPublic = true ∨ result.moduleName = caller) :
      Route sources caller owner name localImports active (entry :: rest) result

/-- Exact token spelling and owner selection of the actual reference query.
Identifier validity is a separate lexical/parser obligation, not silently
assumed from endpoint identity. Qualified paths contain at least one module. -/
inductive Query (sources : SourceRows) (caller : String) :
    List String → List Binding → Binding → Prop
  | localName (name : String) (events : List Binding) (result : Binding)
      (route : Route sources caller caller name true [] events result) :
      Query sources caller [name] events result
  | qualifiedName (modules : List String) (name : String)
      (events : List Binding) (result : Binding) (nonempty : modules ≠ [])
      (route : Route sources caller (String.intercalate "::" modules) name
        false [] events result) :
      Query sources caller (List.intersperse "::" (modules ++ [name])) events result

/-- Retain the complete supplied located query at the adapter boundary. This
asserts text correspondence, not authentication of the spans to a caller body. -/
def LocatedQuery (sources : SourceRows) (caller : String) (tokens : List LocatedToken)
    (events : List Binding) (result : Binding) : Prop :=
  Query sources caller (tokens.map (·.text)) events result

end QleisliKernel.Semantics.SourceResolution
