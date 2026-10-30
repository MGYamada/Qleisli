import QleisliKernel.SourceTypes.NaturalHeaders

/-! Original Nat helpers and their complete acyclic dependency graph. Every
private/unused helper is visited. This catalogue grants no generic body validity;
normalization and source-to-meaning obligations remain separate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.NaturalCatalog
open Semantics.SourceNatural
abbrev WorkM := Finite.WorkM

structure Key where
  moduleName : String
  declarationName : String
  deriving BEq, DecidableEq, Repr

structure Original where
  key : Key
  source : String
  declaration : Declaration
  helper : NaturalHeaders.Helper
  calls : List (Path × Key) := []

private def adapt {α : Type} (result : Except String α) : WorkM α :=
  Finite.lift (result.mapError fun _ => .request)

private def keyCells (key : Key) : Nat :=
  key.moduleName.utf8ByteSize+key.declarationName.utf8ByteSize+1

private def gather (sources : Sources) : WorkM (List Original) := do
  let (_,helpers) ← sources.toList.foldlM (fun (modules,helpers) (moduleName,source) => do
    Finite.exactWork (Exact.charge ((moduleName.utf8ByteSize+1)*(modules.length+1)+source.utf8ByteSize+1))
    Finite.guard (!modules.contains moduleName) .request
    let declarations ← adapt (SourceTypes.declarations source)
    let (_,helpers) ← declarations.foldlM (fun (names,helpers) declaration => do
      Finite.exactWork (Exact.charge ((declaration.name.utf8ByteSize+1)*(names.length+1)))
      Finite.guard (!names.contains declaration.name) .request
      if declaration.kind != "static-fn" then return (declaration.name :: names,helpers)
      let helper ← adapt (NaturalHeaders.read declaration)
      let original : Original := ⟨⟨moduleName,declaration.name⟩,source,declaration,helper,[]⟩
      return (declaration.name :: names,original :: helpers)) (([] : List String),helpers)
    return (moduleName :: modules,helpers)) (([] : List String),([] : List Original))
  return helpers.reverse

private structure Caller where
  moduleName : String
  parameters : List String

private def resolve (sources : Sources) (caller : Caller) (path : Path) : WorkM Key := do
  Finite.exactWork (Exact.charge ((path.map String.utf8ByteSize).sum+path.length+1))
  if let [name] := path then
    Finite.exactWork (Exact.charge ((name.utf8ByteSize+1)*(caller.parameters.length+1)))
    Finite.guard (!caller.parameters.contains name) .request
  let target ← resolveReference sources caller.moduleName (List.intersperse "::" path)
  Finite.guard (target.declaration.kind == "static-fn") .request
  return ⟨target.moduleName,target.declaration.name⟩

private def scan : Nat → Sources → List Original → Caller → List Expr →
    List (Path × Key) → WorkM (List (Path × Key)) :=
  Nat.rec (fun _ _ _ pending calls =>
      if pending.isEmpty then pure calls else throw .limit)
    (fun _ recurse sources catalog caller pending calls => do
      Finite.exactWork (Exact.charge 1)
      match pending with
      | [] => return calls
      | expression :: rest =>
        match expression with
        | .number _ => recurse sources catalog caller rest calls
        | .name path =>
          let [name] := path | throw .request
          Finite.exactWork (Exact.charge ((name.utf8ByteSize+1)*(caller.parameters.length+1)))
          Finite.guard (caller.parameters.contains name) .request
          recurse sources catalog caller rest calls
        | .add a b | .sub a b | .mul a b =>
          Finite.exactWork (Exact.charge 2)
          recurse sources catalog caller (a::b::rest) calls
        | .call path arguments =>
          let key ← resolve sources caller path
          Finite.exactWork (Exact.charge ((catalog.length+1)*(keyCells key+1)+arguments.length+1))
          let [target] := catalog.filter (fun entry => entry.key == key) | throw .request
          Finite.guard (arguments.length == target.helper.parameters.length) .request
          Finite.exactWork (Exact.charge ((calls.length+1)*((path.map String.utf8ByteSize).sum+keyCells key+1)))
          let calls := if calls.contains (path,key) then calls else (path,key) :: calls
          recurse sources catalog caller (arguments ++ rest) calls)

private def dependencies (sources : Sources) (catalog : List Original) (original : Original) :
    WorkM Original := do
  Finite.exactWork (Exact.charge (2*original.helper.premises.length+1))
  let pending := original.helper.body :: original.helper.premises.flatMap (fun p => [p.left,p.right])
  let calls ← scan (original.source.utf8ByteSize+1) sources catalog ⟨original.key.moduleName,original.helper.parameters⟩ pending []
  return {original with calls := calls.reverse}

/-- Resolve expressions in an explicitly supplied original formal scope.
This checks names/call categories, not formal provenance or arithmetic. The
caller must bind the scope and expressions to their actual original header. -/
def scopedExpressionBindings (sources : Sources) (catalog : List Original) (moduleName : String)
    (parameters : List String) (expressions : List Expr) : WorkM (List (Path × Key)) := do
  Finite.exactWork (Exact.charge ((sources.toList.map fun row =>
    row.1.utf8ByteSize+row.2.utf8ByteSize).sum+moduleName.utf8ByteSize+1))
  let [(_,source)] := sources.toList.filter (fun row => row.1 == moduleName) | throw .request
  let calls ← scan (source.utf8ByteSize+1) sources catalog ⟨moduleName,parameters⟩ expressions []
  return calls.reverse

/-- Field expressions have an actual source module and an empty formal scope;
no synthetic helper declaration or producer binding table is introduced. -/
def expressionBindings (sources : Sources) (catalog : List Original) (moduleName : String)
    (expression : Expr) : WorkM (List (Path × Key)) :=
  scopedExpressionBindings sources catalog moduleName [] [expression]

private def order : Nat → List Original → List Original → WorkM (List Original) :=
  Nat.rec (fun pending ready => if pending.isEmpty then pure ready.reverse else throw .request)
    (fun _ recurse pending ready => do
      if pending.isEmpty then return ready.reverse
      Finite.exactWork (Exact.charge (pending.length+ready.length+1))
      let readyKeys := ready.map (·.key)
      let next ← pending.foldlM (fun selected entry => do
        if selected.isSome then return selected
        Finite.exactWork (Exact.charge ((entry.calls.map (fun call => keyCells call.2+1)).sum*(ready.length+1)+1))
        return if entry.calls.all (fun call => readyKeys.contains call.2) then some entry else none) none
      let some next := next | throw .request
      Finite.exactWork (Exact.charge ((keyCells next.key+1)*(pending.length+1)))
      recurse (pending.filter (fun entry => entry.key != next.key)) (next :: ready))

/-- Original-source collection and topological order, including unused bodies.
The caller must still normalize every returned definition before any use. -/
def prepare (sources : Sources) : WorkM (List Original) := do
  let catalog ← gather sources
  let catalog ← catalog.mapM (dependencies sources catalog)
  order catalog.length catalog []

end QleisliKernel.SourceTypes.NaturalCatalog
