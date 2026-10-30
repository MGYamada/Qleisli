import QleisliKernel.SourceTypes.StaticNatural

/-! Original Basis/Nat substitution into the shared finite type grammar.
Actual Basis values are reconstructed from original declarations, even when
unused. This internal component does not resolve host source expressions,
grant visibility/operation access or authorize runtime execution. Its caller
must bind type tokens to an actual original signature occurrence.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.StaticTypes
open Finite Semantics.FiniteCarrier

structure Arguments where
  bases : List (String × Basis) := []
  naturals : StaticNatural.Bindings := []

def namesMatch {sources owner name} (original : StaticHeaders.Original sources owner name)
    (arguments : Arguments) : Bool :=
  let expected := original.header.formals.filter (·.kind == .basis)
  arguments.bases.length == expected.length && expected.all (fun formal =>
    (arguments.bases.filter (fun argument => argument.1 == formal.name)).length == 1)

structure Actual (sources : Sources) (argument : String × Basis) where
  checked : ∃ before after,
    (SourceTypes.check sources argument.2).run before = (.ok (),after)

private def readActual (sources : Sources) (argument : String × Basis) :
    WorkM {_value : Unit // Actual sources argument} := do
  let checked ← NaturalAffine.witness (SourceTypes.check sources argument.2)
  have same : checked.val = () := by cases checked.val; rfl
  return ⟨(),⟨by with_reducible simpa only [same] using checked.property⟩⟩

private def readActuals (sources : Sources) (arguments : Arguments) :
    WorkM {_value : Unit // ∀ argument ∈ arguments.bases,Actual sources argument} := do
  let values ← arguments.bases.attach.mapM fun argument => do
    let actual ← readActual sources argument.val
    return (⟨argument.val,actual.property⟩ : {argument : String × Basis // Actual sources argument})
  -- Retain individual checks without deriving an original binding from an
  -- unchecked producer tree. The dependent fold below preserves membership.
  if same : values.map (·.1) = arguments.bases then
    return ⟨(),by
      intro argument member
      have present : argument ∈ values.map (·.1) := by rwa [same]
      obtain ⟨value,_,equal⟩ := List.mem_map.mp present
      exact equal ▸ value.property⟩
  else throw .request

structure Environment (sources : Sources) (owner name : String) (arguments : Arguments) where
  numeric : StaticNatural.Prepared sources owner name ["0"]
  closed : StaticNatural.Closed numeric arguments.naturals
  matched : namesMatch numeric.original arguments = true
  actuals : ∀ argument ∈ arguments.bases,Actual sources argument
  noOperations : numeric.original.header.formals.all (fun formal =>
    match formal.kind with | .operation _ => false | _ => true) = true

def prepare (sources : Sources) (owner name : String) (arguments : Arguments) :
    WorkM (Environment sources owner name arguments) := do
  guard (arguments.bases.length ≤ 32) .limit
  let numeric ← StaticNatural.prepare sources owner name ["0"]
  if operations : numeric.original.header.formals.all (fun formal =>
      match formal.kind with | .operation _ => false | _ => true) = true then
    exactWork (Exact.charge ((arguments.bases.map (fun a => a.1.utf8ByteSize+1)).sum*
      (numeric.original.header.formals.length+1)+1))
    if matched : namesMatch numeric.original arguments = true then
      let closed ← StaticNatural.close numeric arguments.naturals
      let actuals ← readActuals sources arguments
      return ⟨numeric,closed,matched,actuals.property,operations⟩
    else throw .request
  else throw .request

private def parameter {sources owner name arguments}
    (environment : Environment sources owner name arguments) (tokens : List String) :
    WorkM (Option (TypeRead sources)) := do
  let [name] := tokens | pure none
  exactWork (Exact.charge ((name.utf8ByteSize+1)*
    (environment.numeric.original.header.formals.length+arguments.bases.length+1)))
  match environment.numeric.original.header.formals.find? (·.name == name) with
  | none => pure none
  | some formal =>
    guard (formal.kind == .basis) .request
    let some (_,basis) := arguments.bases.find? (·.1 == name) | throw .request
    pure (some ⟨basis,[]⟩)

def readType {sources owner name arguments}
    (environment : Environment sources owner name arguments) (tokens : List String) :
    WorkM (TypeRead sources) := do
  let read ← typeExpressionScopedWithSources sources owner
    (fun expression => do
      let prepared ← StaticNatural.prepare sources owner name expression
      return (← StaticNatural.close prepared arguments.naturals).value)
    (parameter environment) tokens
  let _ ← FiniteCarrier.read read.basis
  return read

theorem Actual.original {sources argument} (actual : Actual sources argument)
    (atom : Atom) (member : atom ∈ argument.2) : OriginalDeclaration sources atom := by
  obtain ⟨before,after,ran⟩ := actual.checked
  exact check_original_declarations sources argument.2 before after ran atom member

end QleisliKernel.SourceTypes.StaticTypes
