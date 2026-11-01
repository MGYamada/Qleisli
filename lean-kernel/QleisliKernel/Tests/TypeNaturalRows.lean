import QleisliKernel.SourceTypes.NaturalRows
import QleisliKernel.SourceTypes.QuantumSignature
import QleisliKernel.SourceTypes.StaticRuntimeSignature

/-! Original nominal field-width dependency routes. A global unused helper
check never supplies dependency coverage, and caller names cannot capture a
field helper in its original closed declaration scope.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.TypeNaturalRows
open SourceTypes Finite Semantics.FiniteCarrier

private def sources : Sources := #[
  ("main","#![no_implicit_prelude] use carrier::Box; " ++
    "pub unitary fn unused[const A:Basis](q:Q<Bit>)->Q<Bit>{q} " ++
    "pub unitary fn closed(q:Q<Box>)->Q<Box>{q}"),
  ("carrier","#![no_implicit_prelude] use helper_alias::one; pub struct Box{data:Bits<one[0]()>}"),
  ("helper_alias","#![no_implicit_prelude] pub use sizes::one;"),
  ("sizes","#![no_implicit_prelude] pub static fn one[const n:Nat]()->Nat{n+1}"),
  ("unused","#![no_implicit_prelude] pub static fn spare[const n:Nat]()->Nat{n}")]

private def rows (scope : List String) : Option (List String) :=
  let action : WorkM (List String) := do
    let helpers ← NaturalHelpers.prepare sources
    let query ← typeExpressionWithSources sources "main" ["Box"]
    let rows ← NaturalRows.typeRead sources "main" helpers scope ["Box"] query
    pure ((rows.map (·.1)).eraseDups.mergeSort (· ≤ ·))
  (action.run 10000000).1.toOption

#guard rows [] = some ["carrier","helper_alias","main","sizes"]
#guard rows ["one"] = some ["carrier","helper_alias","main","sizes"]

-- Unused host Basis actuals retain all original field helper routes.
#guard
  (((do
    let query ← typeExpressionWithSources sources "main" ["Box"]
    let signature ← QuantumSignature.readWithArguments sources "main" "unused" {bases := [("A",query.basis)]}
    pure ((signature.sourceRows.map (·.1)).eraseDups.mergeSort (· ≤ ·))) : WorkM _).run 10000000).1.toOption =
      some ["carrier","helper_alias","main","sizes"]

-- Closed quantum and mixed signature forests use those same original routes.
#guard
  (((do
    let signature ← QuantumSignature.read sources "main" "closed"
    pure ((signature.sourceRows.map (·.1)).eraseDups.mergeSort (· ≤ ·))) : WorkM _).run 10000000).1.toOption =
      some ["carrier","helper_alias","main","sizes"]
#guard
  (((do
    let signature ← StaticRuntimeSignature.read sources "main" "closed" {}
    pure ((signature.sourceRows.map (·.1)).eraseDups.mergeSort (· ≤ ·))) : WorkM _).run 10000000).1.toOption =
      some ["carrier","helper_alias","main","sizes"]

-- An origin name with different retained source bytes supplies no field row.
#guard
  (((do
    let helpers ← NaturalHelpers.prepare sources
    NaturalRows.nominalOrigins sources helpers [.record ⟨"carrier","Box","pub struct Box{}"⟩ ["data"],.bits 1]) :
      WorkM _).run 10000000).1.isOk = false

end QleisliKernel.Tests.TypeNaturalRows
