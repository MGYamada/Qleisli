import QleisliKernel.Qirf.RuntimeStructuredRoot

/-! A complete original zero-width runtime boundary, without a semantic handle.
These controls distinguish public effects, ordinary Unit fields and separate
quantum owners even though all physical input and output wire lists are empty.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.RuntimeStructuredRoot
open QleisliKernel QleisliKernel.Finite QleisliKernel.Qirf

private def source : String :=
  "#![no_implicit_prelude] pub observe fn route(empty:Unit,a:Q<Unit>,b:Q<Unit>)->(Q<Unit>,Q<Unit>){(b,a)}"
private def sources : SourceTypes.Sources := #[("main",source)]
private def port (token : Nat) : Semantics.Raw.Port := ⟨token,[],0⟩
private def quantum (token : Nat) : Semantics.RuntimeStorage.Atom := .quantum ⟨port token,[.unit]⟩
private def program : Semantics.Observation.Program :=
  ⟨[port 0,port 1],[],[],[1,0],[],.unitary⟩
private def artifact : Artifact := ⟨#[program],#[],sources,0,none⟩

private def request : RuntimeFamily.Request := {
  selection := .exported, moduleName := "main", declarationName := "route",
  parameters := [Semantics.RuntimeType.ordinary [.unit],
    Semantics.RuntimeType.owner [.unit],Semantics.RuntimeType.owner [.unit]],
  inputStorage := [[.ordinary [.unit] .unit],[quantum 0],[quantum 1]],
  inputRows := [[]],result := Semantics.RuntimeType.tuple 2
    [Semantics.RuntimeType.owner [.unit],Semantics.RuntimeType.owner [.unit]],
  storage := [.tuple 2,quantum 1,quantum 0],publicEffect := .observe }

private def check (requested : RuntimeFamily.Request) : WorkM Unit := do
  let signature ← SourceTypes.SourceRuntimeContext.readSignature sources "main" "route" {}
  let body ← SourceTypes.SourceRuntimeTrace.readBodyWithSignature signature
  let root ← Validity.checkRootWithSources artifact #[] signature.sourceRows
  let prepared ← RuntimeInterval.prepare root.dependencies root.program
  let bindings : RuntimeOwnerMap.Map := [⟨⟨1,[.unit]⟩,port 1⟩,⟨⟨0,[.unit]⟩,port 0⟩]
  let _ ← Qirf.RuntimeStructuredRoot.readBoundary body root prepared bindings requested
  return ()

#guard ((check request).run 10000000).1.toOption.isSome
-- Public Observe is preserved even when the original body is pure.
#guard ((check {request with publicEffect := .unitary}).run 10000000).1.toOption.isNone
-- Swapping both zero-width storage owners cannot change the original return.
#guard ((check {request with storage := [.tuple 2,quantum 0,quantum 1]}).run 10000000).1.toOption.isNone
-- An ordinary zero-width parameter remains present in the full forest.
#guard ((check {request with inputStorage := [[quantum 0],[quantum 1]]}).run 10000000).1.toOption.isNone
-- Equal cardinality and width do not identify Unit and Bits<0>.
#guard ((check {request with storage := [.tuple 2,.quantum ⟨port 1,[.bits 0]⟩,quantum 0]}).run
  10000000).1.toOption.isNone

#print axioms QleisliKernel.Qirf.RuntimeStructuredRoot.Boundary.fullResultType
end QleisliKernel.Tests.RuntimeStructuredRoot
