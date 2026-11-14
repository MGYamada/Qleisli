import QleisliKernel.Qirf.StructuralComputedUse

/-! Source-derived compute and inverse around an independently checked use.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.StructuralComputedUse
open QleisliKernel Qirf SourceTypes SourceRuntimeContext Semantics.Finite

private def source : String := "#![no_implicit_prelude]\n" ++
  "classical fn both((lo,hi):(Bit,Bit))->Bit{lo and hi}\n" ++
  "pub unitary fn route(q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>" ++
  "{with_computed(q,both){|flag|phase[1,1](flag)}}"

private def flip : List Step := [⟨[⟨0,true⟩,⟨1,true⟩],.monomial [2] [1,0] [0,0]⟩]
private def z : Semantics.Raw.Use := .protectedGate ⟨.ancilla,0⟩ .z

private def checkOriginal (text : String) (inverse : List Step) (uses : List Semantics.Raw.Use) :
    Finite.WorkM Unit := do
  let checked ← SourceRuntimeTrace.read #[("main",text)] "main" "route"
  let [Event.computed event _] := checked.events | throw .request
  let original ← StructuralXorPredicate.read event
  let _ ← StructuralComputedUse.read original flip inverse uses
  return ()

private def failure (text : String) (inverse : List Step)
    (uses : List Semantics.Raw.Use) : Option Finite.Error :=
  match ((checkOriginal text inverse uses).run exactWorkLimit).1 with
  | .ok _ => none
  | .error error => some error

#guard failure source flip [z] == none
#guard failure source [] [z] == some .equation
#guard failure source flip [.phase [] .minusOne,z] == some .equation
#guard failure source flip [.protectedGate ⟨.ancilla,0⟩ .x] == some .request
#guard failure (source.replace "phase[1,1](flag)" "flag") flip [z] == some .equation

end QleisliKernel.Tests.StructuralComputedUse
