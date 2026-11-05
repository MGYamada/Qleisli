import QleisliKernel.SourceTypes.SourceRuntimeTrace
import QleisliKernel.Tests.SourceTraceOriginals

/-! Original guarded self-calls and concrete decreasing instances. The source
receipt and stack check remain separate; closed values cannot repair a missing
original decrease or authorize a mutual cycle.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceRuntimeRecursion
open QleisliKernel QleisliKernel.SourceTypes SourceRuntimeValues

private def sources (source : String) : Sources := #[("main",source)] ++ SourceTraceOriginals.bundled
private def read (source : String) (n : Nat) :=
  ((SourceRuntimeTrace.read (sources source) "main" "route" {naturals := [("n",n)]}).run 2000000000).1.toOption

private def recurse :=
  "pub unitary fn route[const n:Nat](q:Q<Bit>)->Q<Bit>{if static n==0{q}else{route[n-1](h(q))}}"
#guard (read recurse 0).map (fun checked => (valueOwners checked.summary.value).map (·.ordinal)) = some [0]
#guard (read recurse 2).map (fun checked => (valueOwners checked.summary.value).map (·.ordinal)) = some [0]
#guard (read (recurse.replace "route[n-1]" "route[n]") 0).isNone
#guard (read (recurse.replace "route[n-1]" "route[n+1]") 0).isNone
#guard (read (recurse.replace "if static n==0{q}else{route[n-1](h(q))}" "route[n-1](q)") 2).isNone

private def quantumUse :=
  "pub observe fn route[const n:Nat](q:Q<Bit>)->Bit{if static n==0{measure_z(q)}else{route[n-1](h(q))}}"
#guard (read quantumUse 2).map (fun checked =>
  (checked.summary.generic.inferredEffect,checked.summary.consumed.map (·.ordinal))) = some (.observe,[0])
#guard (read (quantumUse.replace "pub observe fn" "pub unitary fn") 0).isNone

private def ordinary :=
  "pub fn route[const n:Nat](b:Bit)->Bit{if static n==0{b}else{route[n-1](not b)}}"
#guard (read ordinary 2).isSome
#guard (read (ordinary.replace "pub fn" "pub classical fn") 0).isNone

private def mutualSource :=
  "unitary fn helper[const n:Nat](q:Q<Bit>)->Q<Bit>{if static n==0{q}else{route[n-1](q)}}" ++
  "pub unitary fn route[const n:Nat](q:Q<Bit>)->Q<Bit>{helper[n](q)}"
#guard (read mutualSource 0).isNone

#print axioms QleisliKernel.SourceTypes.SourceRecursion.read
#print axioms QleisliKernel.SourceTypes.SourceRuntimeTrace.readNested
end QleisliKernel.Tests.SourceRuntimeRecursion
