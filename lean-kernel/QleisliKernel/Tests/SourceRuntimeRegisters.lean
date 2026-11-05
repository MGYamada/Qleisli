import QleisliKernel.SourceTypes.SourceRuntimeTrace
import QleisliKernel.SourceTypes.SourceRuntimeOrdinary
import QleisliKernel.Tests.SourceTraceOriginals

/-! Existing register primitives with exact tags, zero-width owners, original
Nat guards and head-first ordinary values. Native repartition maps still need
their actual ordered Split/Join equations with coefficient +1.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceRuntimeRegisters
open QleisliKernel QleisliKernel.SourceTypes SourceRuntimeValues

private def sources (source : String) : Sources := #[("main",source)] ++ SourceTraceOriginals.bundled
private def read (source : String) (arguments : StaticTypes.Arguments := {}) :=
  ((SourceRuntimeTrace.read (sources source) "main" "route" arguments).run 2000000000).1.toOption

private def roundtrip :=
  "pub unitary fn route(q:Q<Bits<1>>)->Q<Bits<1>>{let(bit,rest)=take_bit[1,0](q);put_bit[1,0](bit,rest)}"
#guard (read roundtrip).map (fun checked => ((valueOwners checked.summary.value).map (·.ordinal),
  checked.summary.allocated.map (·.basis),checked.summary.consumed.map (·.ordinal))) =
  some ([3],[[.bit],[.bits 0],[.bits 1]],[0,1,2])
#guard (read "pub unitary fn route(q:Q<Bits<1>>)->Q<Bit>{let(bit,rest)=take_bit[1,0](q);bit}").isNone
#guard (read "pub unitary fn route(q:Q<Bit>)->(Q<Bit>,Q<Bits<0>>){take_bit[1,0](q)}").isNone
#guard (read "pub unitary fn route(bit:Q<Bit>,rest:Q<Unit>)->Q<Bits<1>>{put_bit[1,0](bit,rest)}").isNone
#guard (read (roundtrip.replace "take_bit[1,0]" "take_bit[1,1]")).isNone
#guard (read (roundtrip.replace "take_bit[1,0]" "take_bit")).isNone

private def prepend := "pub fn route(bit:Bit)->Bits<1>{prepend_bit[0](bit,empty_bits())}"
#guard (read prepend).map (fun checked =>
  (checked.summary.quantumUse,checked.summary.generic.quantumUse)) = some (false,false)
-- The original classical bracket form is a retained first parse refusal;
-- normal runtime fn is a separate explicit translation, not a grammar rescue.
#guard (read (prepend.replace "pub fn" "pub classical fn")).isNone

private def packed := "pub fn route(bit:Bit,tail:Bits<1>)->Bits<2>{prepend_bit[1](bit,tail)}"
private def values (head tail : Nat) : Semantics.SourceOrdinary.Valuation :=
  ⟨fun ordinal => [head,tail][ordinal]?,fun _ => none,fun _ _ _ => none⟩
#guard (read packed).map (fun checked =>
  (QleisliKernel.SourceTypes.SourceRuntimeOrdinary.extract (values 0 1) checked.summary.value).toOption) =
  some (some [.ordinary [.bits 2] 2])

private def generic :=
  "pub unitary fn route[const n:Nat,const k:Nat](q:Q<Bits<n>>)->(Q<Bit>,Q<Bits<n-1>>)" ++
  "requires n>0,k<n{take_bit[n,k](q)}"
#guard (read generic {naturals := [("n",2),("k",1)]}).isSome
#guard (read (generic.replace "n>0,k<n" "n>0") {naturals := [("n",2),("k",1)]}).isNone
#guard (read generic {naturals := [("n",2),("k",2)]}).isNone

#print axioms QleisliKernel.SourceTypes.SourceRegisterApplication.read
#print axioms QleisliKernel.SourceTypes.SourceRegisterApplication.apply
end QleisliKernel.Tests.SourceRuntimeRegisters
