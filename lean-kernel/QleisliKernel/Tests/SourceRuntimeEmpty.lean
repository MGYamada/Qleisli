import QleisliKernel.SourceTypes.SourceRuntimeTrace
import QleisliKernel.Tests.SourceTraceOriginals

/-! Empty ordinary registers remain distinct from Unit and from their quantum
owners. The exact finite basis equation remains a separate native obligation.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceRuntimeEmpty
open QleisliKernel QleisliKernel.SourceTypes SourceRuntimeValues

private def read (source : String) :=
  ((SourceRuntimeTrace.read (#[("main",source)] ++ SourceTraceOriginals.bundled) "main" "route").run 2000000000).1.toOption

#guard (read "pub classical fn route()->Bits<0>{empty_bits()}").map (fun checked =>
  (checked.summary.value,checked.summary.generic.quantumUse,checked.summary.quantumUse)) =
  some ([.ordinary [.bits 0] (.ordinal 0)],false,false)
#guard (read "pub fn route()->Unit{empty_bits()}").isNone
#guard (read "pub fn route()->Bits<0>{()}").isNone
#guard (read "pub fn route()->Bits<0>{empty_bits(())}").isNone
#guard (read "pub fn route()->Bits<0>{empty_bits[0]()}").isNone

private def factor :=
  "unitary fn empty(q:Q<Unit>)->Q<Bits<0>>{basis q as _{empty_bits()}}" ++
  "unitary fn consume(q:Q<Bits<0>>)->Q<Unit>{basis q as _{()}}" ++
  "pub unitary fn route(q:Q<Unit>)->Q<Unit>{consume(empty(q))}"
#guard (read factor).map (fun checked => (checked.summary.generic.inferredEffect,
  (valueOwners checked.summary.value).map (·.basis))) = some (.unitary,[[.unit]])
#guard (read (factor.replace "consume(empty(q))" "let r=empty(q);q")).isNone

end QleisliKernel.Tests.SourceRuntimeEmpty
