import QleisliKernel.SourceTypes.SourceRuntimeTrace
import QleisliKernel.Tests.SourceTraceOriginals

/-! Original binding grammar and exact ordinary Unit destructuring. A zero
physical width never turns a distinct ordinary type or Q owner into Unit.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceRuntimePatterns
open QleisliKernel QleisliKernel.SourceTypes SourceRuntimeValues

private def read (source : String) :=
  ((SourceRuntimeTrace.read (#[("main",source)] ++ SourceTraceOriginals.bundled) "main" "route").run 2000000000).1.toOption

#guard (read "pub fn route(():Unit)->Unit{let()=();()}").isSome
#guard (read "pub fn route(value:Unit)->Unit{let()=value;()}").isSome
#guard (read "pub unitary fn route(q:Q<Unit>)->Unit{let()=q;()}").isNone
#guard (read "pub fn route(value:Bits<0>)->Unit{let()=value;()}").isNone
#guard (read "struct Empty{}pub fn route(value:Empty)->Unit{let()=value;()}").isNone
#guard (read "enum One{Only}pub fn route(value:One)->Unit{let()=value;()}").isNone
#guard (read "pub fn route()->Bit{let(value)=0;value}").isNone
#guard (read "pub fn route()->Bit{let(value,)=0;value}").isNone
#guard (read "pub fn route()->(Bit,Unit){let(value,empty)=(0,());(value,empty)}").isSome
#guard (read "pub fn route()->(Bit,Unit){let(value,empty,)=(0,());(value,empty)}").isNone

end QleisliKernel.Tests.SourceRuntimePatterns
