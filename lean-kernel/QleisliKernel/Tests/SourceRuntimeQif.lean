import QleisliKernel.SourceTypes.SourceRuntimeTrace
import QleisliKernel.Tests.SourceTraceOriginals

/-! Original qif syntax uses its shared Bit-only coherent selection judgment.
It is neither an ordinary alternative history nor a renamed qmatch token.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceRuntimeQif
open QleisliKernel QleisliKernel.SourceTypes SourceRuntimeValues SourceRuntimeContext

private def read (source : String) :=
  ((SourceRuntimeTrace.read (#[("main",source)] ++ SourceTraceOriginals.bundled) "main" "route").run 2000000000).1.toOption

private def source :=
  "unitary fn idle(q:Q<Bit>)->Q<Bit>{q}" ++
  "pub unitary fn route(c:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){qif(c,q){0=>idle,1=>x}}"
#guard (read source).map (fun checked => checked.events.map (fun event => match event with
  | .selection _ parsed .. => parsed.keyword.text
  | _ => "other")) = some ["qif"]
#guard (read (source.replace "c:Q<Bit>" "c:Q<Bits<1>>")).isNone
#guard (read (source.replace "0=>idle,1=>x" "1=>x,0=>idle")).isNone
#guard (read (source.replace "0=>idle,1=>x" "0=>idle,1=>x,")).isNone
#guard (read (source.replace "qif(c,q)" "qif(q,q)")).isNone

end QleisliKernel.Tests.SourceRuntimeQif
