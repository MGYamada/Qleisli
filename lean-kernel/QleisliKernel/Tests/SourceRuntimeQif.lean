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

private def inlineBody (source : String) (index : Nat) :
    Option (Semantics.FiniteCarrier.Basis × Nat × List String) :=
  let action : Finite.WorkM _ := do
    let signature ← readSignature #[("main",source)] "main" "route" {}
    let body ← SourceRuntimeTrace.readBodyWithSignature signature
    if first : 0 < body.checked.events.length then
      let checked ← SourceRuntimeTrace.readInlineArmBody body ⟨0,first⟩ index
      let events := checked.result.events.map fun event => match event with
        | .primitive _ => "primitive"
        | .phase phase => s!"phase {phase.application.j.result.value} {phase.application.k.result.value}"
        | .named named => named.target.resolution.declaration.name
        | _ => "other"
      pure (checked.output.basis,checked.output.ordinal,events)
    else throw .request
  (action.run 10000000).1.toOption

private def inlineBit := "#![no_implicit_prelude] " ++
  "unitary fn stamp(q:Q<Bit>)->Q<Bit>{global_phase_eighth(q)} " ++
  "pub unitary fn route(c:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){qif(c,q){0=>h,1=>{let r=h(q);stamp(r)}}}"

private def inlineUnit := "#![no_implicit_prelude] " ++
  "unitary fn idle(q:Q<Unit>)->Q<Unit>{q} " ++
  "pub unitary fn route(c:Q<Bit>,q:Q<Unit>)->(Q<Bit>,Q<Unit>){qmatch(c,(q)){1=>{global_phase_eighth(q)},0=>idle}}"

private def inlineProduct := "#![no_implicit_prelude] " ++
  "unitary fn idle(q:Q<(Unit,Bit)>)->Q<(Unit,Bit)>{q} " ++
  "pub unitary fn route(c:Q<Bit>,q:Q<(Unit,Bit)>)->(Q<Bit>,Q<(Unit,Bit)>){" ++
  "static let k=3;qmatch(c,q){1=>{let (u,b)=split(q);join(u,phase[1,k](b))},0=>idle}}"

#guard inlineBody inlineBit 1 = some ([.bit],1,["primitive","stamp"])
#guard inlineBody inlineBit 0 = none
#guard inlineBody inlineBit 2 = none
#guard inlineBody (inlineBit.replace "let r=h(q)" "let r=h(c)") 1 = none
#guard inlineBody inlineUnit 0 = some ([.unit],1,["primitive"])
#guard inlineBody inlineProduct 0 = some ([.pair,.unit,.bit],4,["primitive","phase 1 3","primitive"])

end QleisliKernel.Tests.SourceRuntimeQif
