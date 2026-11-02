import QleisliKernel.SourceTypes.SourceRuntimeTrace
import QleisliKernel.SourceTypes.SourceRuntimeOrdinary
import QleisliKernel.Tests.SourceTraceOriginals

/-! Complete original enum matches around quantum owners and qmatch. These
checks preserve every source arm and logical ordinary result; actual native
case intervals, SSA phis and full history equations remain separate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceRuntimeMatch
open QleisliKernel QleisliKernel.SourceTypes SourceRuntimeValues SourceRuntimeContext

private def sources (source : String) : Sources := #[("main",source)] ++ SourceTraceOriginals.bundled
private def read (source : String) :=
  ((SourceRuntimeTrace.read (sources source) "main" "route").run 2000000000).1.toOption

private def owners :=
  "enum Tag{A,B,C}pub unitary fn route(tag:Tag,a:Q<Bit>,b:Q<Unit>)->(Q<Bit>,Q<Unit>){" ++
  "match tag{Tag::C=>(h(a),b),Tag::A=>(a,b),Tag::B=>(a,b)}}"
#guard (read owners).map (fun checked => ((valueOwners checked.summary.value).map (·.ordinal),
  checked.summary.consumed.map (·.ordinal))) = some ([2,3],[0,1])
#guard (read owners).map (fun checked => checked.events.map (fun event => match event with
  | .matching event arms => (event.labels.labels.ordinals,arms.length,event.phis.map (·.inputs.length))
  | _ => ([],0,[]))) = some [([2,0,1],3,[3,3])]

private def ordinary :=
  "enum Tag{A,B,C}pub fn route(tag:Tag)->Bit{match tag{Tag::C=>1,Tag::A=>0,Tag::B=>0}}"
private def valuation (n : Nat) : Semantics.SourceOrdinary.Valuation :=
  ⟨fun i => if i == 0 then some n else none,fun _ => none,fun _ _ _ => none⟩
#guard (read ordinary).map (fun checked => (List.range 3).map fun n =>
  (SourceRuntimeOrdinary.extract (valuation n) checked.summary.value).toOption.map fun values =>
    values.map (fun atom => match atom with | .ordinary _ ordinal => ordinal | _ => 100)) =
  some [some [0],some [0],some [1]]
#guard (read (ordinary.replace "Tag::B=>0" "Tag::A=>0")).isNone
#guard (read (ordinary.replace ",Tag::B=>0" "")).isNone
#guard (read ("enum Other{A,B,C}" ++ ordinary.replace "Tag::B=>0" "Other::B=>0")).isNone

private def coherent :=
  "enum Tag{Off,On}unitary fn idle(q:Q<Bit>)->Q<Bit>{q}unitary fn hi(q:Q<Bit>)->Q<Bit>{h(q)}" ++
  "pub unitary fn route(tag:Tag,s:Q<Tag>,q:Q<Bit>)->(Q<Tag>,Q<Bit>){match tag{" ++
  "Tag::Off=>qmatch(s,q){Tag::Off=>idle,Tag::On=>hi}," ++
  "Tag::On=>qmatch(s,q){Tag::Off=>hi,Tag::On=>idle}}}"
#guard (read coherent).map (fun checked => checked.events.flatMap Event.qmatchOffsets |>.length) = some 2
#guard (read ("use std::state::reset;enum Tag{A,B}" ++
  "pub unitary fn route(q:Q<Bit>)->Q<Bit>{match Tag::A{Tag::A=>q,Tag::B=>reset(q)}}")).isNone
#guard (read (owners.replace "(a,b),Tag::B=>(a,b)" "(a,b),Tag::B=>(b,a)")).isNone

private def recovered := do
  let body ← SourceRuntimeTrace.read (sources owners) "main" "route"
  let [Event.matching event _] := body.events | throw Finite.Error.request
  let fresh ← SourceRuntimeTrace.readMatchSource event
  return fresh.results.map fun result => (valueOwners result.value).map (·.ordinal)
#guard (recovered.run 2000000000).1.toOption = some [[0,1],[0,1],[0,1]]

#print axioms QleisliKernel.SourceTypes.SourceRuntimeMatching.merge
#print axioms QleisliKernel.SourceTypes.SourceRuntimeTrace.readMatchSource
end QleisliKernel.Tests.SourceRuntimeMatch
