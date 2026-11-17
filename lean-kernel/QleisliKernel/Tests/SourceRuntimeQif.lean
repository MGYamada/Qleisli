import QleisliKernel.SourceTypes.QuantumArms
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
  | .selection selected => selected.parsed.keyword.text
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
    let [.selection selected] := body.checked.events | throw .request
    let checked ← SourceRuntimeTrace.readInlineArmBody selected index
    let events := checked.result.events.map fun event => match event with
      | .primitive _ => "primitive"
      | .phase phase => s!"phase {phase.application.j.result.value} {phase.application.k.result.value}"
      | .named named => named.target.resolution.declaration.name
      | _ => "other"
    pure (checked.output.basis,checked.output.ordinal,events)
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

private def runtimeTable (source : String) (shift : Nat := 0) : Option (List (Nat × Bool)) :=
  let action : Finite.WorkM _ := do
    let signature ← readSignature #[("main",source)] "main" "route" {}
    let body ← SourceRuntimeTrace.readBodyWithSignature signature
    let [.selection selected] := body.checked.events | throw .request
    let table ← QuantumArms.readRuntimeArms selected (selected.parsed.keyword.span.startByte+shift)
      selected.selector.basis selected.target.basis
    pure (table.arms.map fun arm => (arm.ordinal,match arm with | .inline .. => true | .operation _ => false))
  (action.run 10000000).1.toOption

private def inlineEnum := "#![no_implicit_prelude] pub enum Choice{A,B} " ++
  "pub unitary fn route(c:Q<Choice>,q:Q<Bit>)->(Q<Choice>,Q<Bit>){qmatch(c,q){Choice::B=>{h(q)},Choice::A=>h}}"

#guard runtimeTable inlineBit = some [(0,false),(1,true)]
#guard runtimeTable inlineUnit = some [(1,true),(0,false)]
#guard runtimeTable inlineEnum = some [(1,true),(0,false)]
#guard runtimeTable (inlineEnum.replace "Choice::A=>h" "Choice::B=>h") = none
#guard runtimeTable inlineBit 1 = none
#guard runtimeTable (inlineBit.replace "{let r=h(q);stamp(r)}" "stamp") = some [(0,false),(1,false)]

private def nestedOrdinals : Finite.WorkM (Nat × Nat × Nat × Nat) := do
  let source := "#![no_implicit_prelude] pub unitary fn route(s:Q<Bit>,q:Q<(Bit,Bit)>)->(Q<Bit>,Q<(Bit,Bit)>){" ++
    "qmatch(s,q){1=>{let (a,b)=split(q);let (c,d)=qif(a,b){0=>{b},1=>{h(b)}};join(c,d)},0=>{q}}}"
  let signature ← readSignature #[("main",source)] "main" "route" {}
  let body ← SourceRuntimeTrace.readBodyWithSignature signature
  let [.selection parent] := body.checked.events | throw .request
  let outer ← SourceRuntimeTrace.readInlineArmBody parent 0
  let [.primitive _,.selection child,.primitive _] := outer.result.events | throw .request
  let inner ← SourceRuntimeTrace.readInlineArmBody child 1
  return (parent.nextOrdinal,child.nextOrdinal,inner.output.ordinal,outer.output.ordinal)

#guard (nestedOrdinals.run 10000000).1.toOption == some (2,4,3,4)

private def inlineMarkers (n : Nat) (fault : Bool := false) :
    Finite.WorkM (List (Nat × Nat)) := do
  let source := "#![no_implicit_prelude] classical fn mark(b:Bit)->Bit{b} " ++
    "pub unitary fn route[const n:Nat](s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){" ++
    "qif(s,q){0=>{if static n==0 {basis q as b{not b}} else {q}}," ++
    "1=>{with_computed(q,mark){|flag|phase[1,1](flag)}}}}"
  let signature ← readSignature #[("main",source)] "main" "route" {naturals := [("n",n)]}
  let body ← SourceRuntimeTrace.readBodyWithSignature signature
  let [.selection site] := body.checked.events | throw .request
  let original := if fault then {site with inlineOffsets := [([],[]),([],[])]} else site
  let left ← SourceRuntimeTrace.readInlineArmBody original 0
  let right ← SourceRuntimeTrace.readInlineArmBody original 1
  return [left.result.events,right.result.events].map (fun events =>
    ((events.flatMap Event.basisOffsets).length,(events.flatMap Event.computedOffsets).length))

#guard ((inlineMarkers 0).run 10000000).1.toOption == some [(1,0),(0,1)]
#guard ((inlineMarkers 1).run 10000000).1.toOption == some [(0,0),(0,1)]
#guard ((inlineMarkers 0 true).run 10000000).1.toOption.isNone

end QleisliKernel.Tests.SourceRuntimeQif
