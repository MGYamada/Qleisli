import QleisliKernel.SourceTypes.SourceRuntimeTrace
import QleisliKernel.Tests.SourceTraceOriginals

/-! Actual original computed scope typing, owner histories and source bodies.
A successful source traversal still has an explicit protected/certified native
equation obligation; typed auxiliary return is deliberately not clean evidence.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceRuntimeComputed
open QleisliKernel QleisliKernel.SourceTypes SourceRuntimeValues SourceRuntimeContext

private def sources (source : String) : Sources := #[("main",source)] ++ SourceTraceOriginals.bundled
private def read (source : String) :=
  ((SourceRuntimeTrace.read (sources source) "main" "route").run 2000000000).1.toOption

private def predicate := "classical fn predicate(b:Bit)->Bit{b}"
private def protectedSource := predicate ++
  "pub unitary fn route(q:Q<Bit>)->Q<Bit>{with_computed(q,predicate){|aux|z(aux)}}"
#guard (read protectedSource).map (fun checked => ((valueOwners checked.summary.value).map (·.ordinal),
  checked.summary.allocated.map (·.ordinal),checked.summary.consumed.map (·.ordinal),
  checked.events.flatMap Event.computedOffsets |>.length)) = some ([0],[1],[1],1)

private def certifiedSource := predicate ++
  "unitary fn logical(q:Q<Bit>)->Q<Bit>{z(q)}" ++
  "pub unitary fn route(q:Q<Bit>)->Q<Bit>{with_computed(q,predicate,logical){|data,aux|(z(data),aux)}}"
#guard (read certifiedSource).isSome
#guard (read (certifiedSource.replace "(z(data),aux)" "(data,z(aux))")).isSome

-- H is a well-typed use body. Only a later exact native cleanup equation can
-- reject this protected scope; source typing never certifies its cleanliness.
#guard (read (protectedSource.replace "z(aux)" "h(aux)")).isSome
#guard (read (protectedSource.replace "classical fn predicate" "fn predicate")).isNone
#guard (read (protectedSource.replace "predicate(b:Bit)" "predicate((b,u):(Bit,Unit))")).isNone
#guard (read ("use std::state::reset;" ++ protectedSource.replace "z(aux)" "reset(aux)")).isNone
#guard (read (protectedSource.replace "z(aux)" "q")).isNone
#guard (read (protectedSource.replace "z(aux)" "unit(())")).isNone

private def capture := predicate ++
  "pub unitary fn route(c:Bit,q:Q<Bit>)->Q<Bit>{with_computed(q,predicate){|aux|if c{z(aux)}else{aux}}}"
#guard (read capture).isSome
private def certifiedCapture := (certifiedSource.replace "route(q:" "route(c:Bit,q:").replace
  "(z(data),aux)" "(if c{z(data)}else{data},aux)"
#guard (read certifiedCapture).isNone

private def inactive := predicate ++
  "pub unitary fn route[const n:Nat](q:Q<Bit>)->Q<Bit>{if static n==0{q}else{with_computed(q,predicate){|aux|z(aux)}}}"
#guard ((SourceRuntimeTrace.read (sources inactive) "main" "route" {naturals := [("n",0)]}).run 2000000000).1.toOption.map
  (fun checked => checked.events.flatMap Event.computedOffsets |>.length) = some 0
#guard ((SourceRuntimeTrace.read (sources inactive) "main" "route" {naturals := [("n",1)]}).run 2000000000).1.toOption.map
  (fun checked => checked.events.flatMap Event.computedOffsets |>.length) = some 1

private def recovered : Finite.WorkM (List Nat × Bool) := do
  let checked ← SourceRuntimeTrace.read (sources protectedSource) "main" "route"
  let [Event.computed event _] := checked.events | throw Finite.Error.request
  let body ← SourceRuntimeTrace.readComputedSource event
  let predicate ← SourceRuntimeTrace.readComputedPredicateBody event
  return ((valueOwners body.result.value).map (·.ordinal),predicate.checked.summary.generic.quantumUse)
#guard (recovered.run 2000000000).1.toOption = some ([1],false)

#print axioms QleisliKernel.SourceTypes.SourceComputedBindings.originalMember
#print axioms QleisliKernel.SourceTypes.SourceRuntimeTrace.readComputedSource
end QleisliKernel.Tests.SourceRuntimeComputed
