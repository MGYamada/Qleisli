import QleisliKernel.SourceTypes.SourceRuntimeTrace
import QleisliKernel.Tests.SourceTraceOriginals

/-! Closed static branches retain both original source obligations and only
the selected runtime child. These source checks grant no native interval or
finite basis capability by themselves.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceRuntimeStatic
open QleisliKernel QleisliKernel.SourceTypes SourceRuntimeValues SourceRuntimeContext

private def sources (source : String) : Sources := #[("main",source)] ++ SourceTraceOriginals.bundled
private def read (source : String) (n : Nat) :=
  ((SourceRuntimeTrace.read (sources source) "main" "route" {naturals := [("n",n)]}).run 2000000000).1.toOption

private def choice :=
  "pub unitary fn route[const n:Nat](q:Q<Bit>)->Q<Bit>{if static n==0{q}else{h(q)}}"
#guard (read choice 0).map (fun checked => checked.events.map (fun event => match event with
  | .staticConditional event children => (event.selection.selected,children.length)
  | _ => (false,100))) = some [(true,0)]
#guard (read choice 1).map (fun checked => checked.events.map (fun event => match event with
  | .staticConditional event children => (event.selection.selected,children.length)
  | _ => (true,100))) = some [(false,1)]

private def coherent :=
  "pub unitary fn route[const n:Nat](q:Q<Bit>)->Q<Bit>{if static n==0{q}else{basis q as b{not b}}}"
#guard (read coherent 0).map (fun checked => checked.events.flatMap Event.basisOffsets |>.length) = some 0
#guard (read coherent 1).map (fun checked => checked.events.flatMap Event.basisOffsets |>.length) = some 1
#guard (read (coherent.replace "not b" "0") 1).isNone

-- Inactive original branches still retain type, effect and name obligations.
#guard (read (choice.replace "h(q)" "missing(q)") 0).isNone
#guard (read ("use std::state::reset;" ++ choice.replace "h(q)" "reset(q)") 0).isNone
#guard (read (choice.replace "h(q)" "unit(())") 0).isNone

private def localScope :=
  "pub unitary fn route[const n:Nat](q:Q<Bit>)->Q<Bit>{let r=if static n==0{let a=q;a}else{let a=h(q);a};r}"
#guard (read localScope 0).isSome
#guard (read localScope 1).isSome
#guard (read (localScope.replace ";r}" ";a}") 0).isNone

private def recovered := do
  let body ← SourceRuntimeTrace.read (sources choice) "main" "route" {naturals := [("n",1)]}
  let [Event.staticConditional event _] := body.events | throw Finite.Error.request
  let fresh ← SourceRuntimeTrace.readStaticSource event
  return (fresh.result.events.length,(valueOwners fresh.result.value).map (·.ordinal))
#guard (recovered.run 2000000000).1.toOption = some (1,[0])

#print axioms QleisliKernel.SourceTypes.SourceRuntimeTrace.readStaticSource
end QleisliKernel.Tests.SourceRuntimeStatic
