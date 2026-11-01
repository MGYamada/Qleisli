import QleisliKernel.SourceTypes.SourceRuntimeTrace
import QleisliKernel.Tests.SourceTraceOriginals

/-! Small typed mixed-body controls. These test actual original-source traversal,
ordinary copying, observation order and owner history, not native arm equations.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceRuntimeTrace
open QleisliKernel QleisliKernel.SourceTypes
open SourceRuntimeValues SourceRuntimeContext

private def sources (source : String) : Sources :=
  #[("main",source)] ++ SourceTraceOriginals.bundled

private def read (source : String) :=
  ((SourceTypes.SourceRuntimeTrace.read (sources source) "main" "route").run 2000000000).1.toOption

private def view (source : String) := (read source).map fun checked =>
  (valueOwners checked.summary.value |>.map (·.ordinal),
    checked.summary.consumed.map (·.ordinal),checked.summary.inferredEffect)

#guard view SourceTraceOriginals.ordinary_spectator = some ([0,1],[],.unitary)
#guard (read SourceTraceOriginals.hidden_observe_negative).isNone

private def ordinaryCopy := "fn duplicate(c:Bit)->(Bit,Bit){(c,c)}" ++
  "pub unitary fn route(c:Bit,q:Q<Bit>)->((Bit,Bit),Q<Bit>){(duplicate(c),q)}"
#guard view ordinaryCopy = some ([0],[],.unitary)
#guard ((read ordinaryCopy).map fun checked => ordinary checked.summary.value |>.map Prod.snd) =
  some [.input 0,.input 0]

private def observed := "observe fn read(q:Q<Bit>)->Bit{measure_z(h(q))}" ++
  "pub observe fn route(a:Q<Bit>,b:Q<Bit>)->(Q<Bit>,Bit){(h(a),read(b))}"
#guard view observed = some ([0],[1],.observe)
#guard ((read observed).map fun checked => checked.events.map fun event => match event with
  | .primitive primitive => (primitive.kind.name,primitive.held.map (·.ordinal))
  | .named named => (named.target.resolution.declaration.name,named.held.map (·.ordinal))
  | _ => ("other",[])) = some [("h",[]),("read",[0])]
#guard ((read observed).map fun checked => ordinary checked.summary.value |>.all fun (_,expression) =>
  match expression with
  | .measured origin [call] owner =>
    origin.moduleName == "main" && origin.functionName == "read" &&
      call.functionName == "route" && owner.ordinal == 1
  | _ => false) = some true

#guard (read (observed.replace "pub observe fn route" "pub unitary fn route")).isNone
#guard (read (observed.replace "observe fn read" "unitary fn read")).isNone
#guard (read "pub unitary fn route(q:Q<Bit>)->Bit{measure_z(q)}").isNone
#guard (read "pub isometry fn route(q:Q<Bit>)->Bit{measure_z(q)}").isNone
#guard (read "pub observe fn route(q:Q<Bit>)->(Bit,Bit){(measure_z(q),measure_z(q))}").isNone
#guard (read "pub observe fn route(q:Q<Bit>)->(Q<Bit>,Bit){(q,measure_z(q))}").isNone
#guard (read "pub observe fn route(q:Q<Bit>)->Bit{not q}").isNone
#guard view "pub fn route(c:Bit)->(Bit,Bit){let x=c xor c;(not x,c)}" = some ([],[],.unitary)

-- Logical Unit allocation/release is explicit. Bits<0> is a different type.
#guard view "pub unitary fn route(q:Q<Bit>)->Q<Bit>{let u=unit(());finish(u);q}" = some ([0],[1],.unitary)
#guard (read "pub unitary fn route(q:Q<Bit>)->Q<Bit>{let u=unit(());q}").isNone
#guard (read "pub unitary fn route(u:Q<Bits<0>>)->Unit{finish(u)}").isNone
#guard (read "pub fn route()->Unit{let u=unit(());finish(u)}").isNone
#guard (read "pub classical fn route()->Unit{let u=unit(());finish(u)}").isNone
#guard view "pub observe fn route(u:Q<Bits<0>>)->Unit{discard(u)}" = some ([],[0],.observe)

-- Explicit split/join retains exact basis trees and source action history.
#guard view "pub unitary fn route(q:Q<(Bit,Unit)>)->Q<(Bit,Unit)>{let(a,b)=split(q);join(a,b)}" =
  some ([3],[0,1,2],.unitary)
#guard (read "pub unitary fn route(q:Q<(Bit,Unit)>)->Q<(Unit,Bit)>{let(a,b)=split(q);join(a,b)}").isNone

private def external (effect : String) :=
  #[ ("main","use lib::f;pub " ++ effect ++ " fn route(c:Bit)->Bit{f(c)}"),
     ("lib","pub observe fn f(c:Bit)->Bit{c}") ] ++ SourceTraceOriginals.bundled
#guard ((SourceTypes.SourceRuntimeTrace.read (external "unitary") "main" "route").run 2000000000).1.toOption.isNone
#guard ((SourceTypes.SourceRuntimeTrace.read (external "observe") "main" "route").run 2000000000).1.isOk

#print axioms QleisliKernel.SourceTypes.SourceRuntimeTrace.read
#print axioms QleisliKernel.SourceTypes.SourceRuntimeTrace.Checked.completeOwnerHistory
#print axioms QleisliKernel.SourceTypes.SourceRuntimeTrace.Checked.effectAssertion
#print axioms QleisliKernel.SourceTypes.SourceRuntimeTrace.Checked.unitaryNoObservation
end QleisliKernel.Tests.SourceRuntimeTrace
