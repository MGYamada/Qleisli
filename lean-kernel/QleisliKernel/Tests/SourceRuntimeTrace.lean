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

private def originalAccess (text : String) : Except String (Option (List (String × String))) := do
  let tokens ← lexLocated text
  match ← SourceSyntax.read (tokens.length+1) 0 false tokens with
  | .exclusive written _ =>
    pure (some (written.arguments.map fun entry => (entry.2.marker.text,entry.2.owner.text)))
  | .call .. => pure none
  | _ => throw "expected call"

#guard (originalAccess "turn[1](excl q[1],ctrl c)").toOption = some (some [("excl","q"),("ctrl","c")])
#guard ["f(ctrl)","f(ctrl,excl)","f(excl[0],ctrl(x))","f(ctrl(x))","f(ctrl[i](x))","f(ctrl::g(x))"].all
  (fun input => (originalAccess input).toOption == some none)
#guard (originalAccess "f(1,excl q)").toOption = some (some [("excl","q")])
#guard (originalAccess "f(ctrl c,q)").toOption = some (some [("ctrl","c")])

private def originalMixedUnit := "unitary fn turn(pre:Unit,t:Q<Bit>,post:Unit)->Q<Bit>{h(t)} " ++
  "pub unitary fn route(tag:Unit,q:Q<Bits<2>>)->Q<Bits<2>>{turn((),excl q[1],tag);q}"

private def mixedAccessReplay (source : String) : Option (List Value × List Value × List Nat × List Nat) := do
  let checked ← read source
  let [.exclusive access (.named named)] := checked.events | none
  some (access.arguments.values,named.arguments,access.reservation.arguments.map (·.ordinal),
    (valueOwners checked.summary.value).map (·.ordinal))

#guard mixedAccessReplay originalMixedUnit ==
  let values := [[.ordinary [.unit] .unit],[.owner ⟨1,[.bit]⟩],[.ordinary [.unit] (.input 0)]]
  some (values,values,[1],[0])
#guard mixedAccessReplay (originalMixedUnit.replace "(),excl q[1],tag" "tag,excl q[1],()") ==
  let values := [[.ordinary [.unit] (.input 0)],[.owner ⟨1,[.bit]⟩],[.ordinary [.unit] .unit]]
  some (values,values,[1],[0])
#guard (read (originalMixedUnit.replace "(),excl q[1]" "excl q[1],()")).isNone
#guard (read (originalMixedUnit.replace ",tag);q" ",q);q")).isNone
#guard (read (originalMixedUnit.replace "(),excl q[1]" "0,excl q[1]")).isNone
#guard (read (originalMixedUnit.replace "(),excl q[1]" "discard(q),excl q[1]")).isNone

private def originalMixedBit :=
  "unitary fn turn(marker:Unit,choose:Bit,a:Q<Bit>,other:Bit)->Q<Bit>{if choose{h(a)}else{a}} " ++
  "pub unitary fn route(flag:Bit,spare:Bit,q:Q<Bit>)->Q<Bit>{turn((),flag,excl q,spare);q}"

private def mixedBitCondition (source : String) : Option (Expression × Expression) := do
  let checked ← read source
  let [.exclusive _ (.named named)] := checked.events | none
  let callee ← ((SourceTypes.SourceRuntimeTrace.readNamedBody named).run 2000000000).1.toOption
  let [.conditional branch _ _] := callee.checked.events | none
  let actual ← (expressionTransport ⟨"main",named.target.callerName,named.call.calleeOffset⟩
    named.ownerMap (named.arguments.flatMap ordinary) branch.condition).toOption
  some (branch.condition,actual)

#guard mixedAccessReplay originalMixedBit ==
  let values := [[.ordinary [.unit] .unit],[.ordinary [.bit] (.input 0)],
    [.owner ⟨0,[.bit]⟩],[.ordinary [.bit] (.input 1)]]
  some (values,values,[0],[1])
#guard mixedBitCondition originalMixedBit == some (.input 1,.input 0)
#guard mixedBitCondition (originalMixedBit.replace "flag,excl q,spare" "spare,excl q,flag") ==
  some (.input 1,.input 1)
#guard (read (originalMixedBit.replace "excl q" "ctrl q")).isNone
#guard (read (originalMixedBit.replace "flag:Bit" "flag:Bits<1>")).isNone
#guard (read (originalMixedBit.replace "(),flag,excl" "(),0,excl")).isNone
#guard (read (originalMixedBit.replace "(),flag,excl" "(),not flag,excl")).isNone

private def orderedAccess (text : String) : Except String (List (Option AccessSyntax.Role × List String)) := do
  let call ← AccessSyntax.readAccessCall (← lexLocated text)
  return call.slots.map fun slot =>
    let role := match slot.2 with
      | .ordinary _ => none
      | .access argument => some argument.role
    (role,slot.1.map (·.text))

#guard (orderedAccess "turn[1](ctrl,excl q[1],ctrl(x),ctrl c,(0,1),excl,ctrl::g(x))").toOption ==
  some [(none,["ctrl"]),(some .excl,["excl","q","[","1","]"]),(none,["ctrl","(","x",")"]),
    (some .ctrl,["ctrl","c"]),(none,["(","0",",","1",")"]),(none,["excl"]),
    (none,["ctrl","::","g","(","x",")"])]
#guard (orderedAccess "f(ctrl c,1)").toOption == some [(some .ctrl,["ctrl","c"]),(none,["1"])]
#guard (orderedAccess "f(ctrl,excl,ctrl(x),ctrl::g(x))").toOption.isNone
#guard (orderedAccess "f(ctrl c[0..],1)").toOption.isNone
#guard (orderedAccess "f(1,excl q,)").toOption.isNone

private def accessBinding (source : String) :
    Option (List (Bool × Nat × Option (Nat × Nat)) × List Nat × List Nat × Semantics.Raw.Effect) := do
  let checked ← read source
  let [.exclusive access child] := checked.events | none
  let places := access.checked.entries.map fun entry =>
    (entry.1.2.role == .ctrl,entry.2.parent.ordinal,entry.2.coordinates.range)
  some (places,access.reservation.arguments.map (·.ordinal),access.returned.outputs.map (·.ordinal),child.effect)

private def indexedMixed := "unitary fn turn(t:Q<Bit>,c:Q<Bit>)->(Q<Bit>,Q<Bit>){(h(t),c)} " ++
  "pub unitary fn route(c:Q<Bit>,q:Q<Bits<2>>)->(Q<Bit>,Q<Bits<2>>){turn(excl q[1],ctrl c);(c,q)}"
#guard accessBinding indexedMixed == some ([(false,1,some (1,2)),(true,0,none)],[2,0],[2,0],.unitary)
#guard (read (indexedMixed.replace "ctrl c" "ctrl q[1]")).isNone
#guard (accessBinding (indexedMixed.replace "ctrl c" "excl c")).isSome

-- A whole ctrl still retains the source event and zero-width port. Its
-- sector evidence remains an obligation of the independently checked Raw.
#guard accessBinding "pub unitary fn route(q:Q<Bits<0>>)->Q<Bits<0>>{global_phase_eighth(ctrl q);q}" ==
  some ([(true,0,none)],[0],[0],.unitary)
#guard (accessBinding "pub unitary fn route(q:Q<Bit>)->Q<Bit>{h(excl q);q}").isNone
#guard view "pub unitary fn route(q:Q<Bit>)->Q<Bit>{h(excl q);q}" = some ([0],[],.unitary)

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

private def externalClassical :=
  #[ ("main","use lib::f;pub fn route(c:Bit)->Bit{f(c)}"),
     ("lib","pub classical fn f(c:Bit)->Bit{not c}") ] ++ SourceTraceOriginals.bundled
#guard ((SourceTypes.SourceRuntimeTrace.read externalClassical "main" "route").run 2000000000).1.isOk
#guard (read "pub fn route(c:Bit,c:Bit)->Bit{c}").isNone
#guard (read "pub fn route()->Bit{let(c,c)=(0,1);c}").isNone
#guard view "pub fn route(c:Bit)->Bit{let c=not c;c}" = some ([],[],.unitary)

private def unusedAliasRows :=
  #[ ("main","use helpers::next;pub fn route(c:Bit)->Bit{static let ignored=next[1]();c}"),
     ("helpers","pub static fn next[const n:Nat]()->Nat{n+1}"),
     ("unused","pub static fn spare[const n:Nat]()->Nat{n}") ] ++ SourceTraceOriginals.bundled
#guard (((SourceTypes.SourceRuntimeTrace.read unusedAliasRows "main" "route").run 2000000000).1.toOption.map fun checked =>
  (checked.events.isEmpty,checked.summary.staticRows.any (fun row => row.1 == "helpers"),
    checked.summary.staticRows.any (fun row => row.1 == "unused"))) = some (true,true,false)

#guard view "pub unitary fn route(q:Q<Bit>)->Q<Bit>{basis q as b{b}}" = some ([0],[],.unitary)
#guard view "pub unitary fn route(q:Q<Bit>)->Q<Bit>{basis q as b{not b}}" = some ([0],[],.unitary)
#guard (read "pub unitary fn route(q:Q<Bit>)->Q<Bit>{basis q as b{0}}").isNone
#guard view "pub isometry fn route()->Q<Bit>{init0()}" = some ([1],[0],.iso)
#guard view "use std::state::reset;pub observe fn route(q:Q<Bit>)->Q<Bit>{reset(q)}" =
  some ([2],[0,1],.observe)
#guard (read "use std::state::reset;pub unitary fn route(q:Q<Bit>)->Q<Bit>{reset(q)}").isNone
#guard (read "pub unitary fn route(q:Q<Bit>)->Q<Bit>{basis q as b{let u=unit(());finish(u);b}}").isNone

private def branchPermutation :=
  "pub unitary fn route(c:Bit,a:Q<Bit>,b:Q<Bit>)->(Q<Bit>,Q<Bit>){if c{(a,h(b))}else{(b,h(a))}}"
#guard view branchPermutation = some ([2,3],[1,0],.unitary)
#guard ((read branchPermutation).map fun checked => checked.events.all fun event => match event with
  | .conditional branch left right =>
    branch.phis.map (fun phi => (phi.output.ordinal,phi.thenOwner.ordinal,phi.elseOwner.ordinal)) ==
      [(2,0,1),(3,1,0)] && left.length == 1 && right.length == 1
  | _ => false) = some true
#guard view "pub unitary fn route(q:Q<Bit>)->Q<Bit>{if 1{h(q)}else{q}}" = some ([1],[0],.unitary)
#guard (read "use std::state::reset;pub unitary fn route(q:Q<Bit>)->Q<Bit>{if 1{q}else{reset(q)}}").isNone
#guard (read "pub observe fn route(c:Bit,q:Q<Bit>)->(Bit,Q<Bit>){let b=if c{let q=h(q);0}else{0};(b,q)}").isNone
#guard (read "pub unitary fn route(c:Bit,a:Q<Bit>,b:Q<Bits<1>>)->(Q<Bit>,Q<Bits<1>>){if c{(a,b)}else{(b,a)}}").isNone
#guard (read "pub unitary fn route(c:Bit,a:Q<Unit>,b:Q<Bits<0>>)->(Q<Unit>,Q<Bits<0>>){if c{(a,b)}else{(b,a)}}").isNone
#guard view "pub fn route(c:Bit)->(Bit,Bit){let b=if c{let c=not c;c}else{c};(b,c)}" = some ([],[],.unitary)
#guard ((read "pub fn route(c:Bit)->(Bit,Bit){let b=if c{let c=not c;c}else{c};(b,c)}").map fun checked =>
  (ordinary checked.summary.value).map Prod.snd) = some
    [.choose (.input 0) (.not (.input 0)) (.input 0),.input 0]
#guard view "pub unitary fn route(c:Bit,q:Q<Bit>)->Q<Bit>{basis q as b{if c{b}else{not b}}}" =
  some ([0],[],.unitary)

#print axioms QleisliKernel.SourceTypes.SourceRuntimeTrace.read
#print axioms QleisliKernel.SourceTypes.SourceRuntimeTrace.Checked.completeOwnerHistory
#print axioms QleisliKernel.SourceTypes.SourceRuntimeTrace.Checked.effectAssertion
#print axioms QleisliKernel.SourceTypes.SourceRuntimeTrace.Checked.unitaryNoObservation
#print axioms QleisliKernel.SourceTypes.SourceRuntimeTrace.readBranchSource
end QleisliKernel.Tests.SourceRuntimeTrace
