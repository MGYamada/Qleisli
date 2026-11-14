import QleisliKernel.Qirf.StructuralComputedRaw

/-! Circuit-backed protected packets with two data bits and private scratch.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.StructuralComputedRaw
open QleisliKernel Qirf SourceTypes SourceRuntimeContext Semantics.Finite

private def input : Semantics.Raw.Port := ⟨10,[8,2],2⟩
private def spectator : Semantics.Raw.Port := ⟨11,[],0⟩
private def initial : Raw.State :=
  {live := [input,spectator],seenTokens := [10,11,9],seenWires := [8,2,6],frame := [2,8]}
private def flip : List Step := [⟨[⟨0,true⟩,⟨1,true⟩],.monomial [2] [1,0] [0,0]⟩]
private def packet : StructuralComputedRaw.Packet :=
  ⟨10,12,4,flip,flip,[.protectedGate ⟨.ancilla,0⟩ .z]⟩

private def status (packet : StructuralComputedRaw.Packet) : Option Finite.Error :=
  match ((StructuralComputedRaw.read packet initial).run 400000).1 with
  | .ok _ => none
  | .error error => some error

private def exit := ((StructuralComputedRaw.read packet initial).run 400000).1.toOption.map (·.after)

#guard exit.map (·.live) == some [spectator,⟨12,[8,2],2⟩]
#guard exit.map (·.frame) == some [2,8]
#guard exit.map (·.seenWires) == some [8,2,6,4]
#guard status {packet with scratch := 6} == some .invalid
#guard status {packet with output := 9} == some .invalid
#guard status {packet with inverse := []} == some .equation
#guard status {packet with uses := [.protectedGate ⟨.ancilla,0⟩ .x]} == some .request
#guard status {packet with uses := [.protectedGate ⟨.source,0⟩ .z]} == some .request

private def source : String := "#![no_implicit_prelude]\n" ++
  "classical fn both((a,b):(Bit,Bit))->Bit{a and b}\n" ++
  "pub unitary fn route(q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>" ++
  "{with_computed(q,both){|flag|phase[1,1](flag)}}"

private def withSource (text : String) (packet : StructuralComputedRaw.Packet) (swap : Bool) :
    Finite.WorkM (List Nat) := do
  let checked ← SourceRuntimeTrace.read #[("main",text)] "main" "route"
  let [Event.computed event _] := checked.events | throw .request
  let original ← StructuralXorPredicate.read event
  let other : Semantics.SourceOwners.Owner := ⟨2,[.unit]⟩
  let binding : RuntimeOwnerMap.Binding := ⟨event.input,if swap then spectator else input⟩
  let second : RuntimeOwnerMap.Binding := ⟨other,if swap then input else spectator⟩
  let history : RuntimeStructuralAction.SourceState := ⟨[binding,second],[event.input,other],event.nextOrdinal⟩
  let checked ← StructuralComputedRaw.readSource original packet history {quantum := initial}
  return checked.output.wires

#guard ((withSource source packet false).run exactWorkLimit).1.toOption == some [8,2]
#guard ((withSource source packet true).run exactWorkLimit).1.toOption.isNone
#guard ((withSource (source.replace "a and b" "a xor b") packet false).run exactWorkLimit).1.toOption.isNone

end QleisliKernel.Tests.StructuralComputedRaw
