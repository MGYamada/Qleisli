import QleisliKernel.Qirf.StructuralComputedRaw
import QleisliKernel.Raw.Pure

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

private def usingSteps (step : Step) : StructuralComputedRaw.Packet :=
  {packet with forward := [step],inverse := [step]}

#guard status (usingSteps ⟨[⟨2,true⟩],.monomial [2] [1,0] [0,0]⟩) == some .equation
#guard status (usingSteps ⟨[⟨0,true⟩,⟨0,false⟩],.monomial [2] [1,0] [0,0]⟩) == some .equation
#guard status (usingSteps ⟨[⟨0,false⟩],.monomial [2] [1,0] [0,0]⟩) == none
#guard status (usingSteps ⟨[],.monomial [2] [1,0] [4,4]⟩) == some .equation
#guard status (usingSteps ⟨[],.contract [2] 0 false⟩) == some .equation


private def program (packet : StructuralComputedRaw.Packet) : Semantics.Raw.Program :=
  ⟨[input,spectator],
    [.structuralCompute packet.input packet.output packet.scratch packet.forward packet.inverse packet.uses],
    [packet.output,spectator.token],.unitary⟩

private def checkedTrace (packet : StructuralComputedRaw.Packet) : Option Semantics.RawTrace.Prepared :=
  ((Raw.Pure.verify [] (program packet)).run exactWorkLimit).1.toOption.map (·.reference)

#guard (checkedTrace packet).map (·.events) ==
  some [.structuralComputed 2 [0,1] flip flip packet.uses,.reorder 2 [0,1]]
#guard checkedTrace packet == Semantics.RawTrace.run (program packet)
#guard (checkedTrace {packet with inverse := []}).isNone
#guard (checkedTrace {packet with scratch := 2}).isNone
#guard (checkedTrace {packet with output := spectator.token}).isNone

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

private def intervalProbe (text : String) (candidate : StructuralComputedRaw.Packet) :
    Finite.WorkM (List Nat) := do
  let checked ← SourceRuntimeTrace.read #[("main",text)] "main" "route"
  let [Event.computed event _] := checked.events | throw .request
  let auxiliary : Semantics.SourceOwners.Owner := ⟨2,[.unit]⟩
  let history : RuntimeStructuralAction.SourceState :=
    ⟨[⟨event.input,input⟩,⟨auxiliary,spectator⟩],[event.input,auxiliary],event.nextOrdinal⟩
  let whole : Semantics.Observation.Program :=
    ⟨[input,spectator],[],[.pure candidate.operation],[12,11],[],.unitary⟩
  let prepared ← RuntimeInterval.prepare [] whole
  let interval ← RuntimeInterval.check prepared.block 0 1
  let action ← StructuralComputedRaw.readInterval event interval history
  return action.checked.output.wires

#guard ((intervalProbe source packet).run exactWorkLimit).1.toOption == some [8,2]
#guard ((intervalProbe (source.replace "a and b" "a xor b") packet).run
  exactWorkLimit).1.toOption.isNone
#guard ((intervalProbe source {packet with uses := [.phase [] .minusOne] ++ packet.uses}).run
  exactWorkLimit).1.toOption.isNone

end QleisliKernel.Tests.StructuralComputedRaw
