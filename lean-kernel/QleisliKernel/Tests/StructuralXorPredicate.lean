import QleisliKernel.Qirf.StructuralXorInterval

/-! Recover the predicate from original source and compare exact literal steps.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.StructuralXorPredicate
open Qirf SourceTypes SourceRuntimeContext Semantics.Finite

private def source : String := "#![no_implicit_prelude]\n" ++
  "classical fn both(a:Bit,b:Bit)->Bit{a and b}\n" ++
  "classical fn mark((lo,_,hi):(Bit,Bits<1>,Bit))->Bit{both(lo,hi)}\n" ++
  "pub unitary fn route(q:Q<(Bit,Bits<1>,Bit)>)->Q<(Bit,Bits<1>,Bit)>" ++
  "{with_computed(q,mark){|flag|phase[1,1](flag)}}"

private def circuit (target : Nat) (controls : List Nat) (phase : Nat := 0) : List Step :=
  [⟨controls.map (fun axis => ⟨axis,true⟩),.monomial [target] [1,0] [phase,phase]⟩]

private def checkOriginal (source : String) (steps : List Step) : Finite.WorkM Unit := do
  let checked ← SourceRuntimeTrace.read #[⟨"main",source⟩] "main" "route"
  let [Event.computed event _] := checked.events | throw .request
  let original ← StructuralXorPredicate.read event
  let _ ← StructuralXorPredicate.check original steps
  return ()

private def failure (source : String) (steps : List Step) : Option Finite.Error :=
  match ((checkOriginal source steps).run exactWorkLimit).1 with
  | .ok _ => none
  | .error error => some error

#guard failure source (circuit 3 [0,2]) == none
#guard failure source (circuit 3 [0,1]) == some .equation
#guard failure source (circuit 3 [0,2] 4) == some .equation
#guard failure (source.replace "a and b" "a xor b") (circuit 3 [0,2]) == some .equation
#guard failure (source.replace "both(lo,hi)" "both(lo,lo)") (circuit 3 [0]) == none
#guard failure (source.replace "both(lo,hi)" "both(lo,lo)") (circuit 3 [0,0]) == some .equation

private def actual (steps : List Step) (basis : Semantics.FiniteCarrier.Basis) : Finite.WorkM (List Nat) := do
  let checked ← SourceRuntimeTrace.read #[("main",source)] "main" "route"
  let [Event.computed event _] := checked.events | throw .request
  let original ← StructuralXorPredicate.read event
  let combined : Semantics.SourceOwners.Owner := ⟨2,basis⟩
  let spectator : Semantics.SourceOwners.Owner := ⟨3,[.unit]⟩
  let input : Semantics.Raw.Port := ⟨10,[6,2,4,8],4⟩
  let untouched : Semantics.Raw.Port := ⟨11,[],0⟩
  let program : Semantics.Observation.Program := ⟨[input,untouched],[],
    [.pure (.applyUnitary 10 12 steps)],[12,11],[],.unitary⟩
  let prepared ← RuntimeInterval.prepare [] program
  let interval ← RuntimeInterval.check prepared.block 0 1
  let receipt ← StructuralXorInterval.read original interval [⟨combined,input⟩,⟨spectator,untouched⟩] combined
  return receipt.output.wires

private def combinedBasis : Semantics.FiniteCarrier.Basis := [.pair,.tuple 3,.bit,.bits 1,.bit,.bit]

#guard ((actual (circuit 3 [0,2]) combinedBasis).run exactWorkLimit).1.toOption = some [6,2,4,8]
#guard ((actual (circuit 3 [0,1]) combinedBasis).run exactWorkLimit).1.toOption.isNone
#guard ((actual (circuit 3 [0,2]) [.bits 4]).run exactWorkLimit).1.toOption.isNone

private def wordPredicate (width value : Nat) : Finite.WorkM (List (List Control)) := do
  let result ← StructuralXorPredicate.compile [.bits 0 width] (.equalsOrdinal value (.input 0))
  return result.clauses

#guard ((wordPredicate 3 5).run 128).1.toOption = some [[⟨0,true⟩,⟨1,false⟩,⟨2,true⟩]]
#guard ((wordPredicate 3 8).run 128).1.toOption.isNone

end QleisliKernel.Tests.StructuralXorPredicate
