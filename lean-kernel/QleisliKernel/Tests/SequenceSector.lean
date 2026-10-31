import QleisliKernel.Qirf.SequenceSector
import QleisliKernel.SourceTypes.Lexer

/-! Small complete-graph executable sequence controls. Both source selections
apply the same controlled Z and cancel globally; each original interval still
needs its own exact arm/control/sector check. These are bounded observations,
not source/native-runtime preservation proofs. At most two physical bits.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SequenceSector
open Semantics Semantics.Raw Semantics.FiniteCarrier Semantics.CarrierInterface
open Qirf.SequenceSector

def selection := "qmatch(s,q){Tag::B=>sign,Tag::A=>keep}"
def text := "// λ qmatch is not a comment site\npub enum Tag{A,B} " ++
  "unitary fn keep(q:Q<Bit>)->Q<Bit>{q} unitary fn sign(q:Q<Bit>)->Q<Bit>{phase[1,1](q)} " ++
  "pub unitary fn route(s:Q<Tag>,q:Q<Bit>,u:Q<Unit>)->(Q<Unit>,Q<Tag>,Q<Bit>){let(s,q)=" ++ selection ++
  ";let(s,q)=" ++ selection ++ ";(u,s,q)}"
def tag : Basis := [.enumeration ⟨"main","Tag",text⟩ ["A","B"]]
def offsets := SourceTypes.QuantumSequence.originalOffsets ((SourceTypes.lexLocated text).toOption.getD [])

def phaseStep (phase : Nat) : Semantics.Finite.Step := ⟨[⟨0,true⟩],.monomial [1] [0,1] [0,phase]⟩
def main (first second : Nat := 4) : Observation.Program :=
  ⟨[⟨0,[0],1⟩,⟨1,[1],1⟩,⟨2,[],0⟩],[],
    [.pure (.join 0 1 3),.pure (.applyUnitary 3 4 [phaseStep first]),.pure (.split 4 5 6 1),
      .pure (.join 5 6 7),.pure (.applyUnitary 7 8 [phaseStep second]),.pure (.split 8 9 10 1)],
    [2,9,10],[],.unitary⟩
def arm (phase : Nat) : Observation.Program :=
  ⟨[⟨10,[7],1⟩],[],[.pure (.applyUnitary 10 11 [⟨[],.monomial [0] [0,1] [0,phase]⟩])],[11],[],.unitary⟩
def controlled (phase : Nat) : Observation.Program :=
  ⟨[⟨10,[7],1⟩,⟨11,[91],1⟩],[],[.pure (.join 10 11 12),
    .pure (.applyUnitary 12 13 [phaseStep phase]),.pure (.split 13 14 15 1)],[14,15],[],.unitary⟩
def artifact : Qirf.Artifact :=
  ⟨#[main,arm 0,controlled 0,arm 4,controlled 4],
    #[⟨[.bit],1,.phase8 [0,0],"main::keep","independent::identity",[0]⟩,
      ⟨[.bit],3,.phase8 [0,4],"main::sign","independent::z",[0]⟩],#[("main",text)],0,none⟩
def order : Array Nat := #[1,2,3,4,5,6,0]

def interface (second : Bool) : Interface :=
  ⟨[⟨⟨if second then 5 else 0,[0],1⟩,tag⟩,⟨⟨if second then 6 else 1,[1],1⟩,[.bit]⟩],
    [⟨⟨if second then 9 else 5,[0],1⟩,tag⟩,⟨⟨if second then 10 else 6,[1],1⟩,[.bit]⟩],.unitary⟩
def firstRequest : Request :=
  ⟨interface false,interface false,⟨offsets[0]?.getD 0,0,3⟩,[⟨1,4⟩,⟨0,2⟩]⟩
def secondRequest : Request :=
  ⟨interface true,interface true,⟨offsets[1]?.getD 0,3,3⟩,[⟨1,4⟩,⟨0,2⟩]⟩
def requests : List Request := [firstRequest,secondRequest]

def result (data : Qirf.Artifact := artifact) (asked : List Request := requests) : Except Finite.Error (List Nat) :=
  ((Qirf.SequenceSector.check data order "main" "route" asked).run 10000000).1.map fun checked =>
    checked.locals.map (·.logical.length)
def failure (data : Qirf.Artifact := artifact) (asked : List Request := requests) : Option Finite.Error :=
  match result data asked with | .error error => some error | .ok _ => none

def controls : List (String × Bool) := [
  ("both actual source intervals pass the exact complete-graph gate",(result).toOption == some [2,2]),
  ("a valid wrong first phase reaches the exact equation refusal",
    failure {artifact with programs := artifact.programs.set! 0 (main 2 4)} == some .equation),
  ("a valid wrong second phase reaches the exact equation refusal",
    failure {artifact with programs := artifact.programs.set! 0 (main 4 2)} == some .equation),
  ("cancelling wrong intervals cannot borrow the correct final identity",
    failure {artifact with programs := artifact.programs.set! 0 (main 0 0)} == some .equation),
  ("the original arm body is checked against its exact specification",
    failure {artifact with programs := artifact.programs.set! 3 (arm 2)} == some .equation),
  ("a valid wrong controlled body reaches the exact equation refusal",
    failure {artifact with programs := artifact.programs.set! 4 (controlled 2)} == some .equation),
  ("a missing second original selection refuses",(failure artifact (requests.take 1)).isSome),
  ("reordered actual source requests refuse",(failure artifact requests.reverse).isSome),
  ("duplicated occurrence cannot replace the second request",
    (failure artifact [firstRequest,firstRequest]).isSome),
  ("an arm evidence index cannot name another original source function",
    (failure artifact [{firstRequest with programs := [⟨0,2⟩,⟨0,2⟩]},secondRequest]).isSome),
  ("invalid control index does not grant access",
    (failure artifact [{firstRequest with programs := [⟨1,0⟩,⟨0,2⟩]},secondRequest]).isSome),
  ("zero-width caller owner cannot disappear",
    (failure {artifact with programs := artifact.programs.set! 0 {main with outputs := [9,10]}}).isSome),
  ("outer output order is checked independently of physical widths",
    (failure {artifact with programs := artifact.programs.set! 0 {main with outputs := [9,2,10]}}).isSome),
  ("public Unitary cannot hide an Observe root",
    (failure {artifact with programs := artifact.programs.set! 0 {main with effect := .observe}}).isSome),
  ("an unrelated source row is not a checked dependency",
    (failure {artifact with sources := artifact.sources.push ("unrelated","fn unused()->Unit{()}")}).isSome)]

example : controls.length = 15 := by decide +kernel
#guard controls.all (·.2)

end QleisliKernel.Tests.SequenceSector
