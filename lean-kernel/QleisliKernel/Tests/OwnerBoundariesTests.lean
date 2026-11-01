import QleisliKernel.Raw.OwnerBoundaries
import QleisliKernel.Qirf.SourceSequence

/-! Bounded controls use at most two physical bits. Stored boundary proofs bind
the exact reference step; comparison with the previous reader checks both
successful frames and rejected malformed moves. No native acceptance is claimed.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.OwnerBoundariesTests
open QleisliKernel.SourceTypes
open QleisliKernel QleisliKernel.Semantics QleisliKernel.Raw.OwnerBoundaries

def bit (index : Nat) : SourceOwners.Owner := ⟨index,[.bit]⟩
def unit (index : Nat) : SourceOwners.Owner := ⟨index,[.unit]⟩
def port (index : Nat) : Raw.Port := ⟨index,[index],1⟩
def zero (index : Nat) : Raw.Port := ⟨index,[],0⟩

def shape : Nat → RawOwnerFlow.Tree → Option (List (Option SourceOwners.Owner × Nat)) :=
  Nat.rec (fun _ => none) (fun _ next tree => match tree with
    | .owner role bits => some [(some role,bits)]
    | .pair left right bits => do
      return (none,bits)::((← next left) ++ (← next right)))

def view (fuel : Nat) (frame : RawOwnerFlow.Frame) :=
  frame.mapM fun (token,tree) => (shape fuel tree).map fun parts => (token,parts)

def samePrefixes (roles : List SourceOwners.Owner) (inputs : List Raw.Port)
    (operations : List Raw.Op) : Bool :=
  match (check roles inputs operations).run 10000000 with
  | (.error _,_) => false
  | (.ok checked,_) =>
    (List.range (operations.length+1)).all fun offset =>
      match checked.frames[offset]?,
          (Qirf.SourceSequence.frameAt roles inputs operations offset).run 10000000 with
      | some frame,(.ok previous,_) =>
        match view (operations.length+2) frame,view (operations.length+2) previous with
        | some actual,some expected => actual == expected
        | _,_ => false
      | _,_ => false

def refuses (roles : List SourceOwners.Owner) (inputs : List Raw.Port)
    (operations : List Raw.Op) : Bool := !((check roles inputs operations).run 10000000).1.isOk

def manyH : List Raw.Op := (List.range 129).map fun i => .gate .h i (i+1)

def controls : List (String × Bool) := [
  ("empty body retains the initial frame",samePrefixes [bit 0] [port 0] []),
  ("every original H prefix matches the old reader",samePrefixes [bit 0] [port 0] manyH),
  ("two equal-width owners remain distinct",samePrefixes [bit 0,bit 1] [port 0,port 1]
    [.gate .h 1 2,.cnot 0 2 3 4]),
  ("two zero-width owners remain distinct",samePrefixes [unit 0,unit 1] [zero 0,zero 1]
    [.applyUnitary 1 2 [⟨[],.monomial [] [0] [1]⟩]]),
  ("ordered join and split preserve the original leaves",samePrefixes [bit 0,bit 1]
    [port 0,port 1] [.join 1 0 2,.split 2 3 4 1]),
  ("zero-width pair boundaries remain present",samePrefixes [unit 0,unit 1]
    [zero 0,zero 1] [.join 1 0 2,.split 2 3 4 0]),
  ("literal basis wire-list width matches the old reader",samePrefixes [bit 0] [port 0]
    [.liftBasis 0 1 [0] [0,1]]),
  ("wrong basis wire-list width refuses",refuses [bit 0] [port 0]
    [.liftBasis 0 1 [0,1] [0,1]]),
  ("basis wire-list traversal is charged",
    !((check [bit 0] [port 0] [.liftBasis 0 1 [0] [0,1]]).run 2200).1.isOk &&
      ((check [bit 0] [port 0] [.liftBasis 0 1 [0] [0,1]]).run 2208).1.isOk),
  ("missing original owner refuses",refuses [bit 0] [] []),
  ("duplicate input token refuses",refuses [unit 0,unit 1] [zero 0,zero 0] []),
  ("consumed token cannot be reused",refuses [bit 0] [port 0]
    [.gate .h 0 1,.gate .h 0 2]),
  ("move cannot overwrite another live owner",refuses [bit 0,bit 1] [port 0,port 1]
    [.gate .h 0 1]),
  ("equal-width leaf cannot be split",refuses [bit 0] [port 0] [.split 0 1 2 1]),
  ("wrong split width refuses",refuses [unit 0,bit 1] [zero 0,port 1]
    [.join 0 1 2,.split 2 3 4 1]),
  ("allocation has no source-owner fallback",refuses [] [] [.init0 0 0]),
  ("empty work refuses",!((check [bit 0] [port 0] manyH).run 0).1.isOk),
  ("no 128 total-operation cap and bounded shared traversal",
    match (check [bit 0] [port 0] manyH).run 10000000 with
    | (.ok checked,left) => checked.frames.length == 130 && left > 9800000 &&
        checked.frames[130]?.isNone
    | _ => false)
]

#guard controls.all (·.2)
-- Pin the previously observed one-bit traversal work and complete frame count.
#guard (match (QleisliKernel.Raw.OwnerBoundaries.check [bit 0] [port 0] manyH).run 10000000 with
  | (.ok checked,left) => (checked.frames.length,10000000-left)
  | _ => (0,0)) = (130,133272)
#print axioms Checked.originalPrefix
#print axioms QleisliKernel.Raw.OwnerBoundaries.check
end QleisliKernel.Tests.OwnerBoundariesTests
