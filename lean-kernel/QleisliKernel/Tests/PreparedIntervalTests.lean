import QleisliKernel.Tests.ContextIntervalContinuity
import QleisliKernel.Tests.PrimitiveActionTests

/-! Bounded controls for the exact prepared root. At most three physical bits;
no accepted handle or source/algorithm preservation claim.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.PreparedIntervalTests
open QleisliKernel.Qirf
open QleisliKernel.SourceTypes
open QleisliKernel QleisliKernel.Finite QleisliKernel.Semantics
open QleisliKernel.Qirf.PureInterval
open PrimitiveActionTests

def shared (arity : Nat) (program : Observation.Program) (start count : Nat)
    (inputs outputs : List Nat) (roles : List SourceOwners.Owner) :
    WorkM (Many.Checked arity [] program start count inputs outputs roles) := do
  let prepared ← Many.prepare [] program
  Many.checkPrepared arity [] program prepared start count inputs outputs roles

def accepted (arity : Nat) (program : Observation.Program) (start count : Nat)
    (inputs outputs : List Nat) (roles : List SourceOwners.Owner) : Bool :=
  ((shared arity program start count inputs outputs roles).run 100000).1.toOption.isSome

def primitive (program : Observation.Program) (start count input output : Nat)
    (role : SourceOwners.Owner) (kind : PrimitiveAction.Kind) : Bool :=
  ((do
    let prepared ← Many.prepare [] program
    PrimitiveAction.checkPrepared [] program prepared start count input output role kind).run 100000).1.toOption.isSome

def history (program : Observation.Program) (start : Nat) :=
  ((shared 1 program start 1 [10] [13] [⟨0,[.bit]⟩]).run 100000).1.map fun checked =>
    (checked.whole.val.program.effect,checked.whole.val.state.observe,
      checked.before.val.observe,checked.after.val.observe)

def observingSuffix : Observation.Program :=
  {observingPrefix with operations := [.pure (.gate .h 10 13),.measure 12 0]}
def invalidSuffix : Observation.Program :=
  {oneH with operations := [.pure (.gate .h 10 13),.pure (.gate .h 99 14)]}
def touchingSpectator : Observation.Program :=
  {oneH with operations := [.pure (.gate .h 10 13),.pure (.applyUnitary 11 14 [])],outputs := [13,14]}
def three : Observation.Program :=
  ⟨[⟨0,[0],1⟩,⟨1,[2],1⟩,⟨2,[5],1⟩,⟨3,[],0⟩],[],
    [.pure (.toffoli 0 1 2 4 5 6)],[4,5,6,3],[],.unitary⟩

#guard accepted 1 oneH 0 1 [10] [13] [⟨0,[.bit]⟩]
#guard accepted 1 (scalar 0 [] 1) 0 1 [10] [13] [⟨0,[.unit]⟩]
#guard accepted 3 three 0 1 [0,1,2] [4,5,6] [⟨0,[.bit]⟩,⟨1,[.bit]⟩,⟨2,[.bit]⟩]
#guard !accepted 2 oneH 0 1 [10] [13] [⟨0,[.bit]⟩]
#guard !accepted 129 oneH 0 1 [10] [13] [⟨0,[.bit]⟩]
#guard !accepted 1 oneH 2 1 [10] [13] [⟨0,[.bit]⟩]
#guard !accepted 1 oneH 0 1 [99] [13] [⟨0,[.bit]⟩]
#guard !accepted 1 oneH 0 1 [10] [10] [⟨0,[.bit]⟩]
#guard !accepted 1 oneH 0 1 [10] [11] [⟨0,[.bit]⟩]
#guard !accepted 1 {oneH with outputs := [13]} 0 1 [10] [13] [⟨0,[.bit]⟩]
#guard !accepted 1 touchingSpectator 0 2 [10] [13] [⟨0,[.bit]⟩]
#guard !accepted 1 invalidSuffix 0 1 [10] [13] [⟨0,[.bit]⟩]
#guard !accepted 3 three 0 1 [0,1,2] [5,4,6] [⟨0,[.bit]⟩,⟨1,[.bit]⟩,⟨2,[.bit]⟩]
#guard (history observingPrefix 1).toOption == some (.observe,true,true,true)
#guard (history observingSuffix 0).toOption == some (.observe,true,false,false)
#guard !accepted 1 observingSuffix 0 2 [10] [13] [⟨0,[.bit]⟩]
#guard !accepted 1 {observingSuffix with effect := .unitary} 0 1 [10] [13] [⟨0,[.bit]⟩]
#guard !accepted 1 {observingSuffix with effect := .isometry} 0 1 [10] [13] [⟨0,[.bit]⟩]
#guard primitive oneH 0 1 10 13 ⟨0,[.bit]⟩ .h
#guard primitive (scalar 0 [] 1) 0 1 10 13 ⟨0,[.unit]⟩ .globalPhaseEighth
#guard !primitive (scalar 0 [] 2) 0 1 10 13 ⟨0,[.unit]⟩ .globalPhaseEighth
#guard !primitive {oneH with operations := [.pure (.gate .x 10 13)]} 0 1 10 13 ⟨0,[.bit]⟩ .h
#guard !primitive oneH 0 1 10 13 ⟨0,[.bits 1]⟩ .h
#guard ((shared 1 oneH 0 1 [10] [13] [⟨0,[.bit]⟩]).run 0).1.toOption.isNone

-- Checked roots cannot be exchanged even when their port widths agree.
example (_prepared : Many.Prepared [] oneH) : True := by
  fail_if_success have _ : Many.Prepared [] (scalar 1 [7] 1) := _prepared
  trivial
example (left _right : List Finite.Dependency) (_prepared : Many.Prepared left oneH) : True := by
  fail_if_success have _ : Many.Prepared _right oneH := _prepared
  trivial

#print axioms Many.standalone_refinement
#print axioms Many.two_owner_specialization
#print axioms Many.prepare
#print axioms Many.checkPrepared
end QleisliKernel.Tests.PreparedIntervalTests
