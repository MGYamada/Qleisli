import QleisliKernel.Qirf.PrimitiveAction

/-! Bounded literal-action controls, with at most three physical bits. The first
observation is separately retained; the refined gate now rejects that port-width
mismatch. Neither version supplies original source/callee/frame association.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.PrimitiveActionTests
open QleisliKernel.Qirf
open QleisliKernel.SourceTypes
open QleisliKernel QleisliKernel.Semantics PrimitiveAction

def scalar (bits : Nat) (wires : List Nat) (phase : Nat) : Observation.Program :=
  ⟨[⟨10,wires,bits⟩,⟨11,[],0⟩],[],
    [.pure (.applyUnitary 10 13 [⟨[],.monomial [] [0] [phase]⟩])],[13,11],[],.unitary⟩

def accepted (program : Observation.Program) (start count input output : Nat)
    (role : SourceOwners.Owner) (kind : Kind) : Bool :=
  ((check [] program start count input output role kind).run 100000).1.toOption.isSome

def oneH : Observation.Program :=
  ⟨[⟨10,[7],1⟩,⟨11,[],0⟩],[],[.pure (.gate .h 10 13)],[13,11],[],.unitary⟩

def observingPrefix : Observation.Program :=
  ⟨[⟨10,[7],1⟩,⟨11,[],0⟩,⟨12,[5],1⟩],[],
    [.measure 12 0,.pure (.gate .h 10 13)],[13,11],[0],.observe⟩

-- The original component accepted the first mismatched role in the retained
-- primitive-action-first run. The refined input/output port check rejects it.
#guard !accepted (scalar 1 [7] 1) 0 1 10 13 ⟨0,[.unit]⟩ .globalPhaseEighth
#guard accepted (scalar 0 [] 1) 0 1 10 13 ⟨0,[.unit]⟩ .globalPhaseEighth
#guard accepted (scalar 1 [7] 1) 0 1 10 13 ⟨0,[.bit]⟩ .globalPhaseEighth
#guard accepted (scalar 3 [7,3,5] 1) 0 1 10 13 ⟨0,[.bits 3]⟩ .globalPhaseEighth
#guard !accepted (scalar 0 [] 1) 0 1 10 13 ⟨0,[.bit]⟩ .globalPhaseEighth
#guard !accepted (scalar 1 [7] 2) 0 1 10 13 ⟨0,[.bit]⟩ .globalPhaseEighth
#guard !accepted (scalar 1 [7] 7) 0 1 10 13 ⟨0,[.bit]⟩ .globalPhaseEighth
#guard !accepted (scalar 0 [] 1) 0 1 11 13 ⟨0,[.unit]⟩ .globalPhaseEighth
#guard !accepted (scalar 0 [] 1) 0 1 10 11 ⟨0,[.unit]⟩ .globalPhaseEighth
#guard !accepted (scalar 0 [] 1) 0 1 10 13 ⟨0,[]⟩ .globalPhaseEighth
#guard !accepted (scalar 1 [7] 1) 0 1 10 13 ⟨0,[.pair,.bit]⟩ .globalPhaseEighth
#guard accepted oneH 0 1 10 13 ⟨0,[.bit]⟩ .h
#guard !accepted oneH 0 1 10 13 ⟨0,[.bits 1]⟩ .h
#guard !accepted oneH 0 1 10 13 ⟨0,[.unit]⟩ .h
#guard !accepted {oneH with operations := [.pure (.gate .x 10 13)]}
  0 1 10 13 ⟨0,[.bit]⟩ .h
#guard !accepted {oneH with outputs := [13]} 0 1 10 13 ⟨0,[.bit]⟩ .h
#guard !accepted oneH 0 0 10 13 ⟨0,[.bit]⟩ .h
#guard accepted observingPrefix 1 1 10 13 ⟨0,[.bit]⟩ .h
#guard !accepted {observingPrefix with effect := .unitary} 1 1 10 13 ⟨0,[.bit]⟩ .h
#guard !accepted observingPrefix 0 1 10 13 ⟨0,[.bit]⟩ .h

#print axioms QleisliKernel.Qirf.PrimitiveAction.check
#print axioms QleisliKernel.Qirf.PrimitiveAction.Checked.originalInstruction
#print axioms QleisliKernel.Qirf.PrimitiveAction.Checked.hRequiresBit

end QleisliKernel.Tests.PrimitiveActionTests
