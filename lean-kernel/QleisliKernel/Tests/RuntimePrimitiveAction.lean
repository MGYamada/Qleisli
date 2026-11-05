import QleisliKernel.Qirf.RuntimePrimitiveAction

/-! Small exact primitive controls independent of instruction counts.
Original source resolution and full body correspondence remain separate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.RuntimePrimitiveAction
open QleisliKernel QleisliKernel.Finite QleisliKernel.Qirf

private def hThree : Semantics.Observation.Program :=
  ⟨[⟨0,[0],1⟩],[],[.pure (.gate .h 0 1),.pure (.gate .h 1 2),.pure (.gate .h 2 3)],
    [3],[],.unitary⟩

private def checkH : WorkM Unit := do
  let root ← RuntimeInterval.prepare [] hThree
  let _ ← RuntimePrimitiveAction.check root.block 0 3 0 3 ⟨0,[.bit]⟩ .h
  return ()

#guard checkH.run 1000000 |>.1.toOption.isSome

private def identity : Semantics.Observation.Program := ⟨[⟨0,[0],1⟩],[],[],[0],[],.unitary⟩

private def checkPhase (exponent : Nat) : WorkM Unit := do
  let root ← RuntimeInterval.prepare [] identity
  let _ ← RuntimePrimitiveAction.check root.block 0 0 0 0 ⟨0,[.bit]⟩ (.phase exponent)
  return ()

-- A literal identity has zero operations. Full phase still distinguishes it
-- from a phase-four source event.
#guard (checkPhase 0).run 1000000 |>.1.toOption.isSome
#guard (match (checkPhase 4).run 1000000 with
  | (.error .equation,_) => true
  | _ => false)

private def scalar (exponent : Nat) : Semantics.Observation.Program :=
  ⟨[⟨0,[],0⟩],[],[.pure (.applyUnitary 0 1 [⟨[],.monomial [] [0] [exponent]⟩])],
    [1],[],.unitary⟩

private def checkScalar (exponent : Nat) : WorkM Unit := do
  let root ← RuntimeInterval.prepare [] (scalar exponent)
  let _ ← RuntimePrimitiveAction.check root.block 0 1 0 1 ⟨0,[.unit]⟩ .globalPhaseEighth
  return ()

#guard (checkScalar 1).run 1000000 |>.1.toOption.isSome
#guard (match (checkScalar 0).run 1000000 with
  | (.error .equation,_) => true
  | _ => false)

end QleisliKernel.Tests.RuntimePrimitiveAction
