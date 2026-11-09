import Qleisli.RuntimeCallHistoryFold
import Qleisli.RuntimeOriginalBranch

/-! Read both actual arms and the complete quantum phi guard from a native
branch step. The result remains indexed by the original checked instruction.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeCallHistory
open QleisliKernel QleisliKernel.Qirf
open QleisliKernel.Finite (bind_success guard_success)
open Semantics.Finite (Dependency)
open Semantics.Observation (Op Event QuantumPhi ClassicalPhi readOps phiInterface)
open Raw.Observation (checkStep checkOps enter phiValid)
open Raw.ObservationAgreement (readStep)
open RuntimeOriginalBranch (armFinish)

structure BranchRead (dependencies : List Dependency) (depth : Nat) (before : Raw.Observation.State)
    (thenOps elseOps : List Op) (phis : List QuantumPhi) where
  thenState : Raw.Observation.State
  elseState : Raw.Observation.State
  thenRead : RuntimeInterval.Computed (checkOps dependencies depth (enter before) thenOps) thenState
  elseRead : RuntimeInterval.Computed (checkOps dependencies depth
    (RuntimeInterval.rightEntry before thenState) elseOps) elseState
  phisValid : phiValid thenState.quantum elseState.quantum phis = true

/-- Both arm checks and the actual phi guard are premises of the original
successful branch. Extract their results from that exact native step. -/
theorem branch_read {dependencies : List Dependency} {depth : Nat} {before after : Raw.Observation.State}
    {condition : Nat} {thenOps elseOps : List Op} {quantum : List QuantumPhi} {classical : List ClassicalPhi}
    (native : RuntimeInterval.Computed
      (checkStep dependencies (checkOps dependencies depth) before (.branch condition thenOps elseOps quantum classical))
      after) :
    Nonempty (BranchRead dependencies depth before thenOps elseOps quantum) := by
  obtain ⟨work,left,ran⟩ := native
  obtain ⟨_,_,_,afterCharge⟩ := bind_success _ _ _ _ _ ran
  obtain ⟨_,_,_,afterEntry⟩ := bind_success _ _ _ _ _ afterCharge
  obtain ⟨_,_,body,_⟩ := bind_success _ _ _ _ _ afterEntry
  simp only [Raw.Observation.checkAction] at body
  obtain ⟨_,_,_,body⟩ := bind_success _ _ _ _ _ body
  obtain ⟨_,_,_,body⟩ := bind_success _ _ _ _ _ body
  obtain ⟨yes,_,yesRead,body⟩ := bind_success _ _ _ _ _ body
  obtain ⟨no,_,noRead,body⟩ := bind_success _ _ _ _ _ body
  obtain ⟨_,_,guard,_⟩ := bind_success _ _ _ _ _ body
  exact ⟨⟨yes,no,⟨_,_,yesRead⟩,⟨_,_,noRead⟩,(guard_success _ _ _ _ guard).1⟩⟩

/-- The actual independent reader emits both arm bodies and their exact
written output permutations. The post-frame is the native result. -/
theorem BranchRead.events {dependencies : List Dependency} {depth : Nat} {before after : Raw.Observation.State}
    {thenOps elseOps : List Op} {quantum : List QuantumPhi}
    (arms : BranchRead dependencies depth before thenOps elseOps quantum)
    {condition : Nat} {classical : List ClassicalPhi} {events thenEvents elseEvents : List Event}
    (literal : readStep (readOps depth) before.quantum.reference (.branch condition thenOps elseOps quantum classical) =
      some (after.quantum.reference,events))
    (yes : readOps depth (enter before).quantum.reference thenOps = some (arms.thenState.quantum.reference,thenEvents))
    (no : readOps depth (RuntimeInterval.rightEntry before arms.thenState).quantum.reference elseOps =
      some (arms.elseState.quantum.reference,elseEvents)) :
    after.quantum.reference = phiInterface quantum ∧
      events = [.branch condition (thenEvents++[armFinish arms.thenState.quantum.reference quantum true])
        (elseEvents++[armFinish arms.elseState.quantum.reference quantum false]) classical] := by
  change readOps depth before.quantum.reference thenOps = _ at yes
  change readOps depth before.quantum.reference elseOps = _ at no
  have shape : readStep (readOps depth) before.quantum.reference (.branch condition thenOps elseOps quantum classical) =
      some (phiInterface quantum,[.branch condition (thenEvents++[armFinish arms.thenState.quantum.reference quantum true])
        (elseEvents++[armFinish arms.elseState.quantum.reference quantum false]) classical]) := by
    simp [readStep,yes,no,armFinish]
  exact Prod.mk.inj (Option.some.inj (literal.symm.trans shape))

#print axioms branch_read
#print axioms BranchRead.events
end Qleisli.RuntimeCallHistory
