import Qleisli.RuntimeCallBranchAction
import Qleisli.RuntimeCallPureStepLaw

/-! The original branch checks supply both exact recursive arm runs.
The branch law closes by decreasing the caller's original reader depth.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeCallHistory
open QleisliKernel QleisliKernel.Qirf
open Semantics.Finite (Dependency)
open Semantics.Raw (Port)
open Semantics.RawTrace (axes)
open Semantics.Observation (Op Event QuantumPhi ClassicalPhi phiWires phiInterface)
open Raw.Observation (checkOps)
open RuntimeCallTraceFrames (Partition)
open RuntimeOriginalBranch (armFinish)

private theorem positive_depth {dependencies : List Dependency} {depth : Nat}
    {before after : Raw.Observation.State} {ops : List Op}
    (native : RuntimeInterval.Computed (checkOps dependencies depth before ops) after) :
    ∃ smaller, depth = smaller+1 := by
  cases depth with
  | zero =>
    obtain ⟨_,_,failed⟩ := native
    cases failed
  | succ smaller => exact ⟨smaller,rfl⟩

private theorem checked_valid {dependencies : List Dependency} {depth : Nat}
    {before after : Raw.Observation.State} {ops : List Op}
    (native : RuntimeInterval.Computed (checkOps dependencies depth before ops) after) :
    Raw.stateValid after.quantum = true := by
  obtain ⟨work,left,ran⟩ := native
  exact (Raw.Observation.checkOps_invariants _ _ _ _ _ work left ran).1

private theorem branch_step_law {dependencies : List Dependency} {parentDepth childDepth : Nat}
    {spectators : List Port} (condition : Nat) (thenOps elseOps : List Op)
    (quantum : List QuantumPhi) (classical : List ClassicalPhi)
    (smaller : ∀ p c, parentDepth = p+1 → childDepth = c+1 →
      ∀ op, StepLaw dependencies p c spectators op) :
    StepLaw dependencies parentDepth childDepth spectators (.branch condition thenOps elseOps quantum classical) := by
  intro parent child pAfter cAfter pEvents cEvents pNative cNative pLiteral cLiteral partition
  obtain ⟨pArms⟩ := branch_read pNative
  obtain ⟨cArms⟩ := branch_read cNative
  obtain ⟨pd,pDepth⟩ := positive_depth pArms.thenRead
  obtain ⟨cd,cDepth⟩ := positive_depth cArms.thenRead
  subst parentDepth
  subst childDepth
  obtain ⟨pThen,cThen,pYesRead,cYesRead,yes⟩ :=
    checked_operations thenOps pArms.thenRead cArms.thenRead partition (fun op _ => smaller pd cd rfl rfl op)
  obtain ⟨pElse,cElse,pNoRead,cNoRead,no⟩ :=
    checked_operations elseOps pArms.elseRead cArms.elseRead partition (fun op _ => smaller pd cd rfl rfl op)
  have empty := complete_phi_has_no_spectators quantum pArms.phisValid cArms.phisValid yes.partition.live
  subst spectators
  obtain ⟨pFrame,pShape⟩ := pArms.events pLiteral pYesRead pNoRead
  obtain ⟨cFrame,cShape⟩ := cArms.events cLiteral cYesRead cNoRead
  have finalUnique : (phiInterface quantum).frame.Nodup := by
    rw [← pFrame]
    obtain ⟨_,_,read⟩ := pNative
    exact (Raw.Ownership.valid _ (Qleisli.RuntimeObservingPrefix.checkStep_frames_valid read).2).frame
  have finish (choice : Bool) :
      let pArm := (if choice then pArms.thenState else pArms.elseState).quantum.reference
      let cArm := (if choice then cArms.thenState else cArms.elseState).quantum.reference
      Segment dependencies pd cd parent.quantum.reference child.quantum.reference
        (phiInterface quantum) (phiInterface quantum) []
        ((if choice then pThen else pElse) ++ [armFinish pArm quantum choice])
        ((if choice then cThen else cElse) ++ [armFinish cArm quantum choice]) := by
    intro pArm cArm
    have arm : Segment dependencies pd cd parent.quantum.reference child.quantum.reference pArm cArm []
        (if choice then pThen else pElse) (if choice then cThen else cElse) := by
      cases choice
      · exact no
      · exact yes
    let pQuantum := (if choice then pArms.thenState else pArms.elseState).quantum
    let cQuantum := (if choice then cArms.thenState else cArms.elseState).quantum
    have pSide : pQuantum = if choice then pArms.thenState.quantum else pArms.elseState.quantum := by
      cases choice <;> rfl
    have cSide : cQuantum = if choice then cArms.thenState.quantum else cArms.elseState.quantum := by
      cases choice <;> rfl
    have pValid : Raw.stateValid pQuantum = true := by
      cases choice
      · exact checked_valid pArms.elseRead
      · exact checked_valid pArms.thenRead
    have cValid : Raw.stateValid cQuantum = true := by
      cases choice
      · exact checked_valid cArms.elseRead
      · exact checked_valid cArms.thenRead
    exact arm.finish_arm
      (.reorder pArm.frame.length (axes pArm (phiWires pArm quantum choice)))
      (.reorder cArm.frame.length (axes cArm (phiWires cArm quantum choice)))
      (fun _ _ same => paired_phi_reorder quantum choice pArms.phisValid cArms.phisValid
        pSide cSide pValid cValid arm.partition finalUnique same)
  rw [pFrame,cFrame,pShape,cShape]
  exact branch_from_arms condition classical (finish true) (finish false)

/-- Every original checked instruction has the paired local law. Branches
use the same law on both actually checked arms at their smaller depths. -/
theorem operation_step_law (dependencies : List Dependency) (parentDepth childDepth : Nat)
    (spectators : List Port) (op : Op) :
    StepLaw dependencies parentDepth childDepth spectators op := by
  cases op with
  | pure operation => exact pure_step_law dependencies parentDepth childDepth spectators operation
  | measure input output => exact erasure_step_law dependencies parentDepth childDepth spectators input (some output)
  | discard input => exact erasure_step_law dependencies parentDepth childDepth spectators input none
  | reset input output wire => exact reset_step_law dependencies parentDepth childDepth spectators input output wire
  | constant value output => exact constant_step_law dependencies parentDepth childDepth spectators value output
  | not input output => exact not_step_law dependencies parentDepth childDepth spectators input output
  | xor left right output => exact xor_step_law dependencies parentDepth childDepth spectators left right output
  | and left right output => exact and_step_law dependencies parentDepth childDepth spectators left right output
  | branch condition thenOps elseOps quantum classical =>
    exact branch_step_law condition thenOps elseOps quantum classical
      (fun p c pDepth _ next => operation_step_law dependencies p c spectators next)
termination_by parentDepth
decreasing_by omega

#print axioms operation_step_law
end Qleisli.RuntimeCallHistory
