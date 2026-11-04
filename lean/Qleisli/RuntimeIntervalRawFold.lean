import QleisliKernel.Qirf.RuntimePureInterval
import QleisliKernel.Raw.Trace
import QleisliKernel.Raw.Observation

/-! Actual Raw fold receipts from the same original observing interval reader.
The retained checkOps run contains each lifted native Raw.step and all event
checks, ordinary scope/history guards and original budget positions. This proof
extracts those receipts without rerunning any checker. The entry may already
have observe = true; no surrounding effect or hidden history is discarded.
Local sector preparation and trace localization remain separate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeIntervalRawFold
open QleisliKernel QleisliKernel.Finite QleisliKernel.Qirf
open QleisliKernel.Semantics.Finite

private theorem checkStep_pure_raw (dependencies : List Dependency)
    (recurse : Raw.Observation.State → List Semantics.Observation.Op → WorkM Raw.Observation.State)
    (before after : Raw.Observation.State) (operation : Semantics.Raw.Op) (work left : Nat)
    (read : (Raw.Observation.checkStep dependencies recurse before (.pure operation)).run work = (.ok after,left)) :
    ∃ transition, Raw.step (dependencies.map (·.signature)) before.quantum operation = .ok transition ∧
      after = {before with quantum := transition.state} := by
  unfold Raw.Observation.checkStep at read
  obtain ⟨_,w₁,_,h⟩ := bind_success _ _ _ _ _ read
  obtain ⟨_,w₂,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨checked,w₃,action,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₄,_,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst after
  simp only [Raw.Observation.checkAction] at action
  obtain ⟨_,w₅,_,h⟩ := bind_success _ _ _ _ _ action
  obtain ⟨transition,w₆,step,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₇,_,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst checked
  exact ⟨transition,(lift_success _ _ _ _ step).1,rfl⟩

/-- Prefix events and inputBits are bookkeeping from the same Raw fold.
Every actual transition appends its entire original event list, including an
empty circuit event. The observing state is never replaced by a pure entry. -/
private theorem fold_pure_raw (dependencies : List Dependency)
    (recurse : Raw.Observation.State → List Semantics.Observation.Op → WorkM Raw.Observation.State)
    (operations : List Semantics.Raw.Op) (before after : Raw.Observation.State)
    (earlier : List Semantics.Raw.Event) (bits work left : Nat)
    (read : ((operations.map Semantics.Observation.Op.pure).foldlM
      (Raw.Observation.checkStep dependencies recurse) before).run work = (.ok after,left)) :
    ∃ events, operations.foldlM (Raw.advance (dependencies.map (·.signature)))
      ⟨before.quantum,earlier,bits⟩ = .ok ⟨after.quantum,events,bits⟩ := by
  induction operations generalizing before earlier work with
  | nil =>
    have same := (pure_success _ _ _ _ read).1
    subst after
    exact ⟨earlier,rfl⟩
  | cons operation operations ih =>
    simp only [List.map_cons,List.foldlM_cons] at read
    obtain ⟨next,middle,first,rest⟩ := bind_success _ _ _ _ _ read
    obtain ⟨transition,step,nextState⟩ :=
      checkStep_pure_raw dependencies recurse before next operation work middle first
    obtain ⟨events,tail⟩ := ih next (earlier ++ transition.events) middle rest
    have nextQuantum : next.quantum = transition.state := congrArg Raw.Observation.State.quantum nextState
    rw [nextQuantum] at tail
    refine ⟨events,?_⟩
    simpa only [List.foldlM_cons,Raw.advance,step,bind,Except.bind,pure,Except.pure] using tail

/-- The original budgeted pure-operation checkOps receipt supplies a genuine
Raw.advance fold with the exact original before/after quantum states. All
budgets here are the retained run's positions, not a new checker invocation. -/
theorem checkOps_pure_raw_fold (dependencies : List Dependency) (fuel : Nat)
    (before after : Raw.Observation.State) (operations : List Semantics.Raw.Op) (work left : Nat)
    (read : (Raw.Observation.checkOps dependencies fuel before
      (operations.map Semantics.Observation.Op.pure)).run work = (.ok after,left)) :
    ∃ events, operations.foldlM (Raw.advance (dependencies.map (·.signature)))
      ⟨before.quantum,[],before.quantum.frame.length⟩ =
        .ok ⟨after.quantum,events,before.quantum.frame.length⟩ := by
  cases fuel with
  | zero => cases read
  | succ fuel =>
    unfold Raw.Observation.checkOps at read
    obtain ⟨checked,middle,folded,h⟩ := bind_success _ _ _ _ _ read
    obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
    have same := (pure_success _ _ _ _ h).1
    subst after
    exact fold_pure_raw dependencies _ operations before checked [] before.quantum.frame.length work middle folded

/-- The same original interval literal fixes the operation list and both
native quantum states. Its entry can be inside an already observing body. -/
theorem interval_raw_fold {dependencies program block arity start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block arity start count inputs outputs roles) :
    ∃ events, frame.operations.foldlM (Raw.advance (dependencies.map (·.signature)))
      ⟨frame.interval.before.quantum,[],frame.interval.before.quantum.frame.length⟩ =
        .ok ⟨frame.interval.after.quantum,events,frame.interval.before.quantum.frame.length⟩ := by
  obtain ⟨work,left,read⟩ := frame.interval.intervalRead
  rw [frame.literal] at read
  exact checkOps_pure_raw_fold dependencies block.fuel frame.interval.before frame.interval.after frame.operations work left read

#print axioms checkOps_pure_raw_fold
#print axioms interval_raw_fold

end Qleisli.RuntimeIntervalRawFold
