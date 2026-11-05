import QleisliKernel.Qirf.RuntimeLocalEvents
import QleisliKernel.Raw.Trace
import QleisliKernel.Raw.Observation

/-! The actual observing interval supplies its complete pure Raw trace.
Successful checkStep/checkOps runs imply the independent no-finish trace, with
all original event boundaries and the exact final caller interface. No trace,
reader-success flag, lowering form, source owner code or replacement program
is supplied. Selected-fragment localization and full forest codes are separate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeIntervalTrace
open QleisliKernel QleisliKernel.Finite QleisliKernel.Qirf
open QleisliKernel.Semantics.Finite

private theorem checkStep_pure_reference (dependencies : List Dependency)
    (recurse : Raw.Observation.State → List Semantics.Observation.Op → WorkM Raw.Observation.State)
    (before after : Raw.Observation.State) (operation : Semantics.Raw.Op) (work left : Nat)
    (ok : (Raw.Observation.checkStep dependencies recurse before (.pure operation)).run work = (.ok after,left)) :
    ∃ events, Semantics.RawTrace.step before.quantum.reference operation = some (after.quantum.reference,events) := by
  unfold Raw.Observation.checkStep at ok
  obtain ⟨_,w₁,_,h⟩ := bind_success _ _ _ _ _ ok
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
  exact ⟨transition.events,Raw.step_reference _ _ _ _ (lift_success _ _ _ _ step).1⟩

/-- The prefix and inputBits are arbitrary bookkeeping from the same original
trace fold. Each genuine advance appends its actual entire event list; no event
is flattened, discarded, reassociated or replaced by an aggregate circuit. -/
private theorem fold_pure_trace (dependencies : List Dependency)
    (recurse : Raw.Observation.State → List Semantics.Observation.Op → WorkM Raw.Observation.State)
    (operations : List Semantics.Raw.Op) (before after : Raw.Observation.State)
    (earlier : List Semantics.Raw.Event) (bits work left : Nat)
    (ok : ((operations.map Semantics.Observation.Op.pure).foldlM
      (Raw.Observation.checkStep dependencies recurse) before).run work = (.ok after,left)) :
    ∃ events, operations.foldlM Semantics.RawTrace.advance ⟨before.quantum.reference,earlier,bits⟩ =
      some ⟨after.quantum.reference,events,bits⟩ := by
  induction operations generalizing before earlier work with
  | nil =>
    have same := (pure_success _ _ _ _ ok).1
    subst after
    exact ⟨earlier,rfl⟩
  | cons operation operations ih =>
    simp only [List.map_cons,List.foldlM_cons] at ok
    obtain ⟨next,middle,first,rest⟩ := bind_success _ _ _ _ _ ok
    obtain ⟨added,step⟩ := checkStep_pure_reference dependencies recurse before next operation work middle first
    obtain ⟨events,tail⟩ := ih next (earlier ++ added) middle rest
    refine ⟨events,?_⟩
    simpa only [List.foldlM_cons,Semantics.RawTrace.advance,step,bind,Option.bind,pure] using tail

/-- Success of the original budgeted checkOps on pure original operations
supplies a successful independent trace. The trace has no synthetic finish;
its state and inputBits remain those of this same caller interval. -/
theorem checkOps_pure_trace (dependencies : List Dependency) (fuel : Nat)
    (before after : Raw.Observation.State) (operations : List Semantics.Raw.Op) (work left : Nat)
    (ok : (Raw.Observation.checkOps dependencies fuel before
      (operations.map Semantics.Observation.Op.pure)).run work = (.ok after,left)) :
    ∃ events, RuntimeLocalEvents.trace before.quantum.reference operations =
      some ⟨after.quantum.reference,events,before.quantum.frame.length⟩ := by
  cases fuel with
  | zero => cases ok
  | succ fuel =>
    unfold Raw.Observation.checkOps at ok
    obtain ⟨checked,middle,folded,h⟩ := bind_success _ _ _ _ _ ok
    obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
    have same := (pure_success _ _ _ _ h).1
    subst after
    obtain ⟨events,traced⟩ := fold_pure_trace dependencies _ operations before checked []
      before.quantum.frame.length work middle folded
    exact ⟨events,traced⟩

/-- A real checked pure interval retains both the original operation list and
its actual observing-reader invocation. These receipts derive the whole caller
trace and afterState fields without assuming a Literal/readSource result. -/
theorem interval_trace {dependencies program block arity start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block arity start count inputs outputs roles) :
    ∃ traceResult, RuntimeLocalEvents.trace frame.interval.before.quantum.reference frame.operations = some traceResult ∧
      traceResult.state = frame.interval.after.quantum.reference ∧
      traceResult.inputBits = frame.interval.before.quantum.frame.length := by
  obtain ⟨work,left,ran⟩ := frame.interval.intervalRead
  rw [frame.literal] at ran
  obtain ⟨events,traced⟩ := checkOps_pure_trace dependencies block.fuel frame.interval.before frame.interval.after
    frame.operations work left ran
  exact ⟨⟨frame.interval.after.quantum.reference,events,frame.interval.before.quantum.frame.length⟩,traced,rfl,rfl⟩

#print axioms checkOps_pure_trace
#print axioms interval_trace

end Qleisli.RuntimeIntervalTrace
