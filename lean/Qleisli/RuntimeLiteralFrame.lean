import QleisliKernel.Qirf.RuntimeLocalEvents

/-! Frame preservation from the same retained literal circuit trace.
The actual Raw operations and their successful trace determine this result;
no particular lowering shape, code equation or new runtime gate is assumed.
Spectator owner identity and whole-code transport remain separate obligations.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeLiteralFrame
open QleisliKernel QleisliKernel.Qirf

private def IsCircuit : Semantics.Raw.Event → Prop
  | .circuit _ _ => True
  | _ => False

private def OnlyCircuits (events : List Semantics.Raw.Event) : Prop :=
  ∀ event ∈ events, IsCircuit event

private theorem singleton_bad {event events} (same : [event] = events)
    (only : OnlyCircuits events) (bad : IsCircuit event → False) : False := by
  apply bad
  apply only event
  rw [← same]
  exact List.mem_cons_self

private theorem take_frame {before after : Semantics.RawTrace.Interface} {token port}
    (ran : Semantics.RawTrace.take before token = some (port,after)) :
    after.frame = before.frame := by
  unfold Semantics.RawTrace.take at ran
  obtain ⟨found,_lookup,returned⟩ := Option.bind_eq_some_iff.mp ran
  have equal := Option.some.inj returned
  exact (congrArg (fun pair : Semantics.Raw.Port × Semantics.RawTrace.Interface => pair.2.frame) equal).symm

private theorem step_frame {before after : Semantics.RawTrace.Interface} {operation events}
    (ran : Semantics.RawTrace.step before operation = some (after,events))
    (only : OnlyCircuits events) : after.frame = before.frame := by
  cases operation with
  | init0 output wire =>
    simp only [Semantics.RawTrace.step] at ran
    exact False.elim (singleton_bad (congrArg Prod.snd (Option.some.inj ran)) only (fun impossible => impossible))
  | gate value input output =>
    simp only [Semantics.RawTrace.step] at ran
    obtain ⟨⟨port,next⟩,taken,returned⟩ := Option.bind_eq_some_iff.mp ran
    have same : next.frame = after.frame :=
      congrArg (fun pair : Semantics.RawTrace.Interface × List Semantics.Raw.Event => pair.1.frame)
        (Option.some.inj returned)
    exact same.symm.trans (take_frame taken)
  | cnot control target controlOut targetOut =>
    simp only [Semantics.RawTrace.step] at ran
    obtain ⟨⟨c,next⟩,controlRead,tail⟩ := Option.bind_eq_some_iff.mp ran
    obtain ⟨⟨t,last⟩,targetRead,returned⟩ := Option.bind_eq_some_iff.mp tail
    have same : last.frame = after.frame :=
      congrArg (fun pair : Semantics.RawTrace.Interface × List Semantics.Raw.Event => pair.1.frame)
        (Option.some.inj returned)
    exact same.symm.trans ((take_frame targetRead).trans (take_frame controlRead))
  | toffoli a b target aOut bOut targetOut =>
    simp only [Semantics.RawTrace.step] at ran
    obtain ⟨⟨left,next⟩,leftRead,tail⟩ := Option.bind_eq_some_iff.mp ran
    obtain ⟨⟨right,middle⟩,rightRead,tail⟩ := Option.bind_eq_some_iff.mp tail
    obtain ⟨⟨target,last⟩,targetRead,returned⟩ := Option.bind_eq_some_iff.mp tail
    have same : last.frame = after.frame :=
      congrArg (fun pair : Semantics.RawTrace.Interface × List Semantics.Raw.Event => pair.1.frame)
        (Option.some.inj returned)
    exact same.symm.trans ((take_frame targetRead).trans ((take_frame rightRead).trans (take_frame leftRead)))
  | quantumIf control target controlOut targetOut zero one =>
    simp only [Semantics.RawTrace.step] at ran
    obtain ⟨⟨c,next⟩,controlRead,tail⟩ := Option.bind_eq_some_iff.mp ran
    obtain ⟨⟨t,last⟩,targetRead,returned⟩ := Option.bind_eq_some_iff.mp tail
    have same : last.frame = after.frame :=
      congrArg (fun pair : Semantics.RawTrace.Interface × List Semantics.Raw.Event => pair.1.frame)
        (Option.some.inj returned)
    exact same.symm.trans ((take_frame targetRead).trans (take_frame controlRead))
  | split input left right leftBits =>
    simp only [Semantics.RawTrace.step] at ran
    obtain ⟨⟨port,next⟩,taken,returned⟩ := Option.bind_eq_some_iff.mp ran
    have same : next.frame = after.frame :=
      congrArg (fun pair : Semantics.RawTrace.Interface × List Semantics.Raw.Event => pair.1.frame)
        (Option.some.inj returned)
    exact same.symm.trans (take_frame taken)
  | join left right output =>
    simp only [Semantics.RawTrace.step] at ran
    obtain ⟨⟨l,next⟩,leftRead,tail⟩ := Option.bind_eq_some_iff.mp ran
    obtain ⟨⟨r,last⟩,rightRead,returned⟩ := Option.bind_eq_some_iff.mp tail
    have same : last.frame = after.frame :=
      congrArg (fun pair : Semantics.RawTrace.Interface × List Semantics.Raw.Event => pair.1.frame)
        (Option.some.inj returned)
    exact same.symm.trans ((take_frame rightRead).trans (take_frame leftRead))
  | liftBasis input output wires table =>
    simp only [Semantics.RawTrace.step] at ran
    obtain ⟨⟨port,next⟩,_taken,returned⟩ := Option.bind_eq_some_iff.mp ran
    exact False.elim (singleton_bad (congrArg Prod.snd (Option.some.inj returned)) only (fun impossible => impossible))
  | applyUnitary input output steps =>
    simp only [Semantics.RawTrace.step] at ran
    obtain ⟨⟨port,next⟩,taken,returned⟩ := Option.bind_eq_some_iff.mp ran
    have same : next.frame = after.frame :=
      congrArg (fun pair : Semantics.RawTrace.Interface × List Semantics.Raw.Event => pair.1.frame)
        (Option.some.inj returned)
    exact same.symm.trans (take_frame taken)
  | certifiedCompute input output ancilla function uses logical =>
    simp only [Semantics.RawTrace.step] at ran
    obtain ⟨⟨port,next⟩,_taken,returned⟩ := Option.bind_eq_some_iff.mp ran
    exact False.elim (singleton_bad (congrArg Prod.snd (Option.some.inj returned)) only (fun impossible => impossible))
  | computeUseUncompute input output targets ancilla function uses =>
    simp only [Semantics.RawTrace.step] at ran
    obtain ⟨⟨source,next⟩,_taken,tail⟩ := Option.bind_eq_some_iff.mp ran
    obtain ⟨⟨ports,last⟩,_targetsRead,returned⟩ := Option.bind_eq_some_iff.mp tail
    exact False.elim (singleton_bad (congrArg Prod.snd (Option.some.inj returned)) only (fun impossible => impossible))
  | packUnit output =>
    simp only [Semantics.RawTrace.step] at ran
    exact (congrArg (fun pair : Semantics.RawTrace.Interface × List Semantics.Raw.Event => pair.1.frame)
      (Option.some.inj ran)).symm
  | unpackUnit input =>
    simp only [Semantics.RawTrace.step] at ran
    obtain ⟨⟨port,next⟩,taken,returned⟩ := Option.bind_eq_some_iff.mp ran
    split at returned
    · have same : next.frame = after.frame :=
        congrArg (fun pair : Semantics.RawTrace.Interface × List Semantics.Raw.Event => pair.1.frame)
          (Option.some.inj returned)
      exact same.symm.trans (take_frame taken)
    · cases returned

private theorem only_append {first second : List Semantics.Raw.Event}
    (only : OnlyCircuits (first ++ second)) : OnlyCircuits first ∧ OnlyCircuits second := by
  constructor
  · intro event member
    exact only event (List.mem_append.mpr (Or.inl member))
  · intro event member
    exact only event (List.mem_append.mpr (Or.inr member))

/-- `advance` appends events, so a forbidden earlier event cannot disappear
from a later circuit-only trace. -/
private theorem advance_frame {before after : Semantics.RawTrace.Prepared} {operation}
    (ran : Semantics.RawTrace.advance before operation = some after)
    (only : OnlyCircuits after.events) :
    OnlyCircuits before.events ∧ after.state.frame = before.state.frame := by
  unfold Semantics.RawTrace.advance at ran
  obtain ⟨⟨state,events⟩,stepped,returned⟩ := Option.bind_eq_some_iff.mp ran
  have equal := Option.some.inj returned
  have eventsEq : before.events ++ events = after.events :=
    congrArg Semantics.RawTrace.Prepared.events equal
  have all : OnlyCircuits (before.events ++ events) := by
    rw [eventsEq]
    exact only
  have parts := only_append all
  have same : state.frame = after.state.frame :=
    congrArg (fun prepared : Semantics.RawTrace.Prepared => prepared.state.frame) equal
  exact ⟨parts.1,same.symm.trans (step_frame stepped parts.2)⟩

private theorem fold_frame (operations : List Semantics.Raw.Op)
    {before after : Semantics.RawTrace.Prepared}
    (ran : operations.foldlM Semantics.RawTrace.advance before = some after)
    (only : OnlyCircuits after.events) :
    OnlyCircuits before.events ∧ after.state.frame = before.state.frame := by
  induction operations generalizing before with
  | nil =>
    change some before = some after at ran
    cases Option.some.inj ran
    exact ⟨only,rfl⟩
  | cons operation rest ih =>
    rw [List.foldlM_cons] at ran
    obtain ⟨next,advanced,tail⟩ := Option.bind_eq_some_iff.mp ran
    obtain ⟨nextOnly,tailFrame⟩ := ih tail
    obtain ⟨beforeOnly,stepFrame⟩ := advance_frame advanced nextOnly
    exact ⟨beforeOnly,tailFrame.trans stepFrame⟩

/-- The actual circuit-only literal retains the original complete quantum
frame, in its original order, for any finite input and any number of chunks.
No singleton quantumIf or join/apply/split shape is needed. -/
theorem literal_frame
    {dependencies program block start count inputs outputs roles frame selectorBits targetBits retained restricted
      beforeRoles afterRoles before after}
    (literal : @RuntimeLocalEvents.Literal dependencies program block start count inputs outputs roles frame
      selectorBits targetBits retained restricted beforeRoles afterRoles before after) :
    frame.interval.after.quantum.frame = frame.interval.before.quantum.frame := by
  have only : OnlyCircuits literal.traceResult.events := by
    intro event member
    rw [literal.literal] at member
    unfold RuntimeLocalEvents.circuitEvents at member
    obtain ⟨chunk,_present,same⟩ := List.mem_map.mp member
    rw [← same]
    trivial
  have preserved : literal.traceResult.state.frame = frame.interval.before.quantum.frame :=
    (fold_frame frame.operations literal.executed only).2
  have actual : literal.traceResult.state.frame = frame.interval.after.quantum.frame :=
    congrArg (fun state : Semantics.RawTrace.Interface => state.frame) literal.afterState
  exact actual.symm.trans preserved

#print axioms literal_frame

end Qleisli.RuntimeLiteralFrame
