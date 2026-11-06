import QleisliKernel.Raw.ObservationLayer
import QleisliKernel.Raw.ObservationOwnership
import QleisliKernel.Raw.Trace
import Qleisli.RuntimeObservingWrites

/-! Align each actual observing checker prefix with the independently read
Raw interface and event order. Only proofs use the successful checker result.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeObservingPrefix
open QleisliKernel QleisliKernel.Finite
open QleisliKernel.Semantics.Finite
open QleisliKernel.Raw.Observation (State insertClassical consume checkStep checkOps)
open QleisliKernel.Raw.ObservationAgreement (Reader Result Op readStep)
open Qleisli.RuntimeObservingWrites (WritesId WritesWithin)

def Issued (state : State) (id : Nat) : Prop := id ∈ state.classical.map Prod.fst

theorem issued_mono {before after : State} (keeps : before.classical ⊆ after.classical)
    {id : Nat} (issued : Issued before id) : Issued after id := by
  obtain ⟨entry,member,rfl⟩ := List.mem_map.mp issued
  exact List.mem_map_of_mem (keeps member)

private theorem inserted_id {before after : State} {id : Nat}
    (ok : insertClassical before id = .ok after) : Issued after id := by
  unfold Issued
  rw [(Raw.Observation.classical_fresh _ _ _ ok).2,List.map_append]
  exact List.mem_append.mpr (Or.inr (List.mem_singleton_self _))

private theorem classical_writes {before after : State} {output : Nat}
    (expression : Semantics.Observation.Expr) (ok : insertClassical before output = .ok after) :
    WritesWithin [.classical expression output] (Issued after) :=
  WritesWithin.singleton (by intro id writes; cases writes; exact inserted_id ok)

private theorem classical_quantum (state next : State) (id : Nat)
    (ok : insertClassical state id = .ok next) : next.quantum = state.quantum := by
  obtain ⟨_,_,h⟩ := except_bind_success _ _ _ ok
  have same := Except.ok.inj h
  subst next
  rfl

private theorem classical_fold_facts {α : Type} (items : List α) (output : α → Nat)
    (state next : State)
    (ok : items.foldlM (fun state item => insertClassical state (output item)) state = .ok next) :
    next.quantum = state.quantum ∧ state.classical ⊆ next.classical ∧
      ∀ item ∈ items, Issued next (output item) := by
  induction items generalizing state with
  | nil =>
    have same := Except.ok.inj ok
    subst next
    exact ⟨rfl,fun _ member => member,by simp⟩
  | cons item items ih =>
    simp only [List.foldlM_cons] at ok
    obtain ⟨middle,hi,rest⟩ := except_bind_success _ _ _ ok
    obtain ⟨quantum,keeps,outputs⟩ := ih middle rest
    refine ⟨quantum.trans (classical_quantum _ _ _ hi),?_,?_⟩
    · intro entry member
      apply keeps
      rw [(Raw.Observation.classical_fresh _ _ _ hi).2]
      exact List.mem_append.mpr (Or.inl member)
    · intro phi member
      rcases List.mem_cons.mp member with same | inside
      · subst phi
        exact issued_mono keeps (inserted_id hi)
      · exact outputs phi inside

private theorem consume_reference (state next : State) (input : Nat) (port : Semantics.Raw.Port)
    (ok : consume state input = .ok (port,next)) :
    ∃ taken : Semantics.RawTrace.Interface,
      Semantics.RawTrace.take state.quantum.reference input = some (port,taken) ∧
      next.quantum.reference =
        {taken with frame := Semantics.Observation.remaining state.quantum.reference port.wires} := by
  obtain ⟨⟨found,after⟩,hf,h⟩ := except_bind_success _ _ _ ok
  have same := Except.ok.inj h
  cases same
  have frame := congrArg Raw.State.frame (Raw.Ownership.take_state _ _ _ _ hf).2
  refine ⟨after.reference,Raw.take_reference _ _ _ _ hf,?_⟩
  simp only [Raw.State.reference,Semantics.Observation.remaining,frame]

private theorem step_reference (dependencies : List Dependency)
    (recurse : State → List Op → WorkM State) (reader : Reader)
    (sound : ∀ state ops next work left, (recurse state ops).run work = (.ok next,left) →
      state.classical ⊆ next.classical ∧
      ∃ events, reader state.quantum.reference ops = some (next.quantum.reference,events) ∧
        WritesWithin events (Issued next))
    (state next : State) (op : Op) (work left : Nat)
    (ok : (checkStep dependencies recurse state op).run work = (.ok next,left)) :
    state.classical ⊆ next.classical ∧
    ∃ events, readStep reader state.quantum.reference op = some (next.quantum.reference,events) ∧
      WritesWithin events (Issued next) := by
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨result,_,body,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,valid,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst next
  have history := (guard_success _ _ _ _ valid).1
  simp only [Bool.and_eq_true,Raw.Observation.history_eq,List.all_eq_true,List.contains_iff_mem] at history
  refine ⟨history.2.2,?_⟩
  cases op with
  | pure operation =>
    obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ body
    obtain ⟨transition,_,ht,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
    have same := (pure_success _ _ _ _ h).1
    subst result
    refine ⟨transition.events.map Semantics.Observation.Event.pure,?_,WritesWithin.pures _ _⟩
    simp [readStep,Raw.step_reference _ _ _ _ (lift_success _ _ _ _ ht).1]
  | measure input output =>
    obtain ⟨⟨port,consumed⟩,_,hc,h⟩ := bind_success _ _ _ _ _ body
    obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨updated,_,hn,h⟩ := bind_success _ _ _ _ _ h
    have same := (pure_success _ _ _ _ h).1
    subst result
    have insertion := (lift_success _ _ _ _ hn).1
    have quantum := classical_quantum _ _ _ insertion
    obtain ⟨taken,read,frame⟩ := consume_reference _ _ _ _ (lift_success _ _ _ _ hc).1
    refine ⟨[.erase state.quantum.reference.frame.length
      (Semantics.RawTrace.axes state.quantum.reference port.wires) (some output)],?_,?_⟩
    · simp [readStep,read,quantum,frame]
    · exact WritesWithin.singleton (by
        intro id writes
        cases writes
        exact (inserted_id insertion : Issued updated output))
  | reset input output wire =>
    obtain ⟨⟨port,consumed⟩,_,hc,h⟩ := bind_success _ _ _ _ _ body
    obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨quantum,_,hq,h⟩ := bind_success _ _ _ _ _ h
    have same := (pure_success _ _ _ _ h).1
    subst result
    obtain ⟨taken,read,frame⟩ := consume_reference _ _ _ _ (lift_success _ _ _ _ hc).1
    have inputRead := Raw.input_reference _ _ _ (lift_success _ _ _ _ hq).1
    change quantum.reference = ⟨consumed.quantum.reference.live ++ [⟨output,[wire],1⟩],
      consumed.quantum.reference.frame ++ [wire]⟩ at inputRead
    refine ⟨[.erase state.quantum.reference.frame.length (Semantics.RawTrace.axes state.quantum.reference port.wires) none,
      .pure (.init0 (Semantics.Observation.remaining state.quantum.reference port.wires).length)],?_,?_⟩
    · simp [readStep,read,inputRead,frame,Semantics.RawTrace.insert]
    · exact (WritesWithin.erase_none _ _ _).append (WritesWithin.pures [_] _)
  | discard input =>
    obtain ⟨⟨port,consumed⟩,_,hc,h⟩ := bind_success _ _ _ _ _ body
    have same := (pure_success _ _ _ _ h).1
    subst result
    obtain ⟨taken,read,frame⟩ := consume_reference _ _ _ _ (lift_success _ _ _ _ hc).1
    refine ⟨[.erase state.quantum.reference.frame.length
      (Semantics.RawTrace.axes state.quantum.reference port.wires) none],?_,WritesWithin.erase_none _ _ _⟩
    simp [readStep,read,frame]
  | constant value output =>
    have insertion := (lift_success _ _ _ _ body).1
    have quantum := classical_quantum _ _ _ insertion
    exact ⟨[.classical (.constant value) output],by simp [readStep,quantum],classical_writes _ insertion⟩
  | not input output =>
    obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ body
    have insertion := (lift_success _ _ _ _ h).1
    have quantum := classical_quantum _ _ _ insertion
    exact ⟨[.classical (.not input) output],by simp [readStep,quantum],classical_writes _ insertion⟩
  | xor first second output =>
    obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ body
    have insertion := (lift_success _ _ _ _ h).1
    have quantum := classical_quantum _ _ _ insertion
    exact ⟨[.classical (.xor first second) output],by simp [readStep,quantum],classical_writes _ insertion⟩
  | and first second output =>
    obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ body
    have insertion := (lift_success _ _ _ _ h).1
    have quantum := classical_quantum _ _ _ insertion
    exact ⟨[.classical (.and first second) output],by simp [readStep,quantum],classical_writes _ insertion⟩
  | branch condition thenOps elseOps quantum classical =>
    obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ body
    obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨thenState,_,ht,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨elseState,_,he,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨merged,_,hm,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨outputs,joinedKept,phiWrites⟩ := classical_fold_facts classical (·.output) _ _ (lift_success _ _ _ _ h).1
    obtain ⟨_leftKept,leftEvents,leftRead,leftWrites⟩ := sound _ _ _ _ _ ht
    obtain ⟨rightKept,rightEvents,rightRead,rightWrites⟩ := sound _ _ _ _ _ he
    change reader state.quantum.reference thenOps = some (thenState.quantum.reference,leftEvents) at leftRead
    change reader state.quantum.reference elseOps = some (elseState.quantum.reference,rightEvents) at rightRead
    have folded : ((quantum.map fun phi => (⟨phi.output,phi.wires,phi.wires.length⟩ : Semantics.Raw.Port))).foldlM
        Raw.input {elseState.quantum with live := [],frame := [],iso := thenState.quantum.iso || elseState.quantum.iso} =
        .ok merged := by
      simpa only [List.foldlM_map] using (lift_success _ _ _ _ hm).1
    have mergedFrame : merged.reference = Semantics.Observation.phiInterface quantum := by
      simpa [Semantics.Observation.phiInterface,List.flatMap_map,Function.comp_def] using
        Raw.inputs_reference _ _ _ folded
    let finish (arm : Semantics.RawTrace.Interface) (choice : Bool) : Semantics.Raw.Event :=
      .reorder arm.frame.length (Semantics.RawTrace.axes arm (Semantics.Observation.phiWires arm quantum choice))
    refine ⟨[.branch condition (leftEvents++[.pure (finish thenState.quantum.reference true)])
      (rightEvents++[.pure (finish elseState.quantum.reference false)]) classical],?_,?_⟩
    · simp [readStep,leftRead,rightRead,outputs,mergedFrame,finish]
    · have leftAll := leftWrites.append (WritesWithin.pures [finish thenState.quantum.reference true] _)
      have rightAll := rightWrites.append (WritesWithin.pures [finish elseState.quantum.reference false] _)
      apply WritesWithin.singleton
      intro id writes
      cases writes with
      | thenArm member emitted =>
        exact issued_mono (fun _ member => joinedKept (rightKept member)) (leftAll member emitted)
      | elseArm member emitted =>
        exact issued_mono joinedKept (rightAll member emitted)
      | phi member => exact phiWrites _ member

private def advance (reader : Reader) (before : Result) (op : Op) : Option Result := do
  let (after,events) ← readStep reader before.1 op
  return (after,before.2++events)

private theorem fold_reference (dependencies : List Dependency)
    (recurse : State → List Op → WorkM State) (reader : Reader)
    (sound : ∀ state ops next work left, (recurse state ops).run work = (.ok next,left) →
      state.classical ⊆ next.classical ∧
      ∃ events, reader state.quantum.reference ops = some (next.quantum.reference,events) ∧
        WritesWithin events (Issued next))
    (ops : List Op) (state next : State) (previous : List Semantics.Observation.Event) (work left : Nat)
    (ok : (ops.foldlM (checkStep dependencies recurse) state).run work = (.ok next,left)) :
    state.classical ⊆ next.classical ∧
    ∃ events, ops.foldlM (advance reader) (state.quantum.reference,previous) =
      some (next.quantum.reference,previous++events) ∧ WritesWithin events (Issued next) := by
  induction ops generalizing state previous work with
  | nil =>
    have same := (pure_success _ _ _ _ ok).1
    subst next
    exact ⟨fun _ member => member,[],by simp,WritesWithin.empty _⟩
  | cons op ops ih =>
    simp only [List.foldlM_cons] at ok
    obtain ⟨middle,b,head,rest⟩ := bind_success _ _ _ _ _ ok
    obtain ⟨firstKept,first,step,firstWrites⟩ := step_reference _ _ _ sound _ _ _ _ _ head
    obtain ⟨laterKept,later,read,laterWrites⟩ := ih middle (previous++first) b rest
    refine ⟨fun _ member => laterKept (firstKept member),first++later,?_,
      (firstWrites.mono (by intro id issued; exact issued_mono laterKept issued)).append laterWrites⟩
    simpa only [List.foldlM_cons,advance,step,bind,Option.bind,pure,List.append_assoc] using read

/-- The original observing checker and independent reader agree on the
quantum interface. Every literal write belongs to the successful check's
globally issued identities. -/
theorem checkOps_reference_with_writes (dependencies : List Dependency) (fuel : Nat)
    (state next : State) (ops : List Op) (work left : Nat)
    (ok : (checkOps dependencies fuel state ops).run work = (.ok next,left)) :
    state.classical ⊆ next.classical ∧
    ∃ events, Semantics.Observation.readOps fuel state.quantum.reference ops =
      some (next.quantum.reference,events) ∧ WritesWithin events (Issued next) := by
  induction fuel generalizing state next ops work left with
  | zero => cases ok
  | succ fuel ih =>
    obtain ⟨result,b,checked,h⟩ := bind_success _ _ _ _ _ ok
    obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
    have same := (pure_success _ _ _ _ h).1
    subst next
    obtain ⟨keeps,events,read,writes⟩ := fold_reference dependencies (checkOps dependencies fuel)
      (Semantics.Observation.readOps fuel) (fun state ops next work left ok => ih state next ops work left ok)
      ops state result [] work b checked
    refine ⟨keeps,events,?_,writes⟩
    rw [Raw.ObservationAgreement.read_succ]
    simpa only [List.nil_append] using read

theorem checkOps_reference (dependencies : List Dependency) (fuel : Nat)
    (state next : State) (ops : List Op) (work left : Nat)
    (ok : (checkOps dependencies fuel state ops).run work = (.ok next,left)) :
    ∃ events, Semantics.Observation.readOps fuel state.quantum.reference ops =
      some (next.quantum.reference,events) := by
  obtain ⟨_keeps,events,read,_writes⟩ := checkOps_reference_with_writes dependencies fuel state next ops work left ok
  exact ⟨events,read⟩

/-- The complete original verified program retains its input IDs and issues
every ID written by the actual prepared trace, including nested arms. -/
theorem verify_reference_with_writes (dependencies : List Dependency) (program : Semantics.Observation.Program)
    (checked : Raw.Observation.Checked) (work left : Nat)
    (ok : (Raw.Observation.verify dependencies program).run work = (.ok checked,left)) :
    (∀ id ∈ program.classicalInputs, Issued checked.state id) ∧
    WritesWithin checked.prepared.events (Issued checked.state) := by
  obtain ⟨_,_,_,rest⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨quantum,_,opened,rest⟩ := bind_success _ _ _ _ _ rest
  obtain ⟨initial,_,inputRead,rest⟩ := bind_success _ _ _ _ _ rest
  obtain ⟨state,_,walked,rest⟩ := bind_success _ _ _ _ _ rest
  obtain ⟨_,_,_,rest⟩ := bind_success _ _ _ _ _ rest
  obtain ⟨prepared,_,preparedRead,rest⟩ := bind_success _ _ _ _ _ rest
  obtain ⟨_,_,_,rest⟩ := bind_success _ _ _ _ _ rest
  have same := (pure_success _ _ _ _ rest).1
  subst checked
  obtain ⟨initialQuantum,_kept,inputs⟩ := classical_fold_facts program.classicalInputs id
    {quantum := quantum} initial (lift_success _ _ _ _ inputRead).1
  obtain ⟨keeps,events,original,writes⟩ := checkOps_reference_with_writes dependencies 65 initial state
    program.operations _ _ walked
  have start : initial.quantum.reference = Semantics.RawTrace.initial program.inputs := by
    rw [initialQuantum]
    simpa only [List.nil_append] using Raw.inputs_reference program.inputs {} quantum (lift_success _ _ _ _ opened).1
  rw [start] at original
  have literal : Semantics.Observation.read program = some prepared := by
    have read := (lift_success _ _ _ _ preparedRead).1
    cases result : Semantics.Observation.read program with
    | none => simp [readOption,result] at read
    | some actual =>
      simp only [readOption,result,Except.ok.injEq] at read
      exact congrArg some read
  let finish : Semantics.Raw.Event := .reorder state.quantum.reference.frame.length
    (Semantics.RawTrace.axes state.quantum.reference (program.outputs.flatMap fun token =>
      ((state.quantum.reference.live.find? (fun port => port.token == token)).map (·.wires)).getD []))
  have exactEvents : events++[.pure finish] = prepared.events := by
    simp only [Semantics.Observation.read,original,bind,Option.bind,pure] at literal
    exact congrArg Semantics.Observation.Prepared.events (Option.some.inj literal)
  refine ⟨fun id member => issued_mono keeps (inputs id member),?_⟩
  change WritesWithin prepared.events (Issued state)
  rw [← exactEvents]
  exact writes.append (WritesWithin.pures [finish] _)

#print axioms checkOps_reference_with_writes
#print axioms checkOps_reference
#print axioms verify_reference_with_writes

end Qleisli.RuntimeObservingPrefix
