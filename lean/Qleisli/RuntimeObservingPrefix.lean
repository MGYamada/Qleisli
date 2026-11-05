import QleisliKernel.Raw.ObservationLayer
import QleisliKernel.Raw.ObservationOwnership
import QleisliKernel.Raw.Trace

/-! Align each actual observing checker prefix with the independently read
Raw interface and event order. Only proofs use the successful checker result.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeObservingPrefix
open QleisliKernel QleisliKernel.Finite
open QleisliKernel.Semantics.Finite
open QleisliKernel.Raw.Observation (State insertClassical consume checkStep checkOps)
open QleisliKernel.Raw.ObservationAgreement (Reader Result Op readStep)

private theorem classical_quantum (state next : State) (id : Nat)
    (ok : insertClassical state id = .ok next) : next.quantum = state.quantum := by
  obtain ⟨_,_,h⟩ := except_bind_success _ _ _ ok
  have same := Except.ok.inj h
  subst next
  rfl

private theorem classical_fold_quantum (items : List Semantics.Observation.ClassicalPhi)
    (state next : State)
    (ok : items.foldlM (fun state item => insertClassical state item.output) state = .ok next) :
    next.quantum = state.quantum := by
  induction items generalizing state with
  | nil => have same := Except.ok.inj ok; subst next; rfl
  | cons item items ih =>
    simp only [List.foldlM_cons] at ok
    obtain ⟨middle,hi,rest⟩ := except_bind_success _ _ _ ok
    exact (ih middle rest).trans (classical_quantum _ _ _ hi)

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
      ∃ events, reader state.quantum.reference ops = some (next.quantum.reference,events))
    (state next : State) (op : Op) (work left : Nat)
    (ok : (checkStep dependencies recurse state op).run work = (.ok next,left)) :
    ∃ events, readStep reader state.quantum.reference op = some (next.quantum.reference,events) := by
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨result,_,body,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst next
  cases op with
  | pure operation =>
    obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ body
    obtain ⟨transition,_,ht,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
    have same := (pure_success _ _ _ _ h).1
    subst result
    refine ⟨transition.events.map Semantics.Observation.Event.pure,?_⟩
    simp [readStep,Raw.step_reference _ _ _ _ (lift_success _ _ _ _ ht).1]
  | measure input output =>
    obtain ⟨⟨port,consumed⟩,_,hc,h⟩ := bind_success _ _ _ _ _ body
    obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨updated,_,hn,h⟩ := bind_success _ _ _ _ _ h
    have same := (pure_success _ _ _ _ h).1
    subst result
    have quantum := classical_quantum _ _ _ (lift_success _ _ _ _ hn).1
    obtain ⟨taken,read,frame⟩ := consume_reference _ _ _ _ (lift_success _ _ _ _ hc).1
    refine ⟨[.erase state.quantum.reference.frame.length
      (Semantics.RawTrace.axes state.quantum.reference port.wires) (some output)],?_⟩
    simp [readStep,read,quantum,frame]
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
      .pure (.init0 (Semantics.Observation.remaining state.quantum.reference port.wires).length)],?_⟩
    simp [readStep,read,inputRead,frame,Semantics.RawTrace.insert]
  | discard input =>
    obtain ⟨⟨port,consumed⟩,_,hc,h⟩ := bind_success _ _ _ _ _ body
    have same := (pure_success _ _ _ _ h).1
    subst result
    obtain ⟨taken,read,frame⟩ := consume_reference _ _ _ _ (lift_success _ _ _ _ hc).1
    refine ⟨[.erase state.quantum.reference.frame.length
      (Semantics.RawTrace.axes state.quantum.reference port.wires) none],?_⟩
    simp [readStep,read,frame]
  | constant value output =>
    have quantum := classical_quantum _ _ _ (lift_success _ _ _ _ body).1
    exact ⟨[.classical (.constant value) output],by simp [readStep,quantum]⟩
  | not input output =>
    obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ body
    have quantum := classical_quantum _ _ _ (lift_success _ _ _ _ h).1
    exact ⟨[.classical (.not input) output],by simp [readStep,quantum]⟩
  | xor first second output =>
    obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ body
    have quantum := classical_quantum _ _ _ (lift_success _ _ _ _ h).1
    exact ⟨[.classical (.xor first second) output],by simp [readStep,quantum]⟩
  | and first second output =>
    obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ body
    have quantum := classical_quantum _ _ _ (lift_success _ _ _ _ h).1
    exact ⟨[.classical (.and first second) output],by simp [readStep,quantum]⟩
  | branch condition thenOps elseOps quantum classical =>
    obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ body
    obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨thenState,_,ht,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨elseState,_,he,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨merged,_,hm,h⟩ := bind_success _ _ _ _ _ h
    have outputs := classical_fold_quantum _ _ _ (lift_success _ _ _ _ h).1
    obtain ⟨leftEvents,leftRead⟩ := sound _ _ _ _ _ ht
    obtain ⟨rightEvents,rightRead⟩ := sound _ _ _ _ _ he
    change reader state.quantum.reference thenOps = some (thenState.quantum.reference,leftEvents) at leftRead
    change reader state.quantum.reference elseOps = some (elseState.quantum.reference,rightEvents) at rightRead
    have folded : ((quantum.map fun phi => (⟨phi.output,phi.wires,phi.wires.length⟩ : Semantics.Raw.Port))).foldlM
        Raw.input {elseState.quantum with live := [],frame := [],iso := thenState.quantum.iso || elseState.quantum.iso} =
        .ok merged := by
      simpa only [List.foldlM_map] using (lift_success _ _ _ _ hm).1
    have mergedFrame : merged.reference = Semantics.Observation.phiInterface quantum := by
      simpa [Semantics.Observation.phiInterface,List.flatMap_map,Function.comp_def] using
        Raw.inputs_reference _ _ _ folded
    let finish (arm : Semantics.RawTrace.Interface) (choice : Bool) :=
      Semantics.Observation.Event.pure (.reorder arm.frame.length
        (Semantics.RawTrace.axes arm (Semantics.Observation.phiWires arm quantum choice)))
    refine ⟨[.branch condition (leftEvents++[finish thenState.quantum.reference true])
      (rightEvents++[finish elseState.quantum.reference false]) classical],?_⟩
    simp [readStep,leftRead,rightRead,outputs,mergedFrame,finish]

private def advance (reader : Reader) (before : Result) (op : Op) : Option Result := do
  let (after,events) ← readStep reader before.1 op
  return (after,before.2++events)

private theorem fold_reference (dependencies : List Dependency)
    (recurse : State → List Op → WorkM State) (reader : Reader)
    (sound : ∀ state ops next work left, (recurse state ops).run work = (.ok next,left) →
      ∃ events, reader state.quantum.reference ops = some (next.quantum.reference,events))
    (ops : List Op) (state next : State) (previous : List Semantics.Observation.Event) (work left : Nat)
    (ok : (ops.foldlM (checkStep dependencies recurse) state).run work = (.ok next,left)) :
    ∃ events, ops.foldlM (advance reader) (state.quantum.reference,previous) =
      some (next.quantum.reference,previous++events) := by
  induction ops generalizing state previous work with
  | nil =>
    have same := (pure_success _ _ _ _ ok).1
    subst next
    exact ⟨[],by simp⟩
  | cons op ops ih =>
    simp only [List.foldlM_cons] at ok
    obtain ⟨middle,b,head,rest⟩ := bind_success _ _ _ _ _ ok
    obtain ⟨first,step⟩ := step_reference _ _ _ sound _ _ _ _ _ head
    obtain ⟨later,read⟩ := ih middle (previous++first) b rest
    refine ⟨first++later,?_⟩
    simpa only [List.foldlM_cons,advance,step,bind,Option.bind,pure,List.append_assoc] using read

/-- The original observing checker and independent reader have identical
quantum interfaces after each successfully checked prefix. The reader emits
its original events, including all branches and both ordered phi reorders. -/
theorem checkOps_reference (dependencies : List Dependency) (fuel : Nat)
    (state next : State) (ops : List Op) (work left : Nat)
    (ok : (checkOps dependencies fuel state ops).run work = (.ok next,left)) :
    ∃ events, Semantics.Observation.readOps fuel state.quantum.reference ops =
      some (next.quantum.reference,events) := by
  induction fuel generalizing state next ops work left with
  | zero => cases ok
  | succ fuel ih =>
    obtain ⟨result,b,checked,h⟩ := bind_success _ _ _ _ _ ok
    obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
    have same := (pure_success _ _ _ _ h).1
    subst next
    obtain ⟨events,read⟩ := fold_reference dependencies (checkOps dependencies fuel)
      (Semantics.Observation.readOps fuel) (fun state ops next work left ok => ih state next ops work left ok)
      ops state result [] work b checked
    refine ⟨events,?_⟩
    rw [Raw.ObservationAgreement.read_succ]
    simpa only [List.nil_append] using read

#print axioms checkOps_reference

end Qleisli.RuntimeObservingPrefix
