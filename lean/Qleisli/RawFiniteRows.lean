import Qleisli.RawActionLocality
import Qleisli.RawActionComposition
import Qleisli.FinitePull
import Qleisli.RuntimeAdjacentAction
import Qleisli.RuntimeIntervalRawFold

/-! The original checked Raw event list reads amplitudes only on the
physical frame supplied by its actual source interval. This transports finite
input representations through pure slices without changing acceptance or work.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RawFiniteRows
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Semantics.Finite
open QleisliKernel.Semantics.Raw (Event)
open Qleisli.Semantics.RawAction

open Qleisli.Finite.Pull (scatter_bound)

/-- Equality of two reference functions on the genuine finite input frame. -/
def OnRows (bits : Nat) (left right : Nat → ℂ) : Prop :=
  ∀ row, row < 2^bits → left row = right row

private theorem hadamard_congr (bits target row : Nat) (targetBound : target < bits)
    (left right : Nat → ℂ) (same : OnRows bits left right) (bounded : row < 2^bits) :
    Qleisli.Semantics.Protected.gate .h target left row =
      Qleisli.Semantics.Protected.gate .h target right row := by
  have input : Locality.pull row (List.range bits) left = Locality.pull row (List.range bits) right := by
    funext coordinate
    exact same _ (scatter_bound row bits coordinate _ bounded (fun axis present => List.mem_range.mp present))
  have targetAt : ((List.range bits)[target]?).getD 0 = target := by
    rw [List.getElem?_range targetBound,Option.getD_some]
  have full : scatter row (List.range bits) row = row := by
    have undo := RuntimeScatterTransport.scatter_gather row (List.range bits) List.nodup_range
    simpa only [QleisliKernel.Raw.Sector.gather_identity row bits bounded] using undo
  have leftAction := Locality.hadamard_selected row row (List.range bits) List.nodup_range target
    (by simpa only [List.length_range] using targetBound) left
  have rightAction := Locality.hadamard_selected row row (List.range bits) List.nodup_range target
    (by simpa only [List.length_range] using targetBound) right
  rw [targetAt,full] at leftAction rightAction
  rw [leftAction,rightAction,input]

private theorem step_congr (dependencies : List Dependency) (bits : Nat) (operation : Step)
    (targets : ∀ axis ∈ QleisliKernel.Finite.targets operation.action, axis < bits)
    (left right : Nat → ℂ) (same : OnRows bits left right) :
    OnRows bits (step dependencies operation left) (step dependencies operation right) := by
  intro row bounded
  rcases operation with ⟨controls,action⟩
  unfold step
  split
  · exact same row bounded
  · cases action with
    | hadamard target =>
      exact hadamard_congr bits target row (targets target List.mem_cons_self) left right same bounded
    | monomial axes permutation phases =>
      apply Qleisli.Exact.sum_map_congr
      intro input _
      rw [same _ (scatter_bound row bits input axes bounded targets)]
    | contract axes index adjoint =>
      cases lookup : dependencies[index]? with
      | none => simp only [lookup]
      | some dependency =>
        simp only [lookup]
        apply Qleisli.Exact.sum_map_congr
        intro input _
        rw [same _ (scatter_bound row bits input axes bounded targets)]

private theorem circuit_congr (dependencies : List Dependency) (bits : Nat) (operations : List Step)
    (targets : ∀ operation ∈ operations, ∀ axis ∈ QleisliKernel.Finite.targets operation.action, axis < bits)
    (left right : Nat → ℂ) (same : OnRows bits left right) :
    OnRows bits (circuit dependencies operations left) (circuit dependencies operations right) := by
  induction operations generalizing left right with
  | nil => exact same
  | cons operation rest ih =>
    apply ih (fun child present => targets child (List.mem_cons_of_mem _ present))
    exact step_congr dependencies bits operation (targets operation List.mem_cons_self) left right same

/-- The finite frame widths and geometry of a literal event, without making
any claim about its effects, phase, work or realizability. -/
inductive BoundedEvent : Nat → Event → Nat → Prop
  | circuit (bits : Nat) (steps : List Step)
      (targets : ∀ operation ∈ steps, ∀ axis ∈ QleisliKernel.Finite.targets operation.action, axis < bits) :
      BoundedEvent bits (.circuit bits steps) bits
  | init0 (bits : Nat) : BoundedEvent bits (.init0 bits) (bits+1)
  | liftBasis (before after : Nat) (inputAxes outputAxes table : List Nat) :
      BoundedEvent before (.liftBasis before after inputAxes outputAxes table) after
  | reorder (bits : Nat) (axes : List Nat) : BoundedEvent bits (.reorder bits axes) bits
  | computed (bits : Nat) (axes : List Nat) (source ancilla : Nat) (function : List Nat)
      (uses logical : List Step) (bounded : ∀ axis ∈ axes, axis < bits) :
      BoundedEvent bits (.computed bits axes source ancilla function uses logical) bits
  | protectedComputed (bits : Nat) (axes : List Nat) (source ancilla : Nat) (function : List Nat)
      (uses : List Semantics.Raw.Use) (bounded : ∀ axis ∈ axes, axis < bits) :
      BoundedEvent bits (.protectedComputed bits axes source ancilla function uses) bits

  | structuralComputed (bits : Nat) (axes : List Nat) (forward inverse : List Step)
      (uses : List Semantics.Raw.Use) (bounded : ∀ axis ∈ axes, axis < bits) :
      BoundedEvent bits (.structuralComputed bits axes forward inverse uses) bits

private theorem embed_congr (bits : Nat) (axes : List Nat) (bounded : ∀ axis ∈ axes, axis < bits)
    (action : (Nat → ℂ) → Nat → ℂ) (left right : Nat → ℂ) (same : OnRows bits left right) :
    OnRows bits (embed axes action left) (embed axes action right) := by
  intro row inside
  have pulled : (fun input => left (scatter row axes input)) =
      fun input => right (scatter row axes input) := by
    funext input
    exact same _ (scatter_bound row bits input axes inside bounded)
  unfold embed
  rw [pulled]

theorem BoundedEvent.congr {before after operation}
    (bounded : BoundedEvent before operation after) (dependencies : List Dependency)
    (left right : Nat → ℂ) (same : OnRows before left right) :
    OnRows after (event dependencies operation left) (event dependencies operation right) := by
  cases bounded with
  | circuit steps targets => exact circuit_congr dependencies before steps targets left right same
  | init0 =>
    intro row bound
    simp only [event]
    split
    · exact same row ‹row < 2^before›
    · rfl
  | liftBasis _ _ _ _ =>
    intro row bound
    simp only [event]
    apply Qleisli.Exact.sum_map_congr
    intro input present
    rw [same _ (List.mem_range.mp present)]
  | reorder _ =>
    intro row bound
    simp only [event]
    apply Qleisli.Exact.sum_map_congr
    intro input present
    rw [same _ (List.mem_range.mp present)]
  | computed axes source ancilla function uses logical bounded =>
    simp only [event]
    apply embed_congr before axes bounded _ left right same
  | protectedComputed axes source ancilla function uses bounded =>
    simp only [event]
    apply embed_congr before axes bounded _ left right same

  | structuralComputed axes forward inverse uses bounded =>
    simp only [event]
    exact embed_congr before axes bounded _ left right same

inductive BoundedEvents : Nat → List Event → Nat → Prop where
  | nil (bits : Nat) : BoundedEvents bits [] bits
  | cons {before middle after event rest} (head : BoundedEvent before event middle)
      (tail : BoundedEvents middle rest after) : BoundedEvents before (event::rest) after

theorem BoundedEvents.append {before middle after first rest}
    (left : BoundedEvents before first middle) (right : BoundedEvents middle rest after) :
    BoundedEvents before (first++rest) after := by
  induction left with
  | nil => exact right
  | cons head _ ih => exact .cons head (ih right)

theorem BoundedEvents.congr {before after operations}
    (bounded : BoundedEvents before operations after) (dependencies : List Dependency)
    (left right : Nat → ℂ) (same : OnRows before left right) :
    OnRows after (events dependencies operations left) (events dependencies operations right) := by
  induction bounded generalizing left right with
  | nil => exact same
  | cons head _ ih => exact ih _ _ (head.congr dependencies left right same)

#print axioms BoundedEvents.congr



open QleisliKernel.Finite (guard_success)
open QleisliKernel.Semantics.Raw (Port Op)
open QleisliKernel.Semantics.RawTrace (Interface take insert)

private theorem take_facts {initial next : Interface} {token : Nat} {port : Port}
    (read : take initial token = some (port,next)) :
    next.frame = initial.frame ∧ port ∈ initial.live ∧ next.live ⊆ initial.live := by
  obtain ⟨found,lookup,rest⟩ := Option.bind_eq_some_iff.mp read
  rcases Prod.mk.inj (Option.some.inj rest) with ⟨rfl,rfl⟩
  exact ⟨rfl,List.mem_of_find?_eq_some lookup,fun _ h => (List.mem_filter.mp h).1⟩

private theorem read_targets {targets : List Semantics.Raw.Target} {initial next : Interface} {prior ports : List Port}
    (read : targets.foldlM (fun (ports,state) target => do
      let (port,next) ← take state target.input
      pure (ports ++ [port],next)) (prior,initial) = some (ports,next)) :
    next.frame = initial.frame ∧ ∀ port ∈ ports, port ∈ prior ∨ port ∈ initial.live := by
  induction targets generalizing initial prior with
  | nil =>
    rcases Prod.mk.inj (Option.some.inj read) with ⟨rfl,rfl⟩
    exact ⟨rfl,fun _ present => Or.inl present⟩
  | cons target rest ih =>
    simp only [List.foldlM_cons] at read
    obtain ⟨⟨selected,middle⟩,first,tail⟩ := Option.bind_eq_some_iff.mp read
    obtain ⟨⟨port,taken⟩,takeRead,returned⟩ := Option.bind_eq_some_iff.mp first
    rcases Prod.mk.inj (Option.some.inj returned) with ⟨rfl,rfl⟩
    have takenFacts := take_facts takeRead
    have remaining := ih tail
    refine ⟨remaining.1.trans takenFacts.1,?_⟩
    intro candidate member
    rcases remaining.2 candidate member with early | live
    · rcases List.mem_append.mp early with present | same
      · exact Or.inl present
      · have equal := List.mem_singleton.mp same
        exact Or.inr (equal.symm ▸ takenFacts.2.1)
    · exact Or.inr (takenFacts.2.2 live)

private theorem insert_targets_frame (ports : List (Semantics.Raw.Target × Port)) (state : Interface) :
    (ports.foldl (fun next (target,port) => insert next target.output port.wires) state).frame =
      state.frame := by
  induction ports generalizing state with
  | nil => rfl
  | cons head tail ih =>
    rcases head with ⟨target,port⟩
    exact ih (insert state target.output port.wires)

private theorem axes_inside {state : Interface} {wires : List Nat} (covered : wires ⊆ state.frame) :
    ∀ axis ∈ wires.map state.frame.idxOf, axis < state.frame.length := by
  intro axis member
  obtain ⟨wire,present,rfl⟩ := List.mem_map.mp member
  exact List.idxOf_lt_length_of_mem (covered present)

private theorem checked_circuit (dependencies : List Dependency) (bits : Nat) (steps : List Step)
    (receipt : RuntimeInterval.Computed (Raw.Pure.eventCheck dependencies (.circuit bits steps)) ()) :
    BoundedEvents bits [.circuit bits steps] bits := by
  obtain ⟨work,left,ran⟩ := receipt
  have valid := (guard_success _ _ _ _ ran).1
  refine .cons (.circuit bits steps ?_) (.nil bits)
  intro operation present axis used
  unfold Raw.circuitStepsValid at valid
  have localValid := List.all_eq_true.mp valid operation present
  simp only [QleisliKernel.Finite.axesValid,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at localValid
  exact localValid.1.1.2 axis (List.mem_append_right _ used)

/-- Every event emitted by the original pure Raw reader has the original
intermediate finite width. Circuit geometry uses the actual event checks.
Computed geometry uses the original selected live ports. -/
theorem read_step_bounded (dependencies : List Dependency) {state final : Interface} {operation : Op}
    {events : List Event}
    (read : Semantics.RawTrace.step state operation = some (final,events))
    (covered : ∀ port ∈ state.live, port.wires ⊆ state.frame)
    (checks : ∀ event ∈ events, RuntimeInterval.Computed (Raw.Pure.eventCheck dependencies event) ()) :
    BoundedEvents state.frame.length events final.frame.length := by
  cases operation with
  | init0 output wire =>
    rcases Prod.mk.inj (Option.some.inj read) with ⟨rfl,rfl⟩
    simpa only [List.length_append,List.length_cons,List.length_nil] using
      BoundedEvents.cons (BoundedEvent.init0 state.frame.length) (.nil (state.frame.length+1))
  | packUnit output =>
    rcases Prod.mk.inj (Option.some.inj read) with ⟨rfl,rfl⟩
    exact .nil state.frame.length
  | unpackUnit input =>
    obtain ⟨⟨port,next⟩,taken,rest⟩ := Option.bind_eq_some_iff.mp read
    change (if (port.bits == 0 && port.wires.isEmpty) = true then some (next,[]) else none) =
      some (final,events) at rest
    by_cases unit : (port.bits == 0 && port.wires.isEmpty) = true
    · rw [if_pos unit] at rest
      rcases Prod.mk.inj (Option.some.inj rest) with ⟨rfl,rfl⟩
      rw [(take_facts taken).1]
      exact .nil state.frame.length
    · rw [if_neg unit] at rest; cases rest
  | gate gate input output =>
    obtain ⟨⟨port,next⟩,taken,rest⟩ := Option.bind_eq_some_iff.mp read
    rcases Prod.mk.inj (Option.some.inj rest) with ⟨rfl,rfl⟩
    change BoundedEvents state.frame.length _ next.frame.length
    rw [(take_facts taken).1]
    exact checked_circuit dependencies _ _ (checks _ List.mem_cons_self)
  | cnot control target controlOut targetOut =>
    obtain ⟨⟨c,one⟩,cRead,rest⟩ := Option.bind_eq_some_iff.mp read
    obtain ⟨⟨t,two⟩,tRead,rest⟩ := Option.bind_eq_some_iff.mp rest
    rcases Prod.mk.inj (Option.some.inj rest) with ⟨rfl,rfl⟩
    change BoundedEvents state.frame.length _ two.frame.length
    rw [(take_facts tRead).1,(take_facts cRead).1]
    exact checked_circuit dependencies _ _ (checks _ List.mem_cons_self)
  | toffoli first second target firstOut secondOut targetOut =>
    obtain ⟨⟨a,one⟩,aRead,rest⟩ := Option.bind_eq_some_iff.mp read
    obtain ⟨⟨b,two⟩,bRead,rest⟩ := Option.bind_eq_some_iff.mp rest
    obtain ⟨⟨t,three⟩,tRead,rest⟩ := Option.bind_eq_some_iff.mp rest
    rcases Prod.mk.inj (Option.some.inj rest) with ⟨rfl,rfl⟩
    change BoundedEvents state.frame.length _ three.frame.length
    rw [(take_facts tRead).1,(take_facts bRead).1,(take_facts aRead).1]
    exact checked_circuit dependencies _ _ (checks _ List.mem_cons_self)
  | quantumIf control target controlOut targetOut zero oneSteps =>
    obtain ⟨⟨c,one⟩,cRead,rest⟩ := Option.bind_eq_some_iff.mp read
    obtain ⟨⟨t,two⟩,tRead,rest⟩ := Option.bind_eq_some_iff.mp rest
    rcases Prod.mk.inj (Option.some.inj rest) with ⟨rfl,rfl⟩
    change BoundedEvents state.frame.length _ two.frame.length
    rw [(take_facts tRead).1,(take_facts cRead).1]
    exact checked_circuit dependencies _ _ (checks _ List.mem_cons_self)
  | split input left right leftBits =>
    obtain ⟨⟨port,next⟩,taken,rest⟩ := Option.bind_eq_some_iff.mp read
    rcases Prod.mk.inj (Option.some.inj rest) with ⟨rfl,rfl⟩
    change BoundedEvents state.frame.length [] next.frame.length
    rw [(take_facts taken).1]
    exact .nil state.frame.length
  | join left right output =>
    obtain ⟨⟨l,one⟩,lRead,rest⟩ := Option.bind_eq_some_iff.mp read
    obtain ⟨⟨r,two⟩,rRead,rest⟩ := Option.bind_eq_some_iff.mp rest
    rcases Prod.mk.inj (Option.some.inj rest) with ⟨rfl,rfl⟩
    change BoundedEvents state.frame.length [] two.frame.length
    rw [(take_facts rRead).1,(take_facts lRead).1]
    exact .nil state.frame.length
  | liftBasis input output wires table =>
    obtain ⟨⟨port,next⟩,taken,rest⟩ := Option.bind_eq_some_iff.mp read
    rcases Prod.mk.inj (Option.some.inj rest) with ⟨rfl,rfl⟩
    exact .cons (.liftBasis _ _ _ _ _) (.nil _)
  | applyUnitary input output steps =>
    obtain ⟨⟨port,next⟩,taken,rest⟩ := Option.bind_eq_some_iff.mp read
    rcases Prod.mk.inj (Option.some.inj rest) with ⟨rfl,rfl⟩
    change BoundedEvents state.frame.length _ next.frame.length
    rw [(take_facts taken).1]
    exact checked_circuit dependencies _ _ (checks _ List.mem_cons_self)
  | certifiedCompute input output ancilla function uses logical =>
    obtain ⟨⟨port,next⟩,taken,rest⟩ := Option.bind_eq_some_iff.mp read
    rcases Prod.mk.inj (Option.some.inj rest) with ⟨rfl,rfl⟩
    change BoundedEvents state.frame.length _ next.frame.length
    rw [(take_facts taken).1]
    exact .cons (.computed _ _ _ _ _ _ _ (axes_inside (covered _ (take_facts taken).2.1))) (.nil _)
  | structuralCompute input output scratch forward inverse uses =>
    obtain ⟨⟨port,next⟩,taken,rest⟩ := Option.bind_eq_some_iff.mp read
    rcases Prod.mk.inj (Option.some.inj rest) with ⟨rfl,rfl⟩
    change BoundedEvents state.frame.length _ next.frame.length
    rw [(take_facts taken).1]
    exact .cons (.structuralComputed _ _ _ _ _ (axes_inside
      (covered _ (take_facts taken).2.1))) (.nil _)
  | computeUseUncompute input output targets ancilla function uses =>
    obtain ⟨⟨source,one⟩,taken,rest⟩ := Option.bind_eq_some_iff.mp read
    obtain ⟨⟨ports,two⟩,targetRead,rest⟩ := Option.bind_eq_some_iff.mp rest
    rcases Prod.mk.inj (Option.some.inj rest) with ⟨rfl,rfl⟩
    have first := take_facts taken
    have later := read_targets targetRead
    have wires : source.wires ++ ports.flatMap (·.wires) ⊆ state.frame := by
      intro wire member
      rcases List.mem_append.mp member with direct | other
      · exact covered source first.2.1 direct
      · obtain ⟨port,present,found⟩ := List.mem_flatMap.mp other
        rcases later.2 port present with impossible | retained
        · cases impossible
        · exact covered port (first.2.2 retained) found
    rw [insert_targets_frame]
    change BoundedEvents state.frame.length _ two.frame.length
    rw [later.1,first.1]
    exact .cons (.protectedComputed _ _ _ _ _ _ (axes_inside wires)) (.nil _)

#print axioms read_step_bounded



open QleisliKernel.Finite (bind_success pure_success lift_success)

private theorem checked_events (dependencies : List Dependency) (events : List Event)
    (work left : Nat)
    (read : (events.foldlM (fun _ event => Raw.Pure.eventCheck dependencies event) ()).run work = (.ok (),left)) :
    ∀ event ∈ events, RuntimeInterval.Computed (Raw.Pure.eventCheck dependencies event) () := by
  induction events generalizing work with
  | nil => simp
  | cons head tail ih =>
    simp only [List.foldlM_cons] at read
    obtain ⟨returned,middle,first,rest⟩ := bind_success _ _ _ _ _ read
    cases returned
    intro event member
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨work,middle,first⟩
    · exact ih middle rest event later

/-- The actual pure check determines its literal events and finite domains. -/
theorem checked_step (dependencies : List Dependency)
    (recurse : Raw.Observation.State → List Semantics.Observation.Op → QleisliKernel.Finite.WorkM Raw.Observation.State)
    (before after : Raw.Observation.State) (operation : Op) (work left : Nat)
    (read : (Raw.Observation.checkStep dependencies recurse before (.pure operation)).run work = (.ok after,left)) :
    ∃ events, Semantics.RawTrace.step before.quantum.reference operation = some (after.quantum.reference,events) ∧
      BoundedEvents before.quantum.frame.length events after.quantum.frame.length := by
  obtain ⟨transition,native,same,valid,eventsRead⟩ :=
    RuntimeIntervalRawFold.checkStep_pure_raw dependencies recurse before after operation work left read
  have original := Raw.step_reference _ _ _ _ native
  have facts := Raw.Ownership.valid _ valid
  obtain ⟨eventWork,eventLeft,ran⟩ := eventsRead
  subst after
  refine ⟨transition.events,original,read_step_bounded dependencies original ?_ ?_⟩
  · intro port live wire member
    exact facts.covered wire (List.mem_flatMap.mpr ⟨port,live,member⟩)
  · exact checked_events dependencies _ eventWork eventLeft ran

private theorem checked_fold (dependencies : List Dependency)
    (recurse : Raw.Observation.State → List Semantics.Observation.Op → QleisliKernel.Finite.WorkM Raw.Observation.State)
    (operations : List Op) (before after : Raw.Observation.State)
    (earlier : List Event) (bits work left : Nat)
    (read : ((operations.map Semantics.Observation.Op.pure).foldlM
      (Raw.Observation.checkStep dependencies recurse) before).run work = (.ok after,left)) :
    ∃ events, operations.foldlM Semantics.RawTrace.advance ⟨before.quantum.reference,earlier,bits⟩ =
      some ⟨after.quantum.reference,earlier++events,bits⟩ ∧
      BoundedEvents before.quantum.frame.length events after.quantum.frame.length := by
  induction operations generalizing before earlier work with
  | nil =>
    have same := (pure_success _ _ _ _ read).1
    subst after
    exact ⟨[],by simp,.nil _⟩
  | cons operation operations ih =>
    simp only [List.map_cons,List.foldlM_cons] at read
    obtain ⟨next,middle,first,rest⟩ := bind_success _ _ _ _ _ read
    obtain ⟨head,stepped,headBounds⟩ := checked_step dependencies recurse before next operation work middle first
    obtain ⟨tail,folded,tailBounds⟩ := ih next (earlier++head) middle rest
    refine ⟨head++tail,?_,headBounds.append tailBounds⟩
    simpa only [List.foldlM_cons,Semantics.RawTrace.advance,stepped,bind,Option.bind,pure,List.append_assoc] using folded

/-- The original budgeted interval read retains the genuine finite domains
for the exact independently read event list. -/
theorem checked_slice {deps program block start count}
    (slice : @RuntimeAdjacentSlices.Slice deps program block start count)
    (events : List Event)
    (trace : RuntimeLocalEvents.trace slice.interval.before.quantum.reference slice.ops =
      some ⟨slice.interval.after.quantum.reference,events,slice.interval.before.quantum.frame.length⟩) :
    BoundedEvents slice.interval.before.quantum.frame.length events slice.interval.after.quantum.frame.length := by
  obtain ⟨work,left,read⟩ := slice.interval.intervalRead
  rw [slice.literal] at read
  cases fuel : block.fuel with
  | zero => rw [fuel] at read; cases read
  | succ depth =>
    rw [fuel] at read
    obtain ⟨final,middle,checked,h⟩ := bind_success _ _ _ _ _ read
    obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
    have same := (pure_success _ _ _ _ h).1
    obtain ⟨emitted,folded,bounded⟩ := checked_fold deps (Raw.Observation.checkOps deps depth)
      slice.ops slice.interval.before final [] slice.interval.before.quantum.frame.length work middle checked
    rw [← same,List.nil_append] at folded
    have equal : emitted = events :=
      congrArg Semantics.RawTrace.Prepared.events (Option.some.inj (folded.symm.trans trace))
    rw [← same,equal] at bounded
    exact bounded

#print axioms checked_slice

end Qleisli.RawFiniteRows
