import Qleisli.RuntimeAdjacentRootAction
import Qleisli.RuntimeObservingWrites

/-! Two successful reads of the same observing operations write the same
ordinary identities, even when their wire interfaces and depth differ.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeObservingWrites
open QleisliKernel
open Raw.ObservationAgreement (Interface Op Reader readStep read_succ layer)
open Semantics.Observation (Event ClassicalPhi readOps)

private theorem within_append (left right : List Event) (allowed : Nat → Prop) :
    WritesWithin (left++right) allowed ↔ WritesWithin left allowed ∧ WritesWithin right allowed := by
  refine ⟨fun all => ⟨?_,?_⟩,fun both => both.1.append both.2⟩
  · exact fun _ present _ write => all (List.mem_append.mpr (.inl present)) write
  · exact fun _ present _ write => all (List.mem_append.mpr (.inr present)) write

private theorem within_measure (bits : Nat) (axes : List Nat) (output : Nat) (allowed : Nat → Prop) :
    WritesWithin [.erase bits axes (some output)] allowed ↔ allowed output := by
  refine ⟨fun h => h List.mem_cons_self (.measure bits axes output),fun h => WritesWithin.singleton ?_⟩
  intro _ write
  cases write
  exact h

private theorem within_branch (condition : Nat) (left right : List Event) (phis : List ClassicalPhi)
    (allowed : Nat → Prop) : WritesWithin [.branch condition left right phis] allowed ↔
      WritesWithin left allowed ∧ WritesWithin right allowed ∧ ∀ phi ∈ phis, allowed phi.output := by
  refine ⟨fun h => ⟨?_,?_,?_⟩,fun h => WritesWithin.singleton ?_⟩
  · exact fun _ present _ write => h List.mem_cons_self (.thenArm present write)
  · exact fun _ present _ write => h List.mem_cons_self (.elseArm present write)
  · exact fun _ present => h List.mem_cons_self (.phi present)
  · intro _ write
    cases write with
    | thenArm present write => exact h.1 present write
    | elseArm present write => exact h.2.1 present write
    | phi present => exact h.2.2 _ present

private theorem within_finish (events : List Event) (finish : Semantics.Raw.Event) (allowed : Nat → Prop) :
    WritesWithin (events++[.pure finish]) allowed ↔ WritesWithin events allowed := by
  rw [within_append]
  exact ⟨And.left,fun held => ⟨held,WritesWithin.pures [finish] allowed⟩⟩

private theorem reset_has_no_writes (bits : Nat) (axes : List Nat) (finish : Semantics.Raw.Event)
    (allowed : Nat → Prop) : WritesWithin [.erase bits axes none,.pure finish] allowed :=
  (WritesWithin.erase_none bits axes allowed).append (WritesWithin.pures [finish] allowed)

private theorem step_same_writes (left right : Reader) (allowed : Nat → Prop)
    (same : ∀ initialL initialR ops finalL finalR eventsL eventsR,
      left initialL ops = some (finalL,eventsL) → right initialR ops = some (finalR,eventsR) →
      (WritesWithin eventsL allowed ↔ WritesWithin eventsR allowed))
    {initialL initialR finalL finalR : Interface} {eventsL eventsR : List Event} (op : Op)
    (ranL : readStep left initialL op = some (finalL,eventsL))
    (ranR : readStep right initialR op = some (finalR,eventsR)) :
    WritesWithin eventsL allowed ↔ WritesWithin eventsR allowed := by
  cases op with
  | pure operation =>
    simp only [readStep] at ranL ranR
    obtain ⟨⟨_,_⟩,_,doneL⟩ := Option.bind_eq_some_iff.mp ranL
    obtain ⟨⟨_,_⟩,_,doneR⟩ := Option.bind_eq_some_iff.mp ranR
    cases Option.some.inj doneL
    cases Option.some.inj doneR
    exact ⟨fun _ => WritesWithin.pures _ allowed,fun _ => WritesWithin.pures _ allowed⟩
  | measure input output =>
    simp only [readStep] at ranL ranR
    obtain ⟨⟨_,_⟩,_,doneL⟩ := Option.bind_eq_some_iff.mp ranL
    obtain ⟨⟨_,_⟩,_,doneR⟩ := Option.bind_eq_some_iff.mp ranR
    cases Option.some.inj doneL
    cases Option.some.inj doneR
    simp only [within_measure]
  | discard input =>
    simp only [readStep] at ranL ranR
    obtain ⟨⟨_,_⟩,_,doneL⟩ := Option.bind_eq_some_iff.mp ranL
    obtain ⟨⟨_,_⟩,_,doneR⟩ := Option.bind_eq_some_iff.mp ranR
    cases Option.some.inj doneL
    cases Option.some.inj doneR
    exact ⟨fun _ => WritesWithin.erase_none _ _ allowed,fun _ => WritesWithin.erase_none _ _ allowed⟩
  | reset input output wire =>
    simp only [readStep] at ranL ranR
    obtain ⟨⟨_,_⟩,_,doneL⟩ := Option.bind_eq_some_iff.mp ranL
    obtain ⟨⟨_,_⟩,_,doneR⟩ := Option.bind_eq_some_iff.mp ranR
    cases Option.some.inj doneL
    cases Option.some.inj doneR
    exact ⟨fun _ => reset_has_no_writes _ _ _ allowed,fun _ => reset_has_no_writes _ _ _ allowed⟩
  | constant value output | not input output | xor first second output | and first second output =>
    cases Option.some.inj ranL
    cases Option.some.inj ranR
    rfl
  | branch condition thenOps elseOps quantum phis =>
    simp only [readStep] at ranL ranR
    obtain ⟨⟨_,_⟩,thenL,restL⟩ := Option.bind_eq_some_iff.mp ranL
    obtain ⟨⟨_,_⟩,thenR,restR⟩ := Option.bind_eq_some_iff.mp ranR
    obtain ⟨⟨_,_⟩,elseL,doneL⟩ := Option.bind_eq_some_iff.mp restL
    obtain ⟨⟨_,_⟩,elseR,doneR⟩ := Option.bind_eq_some_iff.mp restR
    cases Option.some.inj doneL
    cases Option.some.inj doneR
    rw [within_branch,within_branch,within_finish,within_finish,within_finish,within_finish,
      same _ _ thenOps _ _ _ _ thenL thenR,same _ _ elseOps _ _ _ _ elseL elseR]

private theorem read_single (fuel : Nat) (initial : Interface) (op : Op) :
    readOps (fuel+1) initial [op] = readStep (readOps fuel) initial op := by
  rw [read_succ]
  unfold layer
  cases result : readStep (readOps fuel) initial op with
  | none => simp [result]
  | some pair =>
    rcases pair with ⟨_,_⟩
    simp [result]

/-- Scope and quantum frame changes affect literal coordinates, but the
ordinary write identities of successful reads follow the original syntax. -/
theorem readOps_same_writes (allowed : Nat → Prop) (fuelL fuelR : Nat) (ops : List Op)
    {initialL initialR finalL finalR : Interface} {eventsL eventsR : List Event}
    (ranL : readOps fuelL initialL ops = some (finalL,eventsL))
    (ranR : readOps fuelR initialR ops = some (finalR,eventsR)) :
    WritesWithin eventsL allowed ↔ WritesWithin eventsR allowed := by
  induction fuelL generalizing fuelR ops initialL initialR finalL finalR eventsL eventsR with
  | zero => cases ranL
  | succ fuelL descend =>
    cases fuelR with
    | zero => cases ranR
    | succ fuelR =>
      induction ops generalizing initialL initialR finalL finalR eventsL eventsR with
      | nil =>
        cases Option.some.inj ranL
        cases Option.some.inj ranR
        rfl
      | cons op rest tail =>
        change readOps (fuelL+1) initialL ([op]++rest) = _ at ranL
        change readOps (fuelR+1) initialR ([op]++rest) = _ at ranR
        rw [RuntimeAdjacentSlices.readOps_append,read_single] at ranL ranR
        obtain ⟨⟨_,_⟩,firstL,restL⟩ := Option.bind_eq_some_iff.mp ranL
        obtain ⟨⟨_,_⟩,firstR,restR⟩ := Option.bind_eq_some_iff.mp ranR
        obtain ⟨⟨_,_⟩,laterL,doneL⟩ := Option.bind_eq_some_iff.mp restL
        obtain ⟨⟨_,_⟩,laterR,doneR⟩ := Option.bind_eq_some_iff.mp restR
        cases Option.some.inj doneL
        cases Option.some.inj doneR
        have first := step_same_writes (readOps fuelL) (readOps fuelR) allowed
          (fun _ _ ops _ _ _ _ => descend fuelR ops) op firstL firstR
        rw [within_append,within_append,first,tail laterL laterR]

#print axioms readOps_same_writes
end Qleisli.RuntimeObservingWrites
