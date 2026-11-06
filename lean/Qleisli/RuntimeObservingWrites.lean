import QleisliKernel.Semantics.Observation

/-! The identities written by an independent observing trace, including both
recursive arm traces and the actual classical phi destinations.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeObservingWrites
open QleisliKernel.Semantics.Observation (Event)

inductive WritesId : Event → Nat → Prop where
  | measure (bits : Nat) (axes : List Nat) (output : Nat) : WritesId (.erase bits axes (some output)) output
  | classical (expression : QleisliKernel.Semantics.Observation.Expr) (output : Nat) :
      WritesId (.classical expression output) output
  | thenArm {condition left right phis event id} (member : event ∈ left) (writes : WritesId event id) :
      WritesId (.branch condition left right phis) id
  | elseArm {condition left right phis event id} (member : event ∈ right) (writes : WritesId event id) :
      WritesId (.branch condition left right phis) id
  | phi {condition left right phis item} (member : item ∈ phis) :
      WritesId (.branch condition left right phis) item.output

def WritesWithin (events : List Event) (allowed : Nat → Prop) : Prop :=
  ∀ ⦃event⦄, event ∈ events → ∀ ⦃id⦄, WritesId event id → allowed id

theorem WritesWithin.empty (allowed : Nat → Prop) : WritesWithin [] allowed := by
  intro event member
  cases member

theorem WritesWithin.singleton {event : Event} {allowed : Nat → Prop}
    (writes : ∀ ⦃id⦄, WritesId event id → allowed id) : WritesWithin [event] allowed := by
  intro item member id emits
  cases List.mem_singleton.mp member
  exact writes emits

theorem WritesWithin.pures (operations : List QleisliKernel.Semantics.Raw.Event) (allowed : Nat → Prop) :
    WritesWithin (operations.map Event.pure) allowed := by
  intro event member id writes
  obtain ⟨operation,_inside,rfl⟩ := List.mem_map.mp member
  cases writes

theorem WritesWithin.erase_none (bits : Nat) (axes : List Nat) (allowed : Nat → Prop) :
    WritesWithin [.erase bits axes none] allowed :=
  WritesWithin.singleton (by intro id writes; cases writes)

theorem WritesWithin.append {left right : List Event} {allowed : Nat → Prop}
    (first : WritesWithin left allowed) (second : WritesWithin right allowed) : WritesWithin (left++right) allowed := by
  intro event member id writes
  rcases List.mem_append.mp member with inside | inside
  · exact first inside writes
  · exact second inside writes

theorem WritesWithin.mono {events : List Event} {original target : Nat → Prop}
    (writes : WritesWithin events original) (inclusion : ∀ ⦃id⦄, original id → target id) :
    WritesWithin events target := by
  intro event member id emitted
  exact inclusion (writes member emitted)

end Qleisli.RuntimeObservingWrites
