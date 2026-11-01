import QleisliKernel.Raw.RawAgreement

/-! Dependency agreement for events read from original Raw operations.
The Option property requires a successful literal reader result.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Raw.RawTraceAgreement
open QleisliKernel QleisliKernel.Semantics.Finite
open QleisliKernel.Raw.DependencyTransport QleisliKernel.Raw.EventTransport QleisliKernel.Raw.RawAgreement
abbrev Interface := Semantics.RawTrace.Interface
abbrev Event := Semantics.Raw.Event

def Traced (left right : List Dependency) (result : Option (Interface × List Event)) : Prop :=
  ∀ actual, result = some actual → ∀ event, event ∈ actual.2 → ActionAgrees left right event

theorem bind_traced {left right : List Dependency} {α : Type} (input : Option α)
    (next : α → Option (Interface × List Event))
    (same : ∀ actual, Traced left right (next actual)) :
    Traced left right (input.bind next) := by
  cases input with
  | none => intro actual impossible; cases impossible
  | some actual => exact same actual

theorem returned {left right : List Dependency} (state : Interface) (events : List Event)
    (same : ∀ event, event ∈ events → ActionAgrees left right event) :
    Traced left right (some (state,events)) := by
  intro actual original
  have equal := Option.some.inj original
  subst actual
  exact same

theorem empty (left right : List Dependency) (state : Interface) :
    Traced left right (some (state,[])) := by
  apply returned
  intro event member
  cases member

theorem conditional {left right : List Dependency} (condition : Prop) [Decidable condition]
    (first second : Option (Interface × List Event))
    (yes : Traced left right first) (no : Traced left right second) :
    Traced left right (if condition then first else second) := by
  split
  · exact yes
  · exact no

theorem circuit {left right : List Dependency} (state : Interface) (bits : Nat) (steps : List Step)
    (same : StepsAgree left right steps) :
    Traced left right (some (state,[.circuit bits steps])) := by
  apply returned
  intro event member
  have equal := List.mem_singleton.mp member
  subst event
  exact same

theorem step (left right : List Dependency) (state : Interface) (operation : Semantics.Raw.Op)
    (same : OpAgrees left right operation) :
    Traced left right (Semantics.RawTrace.step state operation) := by
  cases operation with
  | init0 output wire =>
    apply returned
    intro event member
    have equal := List.mem_singleton.mp member
    subst event
    exact True.intro
  | gate value input output =>
    apply bind_traced
    intro pair
    rcases pair with ⟨port,next⟩
    apply circuit
    intro step member
    have equal := List.mem_singleton.mp member
    subst step
    exact RawAgreement.gate left right value _
  | cnot control target controlOut targetOut =>
    apply bind_traced
    intro pair
    rcases pair with ⟨control,next⟩
    apply bind_traced
    intro pair
    rcases pair with ⟨target,next⟩
    apply circuit
    intro step member
    have equal := List.mem_singleton.mp member
    subst step
    exact with_controls (RawAgreement.gate left right .x _) _
  | toffoli first second target firstOut secondOut targetOut =>
    apply bind_traced
    intro pair
    rcases pair with ⟨first,next⟩
    apply bind_traced
    intro pair
    rcases pair with ⟨second,next⟩
    apply bind_traced
    intro pair
    rcases pair with ⟨target,next⟩
    apply circuit
    intro step member
    have equal := List.mem_singleton.mp member
    subst step
    exact with_controls (RawAgreement.gate left right .x _) _
  | quantumIf control target controlOut targetOut zero one =>
    apply bind_traced
    intro pair
    rcases pair with ⟨control,next⟩
    apply bind_traced
    intro pair
    rcases pair with ⟨target,next⟩
    apply circuit
    intro step member
    rcases List.mem_append.mp member with zeroMember | oneMember
    · obtain ⟨original,_,rfl⟩ := List.mem_map.mp zeroMember
      exact with_controls (RawAgreement.localize (RawAgreement.unitary left right original) _) _
    · obtain ⟨original,_,rfl⟩ := List.mem_map.mp oneMember
      exact with_controls (RawAgreement.localize (RawAgreement.unitary left right original) _) _
  | split input first second width =>
    apply bind_traced
    intro pair
    rcases pair with ⟨port,next⟩
    exact empty left right _
  | join first second output =>
    apply bind_traced
    intro pair
    rcases pair with ⟨first,next⟩
    apply bind_traced
    intro pair
    rcases pair with ⟨second,next⟩
    exact empty left right _
  | liftBasis input output wires table =>
    apply bind_traced
    intro pair
    rcases pair with ⟨port,next⟩
    apply returned
    intro event member
    have equal := List.mem_singleton.mp member
    subst event
    exact True.intro
  | applyUnitary input output steps =>
    apply bind_traced
    intro pair
    rcases pair with ⟨port,next⟩
    apply circuit
    exact RawAgreement.localize_steps steps same _
  | certifiedCompute input output ancilla table uses logical =>
    apply bind_traced
    intro pair
    rcases pair with ⟨port,next⟩
    apply returned
    intro event member
    have equal := List.mem_singleton.mp member
    subst event
    exact same
  | computeUseUncompute input output targets ancilla table uses =>
    apply bind_traced
    intro pair
    rcases pair with ⟨source,next⟩
    apply bind_traced
    intro pair
    rcases pair with ⟨ports,next⟩
    apply returned
    intro event member
    have equal := List.mem_singleton.mp member
    subst event
    exact True.intro
  | packUnit output => exact empty left right _
  | unpackUnit input =>
    apply bind_traced
    intro pair
    rcases pair with ⟨port,next⟩
    apply conditional
    · exact empty left right _
    · intro actual impossible; cases impossible

end QleisliKernel.Raw.RawTraceAgreement
