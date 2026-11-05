import QleisliKernel.Raw.ObservationLayer

/-! One actual observing-reader step retains dependency agreement. Both
original branch reads and their final phi permutations remain present.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Raw.ObservationAgreement
open QleisliKernel QleisliKernel.Semantics.Finite
open QleisliKernel.Raw.EventTransport

theorem readStep_agrees (left right : List Dependency) (fuel : Nat) (recurse : Reader)
    (recursive : ∀ state ops, OpsAgree left right fuel ops →
      ReadAgrees left right fuel (recurse state ops))
    (state : Interface) (op : Op) (same : OneAgrees left right fuel op) :
    ReadAgrees left right (fuel+1) (readStep recurse state op) := by
  cases op with
  | pure operation =>
    intro actual original
    obtain ⟨⟨next,events⟩,read,finish⟩ := Option.bind_eq_some_iff.mp original
    have equal := Option.some.inj finish
    subst actual
    exact pure_events fuel events
      (RawTraceAgreement.step left right state operation same ⟨next,events⟩ read)
  | measure input output =>
    apply bind_agrees
    intro pair
    rcases pair with ⟨port,next⟩
    apply returned
    intro event member
    have equal := List.mem_singleton.mp member
    subst event
    exact True.intro
  | discard input =>
    apply bind_agrees
    intro pair
    rcases pair with ⟨port,next⟩
    apply returned
    intro event member
    have equal := List.mem_singleton.mp member
    subst event
    exact True.intro
  | reset input output wire =>
    apply bind_agrees
    intro pair
    rcases pair with ⟨port,next⟩
    apply returned
    intro event member
    rcases List.mem_cons.mp member with equal | member
    · subst event; exact True.intro
    · have equal := List.mem_singleton.mp member
      subst event
      exact True.intro
  | constant value output =>
    apply returned
    intro event member
    have equal := List.mem_singleton.mp member
    subst event
    exact True.intro
  | not input output =>
    apply returned
    intro event member
    have equal := List.mem_singleton.mp member
    subst event
    exact True.intro
  | xor first second output =>
    apply returned
    intro event member
    have equal := List.mem_singleton.mp member
    subst event
    exact True.intro
  | and first second output =>
    apply returned
    intro event member
    have equal := List.mem_singleton.mp member
    subst event
    exact True.intro
  | branch condition zero one quantum classical =>
    intro actual original
    obtain ⟨⟨zeroState,zeroEvents⟩,zeroRead,remaining⟩ := Option.bind_eq_some_iff.mp original
    obtain ⟨⟨oneState,oneEvents⟩,oneRead,finish⟩ := Option.bind_eq_some_iff.mp remaining
    have zeroAgreement := recursive state zero same.1 ⟨zeroState,zeroEvents⟩ zeroRead
    have oneAgreement := recursive state one same.2 ⟨oneState,oneEvents⟩ oneRead
    have equal := Option.some.inj finish
    subst actual
    intro event member
    have equal := List.mem_singleton.mp member
    subst event
    exact ⟨events_append fuel zeroEvents _ zeroAgreement (reorder left right fuel zeroState.frame.length _),
      events_append fuel oneEvents _ oneAgreement (reorder left right fuel oneState.frame.length _)⟩

end QleisliKernel.Raw.ObservationAgreement
