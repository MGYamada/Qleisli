import QleisliKernel.Raw.ObservationStep

/-! Dependency agreement through the complete actual observing reader.
The fold invariant retains every emitted event in both branch subtrees.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Raw.ObservationAgreement
open QleisliKernel QleisliKernel.Semantics.Finite
open QleisliKernel.Raw.EventTransport

theorem layer_agrees (left right : List Dependency) (fuel : Nat) (recurse : Reader)
    (recursive : ∀ state ops, OpsAgree left right fuel ops →
      ReadAgrees left right fuel (recurse state ops))
    (initial : Interface) (operations : List Op)
    (same : OpsAgree left right (fuel+1) operations) :
    ReadAgrees left right (fuel+1) (layer recurse initial operations) := by
  unfold layer ReadAgrees
  apply fold_property operations _ (fun (result : Result) => EventsAgree left right (fuel+1) result.2)
  · intro op member before held after completed
    rcases before with ⟨state,events⟩
    obtain ⟨⟨next,added⟩,read,finish⟩ := Option.bind_eq_some_iff.mp completed
    have equal := Option.some.inj finish
    subst after
    exact events_append (fuel+1) events added held
      (readStep_agrees left right fuel recurse recursive state op (same op member) ⟨next,added⟩ read)
  · exact events_nil left right (fuel+1)

theorem read_ops (left right : List Dependency) (fuel : Nat) :
    ∀ initial operations, OpsAgree left right fuel operations →
      ReadAgrees left right fuel (Semantics.Observation.readOps fuel initial operations) := by
  induction fuel with
  | zero =>
    intro initial operations same actual impossible
    change none = some actual at impossible
    cases impossible
  | succ fuel ih =>
    intro initial operations same
    rw [read_succ fuel initial operations]
    exact layer_agrees left right fuel (Semantics.Observation.readOps fuel) ih initial operations same

end QleisliKernel.Raw.ObservationAgreement
