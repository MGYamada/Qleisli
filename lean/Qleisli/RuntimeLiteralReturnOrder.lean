import Qleisli.RuntimeLiteralObservationAction
import Qleisli.RuntimeForestFrameEvidence
import Mathlib.Data.List.Perm.Subperm

/-! Transport a source history through the original checked return order.
Return order changes logical coordinates while the same Raw state is retained.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeLiteralHistory
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite
open Qleisli.RuntimeOriginalBranchJoin (RepresentsOperator)
open Qleisli.Semantics.ObservingAction (History)
open Qleisli.RuntimeForestProduct (referenceAction)
open Qleisli.RuntimeForestOrderedProduct (ordered_product_action product_agrees frame_product_agrees sparseProduct)
open RuntimeForestCode (Frame)
open RuntimeOwnerCodeReindex (dimensionAt reindex_exists)
open RuntimeOwnerMap (Binding Map)

private theorem return_permutation {state inputRoles outputRoles}
    (input : RuntimeOwnerMap.Checked inputRoles state) (output : RuntimeOwnerMap.Checked outputRoles state)
    (read : RuntimeInterval.Computed (RuntimePureBody.reordered outputRoles state input.bindings) output) :
    output.bindings.Perm input.bindings := by
  obtain ⟨work,left,ran⟩ := read
  unfold RuntimePureBody.reordered at ran
  obtain ⟨ordered,middle,order,checked⟩ := bind_success _ _ _ _ _ ran
  have actual := RuntimeBoundaryOwnerEvidence.check_bindings output ⟨middle,left,checked⟩
  have subset := (RuntimeSelectionPartition.order_values input.bindings outputRoles ordered ⟨work,middle,order⟩).1
  rw [← actual] at subset
  have distinct : output.bindings.Nodup :=
    List.Pairwise.of_map (fun binding : Binding => binding.port.token)
      (fun _ _ different equal => different (congrArg (fun binding : Binding => binding.port.token) equal))
      output.tokensDistinct
  have count : input.bindings.length = output.bindings.length := by
    simpa only [List.length_map] using (input.complete.trans output.complete.symm).length_eq
  exact (distinct.subperm subset).perm_of_length_le count.le

/-- Evaluate the original source return order on the logical rows of a history. -/
noncomputable def sourceReturn {Reference : Type} (incoming outgoing : Map) (joint : Nat → Reference → ℂ) :
    Nat → Reference → ℂ :=
  fun logical ref => joint (Qleisli.MixedRadix.recode outgoing incoming (sourceDimension incoming) logical) ref

/-- The actual return-order check only permutes the original owners. Its
source operator retains exact phase and arbitrary reference columns. -/
theorem return_order {state inputRoles outputRoles inputChecked}
    (input : @Frame inputRoles state inputChecked) (outputChecked : RuntimeOwnerMap.Checked outputRoles state)
    (read : RuntimeInterval.Computed (RuntimePureBody.reordered outputRoles state inputChecked.bindings) outputChecked)
    (history : History) (joint : Nat → Nat → ℂ) (represented : RepresentsOperator input history joint) :
    ∃ output : Frame outputChecked,
      RepresentsOperator output history (sourceReturn inputChecked.bindings outputChecked.bindings joint) := by
  have permutation := return_permutation inputChecked outputChecked read
  obtain ⟨codes,found⟩ := reindex_exists input.owners outputChecked.bindings permutation.subset
  obtain ⟨output,kept⟩ := Qleisli.RuntimeForestFrameEvidence.with_ownerCodes outputChecked codes
  have dimension : (sparseProduct codes).dimension = output.code.dimension := by
    rw [← kept]
    exact (product_agrees output.owners).dimension.trans (frame_product_agrees output).dimension.symm
  refine ⟨output,?_⟩
  intro col row bound
  refine (represented col row bound).trans ?_
  change referenceAction input joint row col =
    referenceAction output (sourceReturn inputChecked.bindings outputChecked.bindings joint) row col
  rw [Qleisli.RuntimeNamedOutputOrder.regroup_dense_action input outputChecked.bindings ⟨codes,found⟩ permutation,
    ordered_product_action, kept, dimension, funext (dimensionAt_source input.owners)]
  rfl

#print axioms return_order
end Qleisli.RuntimeLiteralHistory
