import Qleisli.RuntimeTargetScatter
import Qleisli.RuntimeNamedHeadCoefficients
import Qleisli.RuntimeNamedSelectionFrames
import Qleisli.RuntimeNamedCallerAction

/-! Exact spectator coefficients outside a real selected owner block.
Logical ownership and physical disjointness remain distinct. This changes no
Raw event, bounded computation or accepted capability.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeNamedBlockSpectators
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Semantics.Exact
open QleisliKernel.Semantics.Finite (gather scatter)
open RuntimeOwnerMap (Map Binding)
open RuntimeForestCode
open Qleisli.Semantics.Exact Qleisli.RuntimeForestProduct Qleisli.RuntimeForestOrderedProduct

theorem checked_axes_unique {roles state} (checked : RuntimeOwnerMap.Checked roles state)
    (valid : Raw.stateValid state.quantum = true) :
    (forestAxes state.quantum.frame checked.bindings).Nodup := by
  have original := Raw.Ownership.valid _ valid
  have ports := List.Perm.flatMap_right (fun port : Semantics.Raw.Port => port.wires) checked.complete
  have wires : (checked.bindings.flatMap (fun binding => binding.port.wires)).Nodup := by
    simpa only [List.flatMap_map] using ports.symm.nodup original.exclusive
  have covered (wire : Nat) (member : wire ∈ checked.bindings.flatMap (fun binding => binding.port.wires)) :
      wire ∈ state.quantum.frame :=
    original.covered wire (ports.mem_iff.mp (by simpa only [List.flatMap_map] using member))
  unfold forestAxes
  exact List.Nodup.map_on (fun wire member _ _ equal => (List.idxOf_inj (covered wire member)).mp equal) wires

/-- The true full caller partition supplies disjoint selected/spectator axes.
It never supplies uniqueness of empty-wire logical owners from physical axes. -/
theorem partition_axes_disjoint {roles state} (checked : RuntimeOwnerMap.Checked roles state)
    (valid : Raw.stateValid state.quantum = true) (selected spectators : Map)
    (permutation : (selected++spectators).Perm checked.bindings) :
    (forestAxes state.quantum.frame spectators).Disjoint (forestAxes state.quantum.frame selected) := by
  have raw := List.Perm.flatMap_right (fun binding : Binding => binding.port.wires) permutation
  have reordered := raw.map state.quantum.frame.idxOf
  have unique : (forestAxes state.quantum.frame (selected++spectators)).Nodup :=
    reordered.nodup_iff.mpr (checked_axes_unique checked valid)
  have split : (forestAxes state.quantum.frame selected ++ forestAxes state.quantum.frame spectators).Nodup := by
    simpa only [forestAxes,List.flatMap_append,List.map_append] using unique
  exact List.disjoint_left.mpr (fun axis spectator chosen =>
    (List.nodup_append.mp split).2.2 axis chosen axis spectator rfl)

theorem coefficients_scatter (frame : List Nat) {bindings} (owners : OwnerCodes bindings)
    (selected : List Nat) (disjoint : (forestAxes frame bindings).Disjoint selected)
    (physical replacement logical : Nat) :
    coefficients frame owners (scatter physical selected replacement) logical =
      coefficients frame owners physical logical := by
  induction owners generalizing logical with
  | nil => rfl
  | @cons binding bindings first rest ih =>
    have axes : forestAxes frame (binding::bindings) =
        binding.port.wires.map frame.idxOf ++ forestAxes frame bindings := by
      simp only [forestAxes,List.flatMap_cons,List.map_append]
    rw [axes] at disjoint
    have head : (binding.port.wires.map frame.idxOf).Disjoint selected :=
      List.disjoint_left.mpr (fun axis member chosen =>
        List.disjoint_left.mp disjoint (List.mem_append.mpr (Or.inl member)) chosen)
    have tail : (forestAxes frame bindings).Disjoint selected :=
      List.disjoint_left.mpr (fun axis member chosen =>
        List.disjoint_left.mp disjoint (List.mem_append.mpr (Or.inr member)) chosen)
    simp only [coefficients]
    rw [RuntimeTargetScatter.gather_disjoint physical replacement selected _ head,ih tail]

#print axioms checked_axes_unique
#print axioms partition_axes_disjoint
#print axioms coefficients_scatter
end Qleisli.RuntimeNamedBlockSpectators
