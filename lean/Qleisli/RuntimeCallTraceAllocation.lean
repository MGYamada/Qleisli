import Qleisli.RuntimeCallTraceFrames
import Qleisli.RuntimeForestProduct

/-! The original caller and child allocate the same zero-valued wire.
Their complete ordered projections retain every spectator coordinate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeCallTraceAllocation
open QleisliKernel QleisliKernel.Qirf
open Semantics.Finite (bit gather)
open Semantics.Raw (Port)
open Semantics.RawTrace (Interface axes)
open Qleisli.RuntimeCallTraceFrames (Partition WireOrder allocated)
open Qleisli.RuntimeForestProduct (gather_append gather_bound)

theorem old_axes (old extra wires : List Nat) (inside : wires ⊆ old) :
    wires.map (old++extra).idxOf = wires.map old.idxOf := by
  apply List.map_congr_left
  intro wire member
  exact List.idxOf_append_of_mem (inside member)

private theorem bit_above (label bits axis : Nat) (bound : label < 2^bits)
    (above : bits ≤ axis) : bit label axis = 0 := by
  have power : 2^bits ≤ 2^axis := Nat.pow_le_pow_right (by decide) above
  simp [bit,Nat.div_eq_of_lt (Nat.lt_of_lt_of_le bound power)]

theorem gather_zero (label : Nat) (indices : List Nat) (zeros : ∀ axis ∈ indices, bit label axis = 0) :
    gather label indices = 0 := by
  unfold gather
  have equal : (indices.zipIdx.map (fun pair => bit label pair.1 * 2^pair.2)) =
      indices.zipIdx.map (fun _ => 0) := by
    apply List.map_congr_left
    intro pair member
    have axis : pair.1 ∈ indices := by
      simpa only [List.zipIdx_map_fst] using (List.mem_map_of_mem (f := Prod.fst) member)
    simp only [zeros pair.1 axis,Nat.zero_mul]
  rw [equal]
  simp

/-- A finite row of the old frame has zero bits in the newly appended
coordinates, even when the retained child axes have a different order. -/
theorem gather_extended (old kept extra : List Nat) (inside : kept ⊆ old)
    (fresh : old.Disjoint extra) (row : Nat) (bound : row < 2^old.length) :
    gather row ((kept++extra).map (old++extra).idxOf) = gather row (kept.map old.idxOf) := by
  rw [List.map_append,old_axes old extra kept inside,gather_append]
  have zero := gather_zero row (extra.map (old++extra).idxOf) (by
    intro axis member
    obtain ⟨wire,present,rfl⟩ := List.mem_map.mp member
    have absent : wire ∉ old := fun inside => List.disjoint_left.mp fresh inside present
    rw [List.idxOf_append_of_notMem absent]
    exact bit_above row old.length _ bound (by omega))
  simp only [zero,Nat.mul_zero,Nat.add_zero]

private theorem high_bit (row width : Nat) (bound : row < 2^(width+1)) :
    bit row width = 0 ↔ row < 2^width := by
  have positive : 0 < 2^width := Nat.pow_pos (by decide)
  have quotient : row / 2^width < 2 := by
    apply (Nat.div_lt_iff_lt_mul positive).2
    simpa only [Nat.pow_succ,Nat.mul_comm] using bound
  unfold bit
  rw [Nat.mod_eq_of_lt quotient]
  exact Nat.div_eq_zero_iff_lt positive

/-- Evaluate both original initialization events on their exact frames. The
zero-wire check and the unchanged spectator coordinate agree on every row. -/
theorem allocation_correlated (parent child : Interface) (spectators : List Port)
    (partition : Partition parent child spectators) (output wire : Nat) (fresh : wire ∉ parent.frame)
    (dependencies : List Semantics.Finite.Dependency) (joint : Nat → Nat → ℂ) (row : Nat)
    (bound : row < 2^(allocated parent output wire).frame.length) :
    let after := allocated parent output wire
    let localAfter := allocated child output wire
    Qleisli.Semantics.RawAction.event dependencies (.init0 parent.frame.length)
      (fun input => joint (gather input (axes parent child.frame))
        (gather input (axes parent (WireOrder spectators)))) row =
    Qleisli.Semantics.RawAction.event dependencies (.init0 child.frame.length)
      (fun input => joint input (gather row (axes after (WireOrder spectators))))
      (gather row (axes after localAfter.frame)) := by
  intro after localAfter
  have childInside : child.frame ⊆ parent.frame := fun _ member =>
    partition.frame.mem_iff.mpr (List.mem_append_left _ member)
  have spectatorInside : WireOrder spectators ⊆ parent.frame := fun _ member =>
    partition.frame.mem_iff.mpr (List.mem_append_right _ member)
  have sameChild : axes after child.frame = axes parent child.frame :=
    old_axes parent.frame [wire] child.frame childInside
  have sameSpectators : axes after (WireOrder spectators) = axes parent (WireOrder spectators) :=
    old_axes parent.frame [wire] (WireOrder spectators) spectatorInside
  have wireIndex : after.frame.idxOf wire = parent.frame.length := by
    change (parent.frame++[wire]).idxOf wire = _
    rw [List.idxOf_append_of_notMem fresh,List.idxOf_cons_self,Nat.add_zero]
  have newAxes : axes after localAfter.frame = axes parent child.frame ++ [parent.frame.length] := by
    change (child.frame++[wire]).map after.frame.idxOf = _
    rw [List.map_append,show child.frame.map after.frame.idxOf = _ from sameChild,
      List.map_singleton,wireIndex]
  have localRow : gather row (axes after localAfter.frame) =
      gather row (axes parent child.frame) + 2^child.frame.length * bit row parent.frame.length := by
    rw [newAxes,gather_append]
    simp only [axes,List.length_map,RuntimeTargetScatter.gather_one]
  have localBound : gather row (axes parent child.frame) < 2^child.frame.length := by
    simpa only [axes,List.length_map] using gather_bound row (axes parent child.frame)
  have rowBound : row < 2^(parent.frame.length+1) := by
    simpa only [allocated,List.length_append,List.length_singleton] using bound
  have zero := high_bit row parent.frame.length rowBound
  simp only [Qleisli.Semantics.RawAction.event,localRow,sameSpectators]
  by_cases inside : row < 2^parent.frame.length
  · simp only [if_pos inside,zero.mpr inside,Nat.mul_zero,Nat.add_zero,if_pos localBound]
  · have nonzero : bit row parent.frame.length ≠ 0 := fun no => inside (zero.mp no)
    have outside : ¬ gather row (axes parent child.frame) +
        2^child.frame.length * bit row parent.frame.length < 2^child.frame.length := by
      have large := Nat.mul_le_mul_left (2^child.frame.length) (Nat.one_le_iff_ne_zero.mpr nonzero)
      omega
    simp only [if_neg inside,if_neg outside]

#print axioms allocation_correlated
end Qleisli.RuntimeCallTraceAllocation
