import Qleisli.RuntimeCallTraceAllocation
import Qleisli.RuntimeNamedThreePackedOutput
import Qleisli.RuntimeFiniteTargetScatter
import Qleisli.FinitePull

/-! Project complete finite Raw frames along their original wire order.
A caller row decomposes into child and spectator coordinates, even when
the two ordered frames use different physical axis numbers.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeCallTraceProjection
open QleisliKernel QleisliKernel.Qirf
open Semantics.Finite (gather scatter)
open QleisliKernel.FiniteRestriction (pack pack_low pack_high)
open Qleisli.RuntimeForestProduct (gather_append gather_bound)
open Qleisli.RuntimeNamedThreePackedOutput (gather_bijective)

theorem split_axes {parent child spectators : List Nat}
    (partition : parent.Perm (child++spectators)) (unique : parent.Nodup) :
    (child.map parent.idxOf ++ spectators.map parent.idxOf).Perm (List.range parent.length) := by
  have permuted := partition.symm.map parent.idxOf
  rw [List.map_append,RuntimeNamedCallerAction.self_indices _ unique] at permuted
  exact permuted

theorem split_eq {parent child spectators : List Nat}
    (partition : parent.Perm (child++spectators)) (unique : parent.Nodup)
    {left right : Nat} (leftBound : left < 2^parent.length) (rightBound : right < 2^parent.length) :
    left = right ↔
      gather left (child.map parent.idxOf) = gather right (child.map parent.idxOf) ∧
      gather left (spectators.map parent.idxOf) = gather right (spectators.map parent.idxOf) := by
  constructor
  · rintro rfl
    exact ⟨rfl,rfl⟩
  · rintro ⟨sameChild,sameSpectators⟩
    obtain ⟨project,bij,equation⟩ := gather_bijective _ _ (split_axes partition unique)
    let l : Fin (2^parent.length) := ⟨left,leftBound⟩
    let r : Fin (2^parent.length) := ⟨right,rightBound⟩
    have same : gather l.val (child.map parent.idxOf ++ spectators.map parent.idxOf) =
        gather r.val (child.map parent.idxOf ++ spectators.map parent.idxOf) := by
      change gather left _ = gather right _
      simp only [gather_append,sameChild,sameSpectators]
    exact congrArg Fin.val (bij.1 (Fin.ext ((equation l).trans (same.trans (equation r).symm))))

/-- Reindex the finite caller sum by complete child and spectator rows. -/
theorem sum_split {parent child spectators : List Nat}
    (partition : parent.Perm (child++spectators)) (unique : parent.Nodup) (f : Nat → Nat → ℂ) :
    ((List.range (2^parent.length)).map fun row =>
      f (gather row (child.map parent.idxOf)) (gather row (spectators.map parent.idxOf))).sum =
    ((List.range (2^spectators.length)).map fun spectator =>
      ((List.range (2^child.length)).map fun localRow => f localRow spectator).sum).sum := by
  let childAxes := child.map parent.idxOf
  let spectatorAxes := spectators.map parent.idxOf
  let joined := childAxes ++ spectatorAxes
  let width := child.length
  let term := fun row => f (row % 2^width) (row / 2^width)
  obtain ⟨project,bij,equation⟩ := gather_bijective parent.length joined (split_axes partition unique)
  have reindexed : ((List.range (2^parent.length)).map fun row => gather row joined).Perm
      (List.range (2^parent.length)) := by
    have distinct : ((List.range (2^parent.length)).map fun row => gather row joined).Nodup :=
      List.Nodup.map_on (fun first firstIn second secondIn same => by
        let a : Fin (2^parent.length) := ⟨first,List.mem_range.mp firstIn⟩
        let b : Fin (2^parent.length) := ⟨second,List.mem_range.mp secondIn⟩
        exact congrArg Fin.val (bij.1 (Fin.ext ((equation a).trans (same.trans (equation b).symm)))))
        List.nodup_range
    apply (List.perm_ext_iff_of_nodup distinct List.nodup_range).mpr
    intro row
    constructor
    · intro found
      obtain ⟨input,present,rfl⟩ := List.mem_map.mp found
      let index : Fin (2^parent.length) := ⟨input,List.mem_range.mp present⟩
      exact List.mem_range.mpr ((equation index) ▸ (project index).isLt)
    · intro present
      obtain ⟨input,found⟩ := bij.2 ⟨row,List.mem_range.mp present⟩
      exact List.mem_map.mpr ⟨input.val,List.mem_range.mpr input.isLt,
        (equation input).symm.trans (congrArg Fin.val found)⟩
  have packed (row : Nat) : gather row joined = pack width (gather row childAxes) (gather row spectatorAxes) := by
    simp only [joined,gather_append,childAxes,List.length_map,pack,width]
  have parentWidth : parent.length = child.length+spectators.length :=
    partition.length_eq.trans List.length_append
  calc
    _ = ((List.range (2^parent.length)).map fun row => term (gather row joined)).sum := by
      apply Qleisli.Exact.sum_map_congr
      intro row _
      change f (gather row childAxes) (gather row spectatorAxes) = _
      have bounded : gather row childAxes < 2^width := by
        simpa only [childAxes,List.length_map,width] using gather_bound row childAxes
      simp only [term,packed,pack_low _ _ _ bounded,pack_high _ _ _ bounded]
    _ = ((List.range (2^parent.length)).map term).sum := by
      simpa only [List.map_map,Function.comp_def] using (reindexed.map term).sum_eq
    _ = _ := by
      rw [parentWidth,Nat.pow_add,Qleisli.RuntimeNamedHeadCoefficients.sum_blocks]
      apply Qleisli.Exact.sum_map_congr
      intro spectator _
      apply Qleisli.Exact.sum_map_congr
      intro localRow member
      have bounded : localRow < 2^width := List.mem_range.mp member
      change term (pack width localRow spectator) = _
      simp only [term,pack_low _ _ _ bounded,pack_high _ _ _ bounded]

private theorem mapped_axes {parent child wires : List Nat} (inside : wires ⊆ child) :
    RuntimeScatterTransport.mappedAxes (child.map parent.idxOf) (wires.map child.idxOf) =
      wires.map parent.idxOf := by
  unfold RuntimeScatterTransport.mappedAxes
  rw [List.map_map]
  apply List.map_congr_left
  intro wire member
  simp only [Function.comp_def,List.getElem?_map,RuntimeNamedFrameAxes.wireLookup _ (inside member),Option.map_some,
    Option.getD_some]

/-- Overwrite selected wires and then project to the child. The result is
the same literal overwrite in the child's physical row. -/
theorem scatter_project {parent child wires : List Nat} (inside : wires ⊆ child)
    (unique : (child.map parent.idxOf).Nodup) (input replacement : Nat) :
    gather (scatter input (wires.map parent.idxOf) replacement) (child.map parent.idxOf) =
      scatter (gather input (child.map parent.idxOf)) (wires.map child.idxOf) replacement := by
  let selected := child.map parent.idxOf
  let targets := wires.map child.idxOf
  have targetBounds : ∀ axis ∈ targets, axis < child.length := by
    intro axis member
    obtain ⟨wire,present,rfl⟩ := List.mem_map.mp member
    exact List.idxOf_lt_length_of_mem (inside present)
  have bounds : ∀ axis ∈ targets, axis < selected.length := by
    simpa only [selected,List.length_map] using targetBounds
  have scattered := RuntimeScatterTransport.scatter_mapped input (gather input selected) replacement
    selected unique targets bounds
  rw [RuntimeScatterTransport.scatter_gather input selected unique,mapped_axes inside] at scattered
  rw [scattered]
  apply Qleisli.RuntimeFiniteTargetScatter.gather_scatter _ _ _ unique
  apply Qleisli.Finite.Pull.scatter_bound _ _ _ _
  · exact gather_bound _ _
  · exact bounds

#print axioms sum_split
#print axioms scatter_project
end Qleisli.RuntimeCallTraceProjection
