import QleisliKernel.Finite

/-! Exact coordinates for selector sectors. Ordered axes, both control polarities
and the original integer packing are retained; equal width is not type identity.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.FiniteRestriction
open QleisliKernel.Semantics.Finite
open QleisliKernel.Semantics.Exact

def pack (selector low high : Nat) : Nat := low + 2^selector * high

theorem pack_low (selector low high : Nat) (bound : low < 2^selector) :
    pack selector low high % 2^selector = low := by
  simp only [pack, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt bound]

theorem pack_high (selector low high : Nat) (bound : low < 2^selector) :
    pack selector low high / 2^selector = high := by
  rw [pack, Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide)), Nat.div_eq_of_lt bound]
  exact Nat.zero_add high

theorem bit_target (selector low high axis : Nat) (bound : low < 2^selector) :
    bit (pack selector low high) (selector+axis) = bit high axis := by
  unfold bit
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul, pack_high selector low high bound]

theorem bit_selector (selector low high axis : Nat) (axisBound : axis < selector) :
    bit (pack selector low high) axis = bit low axis := by
  obtain ⟨rest, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt axisBound)
  have factor : 2^(axis+1+rest) * high = 2^axis * (2 * (2^rest * high)) := by
    simp [Nat.pow_add, Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  unfold bit pack
  rw [factor, Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide))]
  exact Nat.add_mul_mod_self_left _ _ _

def selectorControls (selector : Nat) (controls : List Control) : List Control :=
  controls.filter (fun control => control.index < selector)

def targetControls (selector : Nat) (controls : List Control) : List Control :=
  (controls.filter (fun control => selector ≤ control.index)).map
    (fun control => {control with index := control.index-selector})

/-- Both polarities and target-local controls retain their original predicate.
This identity holds for every control list; circuit validity remains separate. -/
theorem enabled_pack (selector low high : Nat) (bound : low < 2^selector)
    (controls : List Control) :
    enabled controls (pack selector low high) =
      (enabled (selectorControls selector controls) low &&
        enabled (targetControls selector controls) high) := by
  induction controls with
  | nil => rfl
  | cons control controls ih =>
    by_cases before : control.index < selector
    · have after : ¬ selector ≤ control.index := by omega
      have step := congrArg (fun next => ((bit low control.index == 1) == control.whenOne) && next) ih
      simpa [enabled, selectorControls, targetControls, before, after,
        bit_selector selector low high control.index before, Bool.and_assoc] using step
    · have after : selector ≤ control.index := by omega
      have actual : bit (pack selector low high) control.index = bit high (control.index-selector) := by
        have h := bit_target selector low high (control.index-selector) bound
        simpa only [Nat.add_sub_of_le after] using h
      have step := congrArg (fun next => ((bit high (control.index-selector) == 1) == control.whenOne) && next) ih
      simpa [enabled, selectorControls, targetControls, before, after, actual,
        Bool.and_assoc, Bool.and_left_comm] using step

theorem zipIdx_map (f : α → β) (xs : List α) (start : Nat) :
    (xs.map f).zipIdx start = (xs.zipIdx start).map (fun pair => (f pair.1,pair.2)) := by
  induction xs generalizing start with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.zipIdx_cons, ih]

theorem bit_high_axis (selector low high axis : Nat) (bound : low < 2^selector)
    (after : selector ≤ axis) :
    bit (pack selector low high) axis = bit high (axis-selector) := by
  simpa only [Nat.add_sub_of_le after] using bit_target selector low high (axis-selector) bound

theorem gather_pack (selector low high : Nat) (bound : low < 2^selector)
    (axes : List Nat) (after : ∀ axis ∈ axes, selector ≤ axis) :
    gather (pack selector low high) axes = gather high (axes.map (·-selector)) := by
  unfold gather
  rw [zipIdx_map]
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro pair present
  have member : pair.1 ∈ axes := by
    have h : pair.1 ∈ axes.zipIdx.map Prod.fst := List.mem_map.mpr ⟨pair,present,rfl⟩
    simpa only [List.zipIdx_map_fst] using h
  rw [bit_high_axis selector low high pair.1 bound (after pair.1 member)]
  rfl

theorem bit_weight_le (label axis : Nat) : bit label axis * 2^axis ≤ label := by
  exact Nat.le_trans (Nat.mul_le_mul_right (2^axis) (Nat.mod_le (label/2^axis) 2))
    (Nat.div_mul_le_self label (2^axis))

theorem update_pack (selector low high axis value place : Nat) (bound : low < 2^selector) :
    pack selector low high - bit (pack selector low high) (selector+axis) * 2^(selector+axis)
      + bit value place * 2^(selector+axis) =
    pack selector low (high - bit high axis * 2^axis + bit value place * 2^axis) := by
  rw [bit_target selector low high axis bound, Nat.pow_add]
  have scaled := Nat.mul_le_mul_left (2^selector) (bit_weight_le high axis)
  have subtractAxis : bit high axis * (2^selector * 2^axis) =
      2^selector * (bit high axis * 2^axis) := by ac_rfl
  have addAxis : bit value place * (2^selector * 2^axis) =
      2^selector * (bit value place * 2^axis) := by ac_rfl
  simp only [pack]
  rw [subtractAxis, addAxis]
  rw [Nat.add_sub_assoc scaled, ← Nat.mul_sub, Nat.mul_add]
  ac_rfl

/-- Fold the actual scatter updates, retaining their original ordered positions.
No sorting, axis normalization or predicate about a producer's summary is used. -/
theorem scatterFold_pack (selector low high value : Nat) (bound : low < 2^selector)
    (pairs : List (Nat × Nat)) (after : ∀ pair ∈ pairs, selector ≤ pair.1) :
    pairs.foldl (fun state pair =>
      state - bit state pair.1 * 2^pair.1 + bit value pair.2 * 2^pair.1) (pack selector low high) =
    pack selector low (pairs.foldl (fun state pair =>
      state - bit state (pair.1-selector) * 2^(pair.1-selector) +
        bit value pair.2 * 2^(pair.1-selector)) high) := by
  induction pairs generalizing high with
  | nil => rfl
  | cons pair pairs ih =>
    have head : selector ≤ pair.1 := after pair (List.mem_cons_self ..)
    have actual := update_pack selector low high (pair.1-selector) value pair.2 bound
    rw [Nat.add_sub_of_le head] at actual
    simp only [List.foldl_cons]
    rw [actual]
    apply ih
    intro item present
    exact after item (List.mem_cons_of_mem pair present)

theorem scatter_pack (selector low high value : Nat) (bound : low < 2^selector)
    (axes : List Nat) (after : ∀ axis ∈ axes, selector ≤ axis) :
    scatter (pack selector low high) axes value =
      pack selector low (scatter high (axes.map (·-selector)) value) := by
  unfold scatter
  rw [zipIdx_map, List.foldl_map]
  apply scatterFold_pack selector low high value bound
  intro pair present
  have member : pair.1 ∈ axes := by
    have h : pair.1 ∈ axes.zipIdx.map Prod.fst := List.mem_map.mpr ⟨pair,present,rfl⟩
    simpa only [List.zipIdx_map_fst] using h
  exact after pair.1 member

end QleisliKernel.FiniteRestriction
