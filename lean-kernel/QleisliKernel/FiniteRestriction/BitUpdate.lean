import QleisliKernel.FiniteRestriction.Coordinates

/-! Read and replace one bit of a physical basis label. These coordinate laws
have no dependency on runtime source checking or on coefficient evaluation.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.FiniteRestriction.BitUpdate
open QleisliKernel.Semantics.Finite

def write (label axis replacement : Nat) : Nat :=
  label-bit label axis*2^axis+replacement*2^axis

theorem bit_lt (label axis : Nat) : bit label axis < 2 := Nat.mod_lt _ (by decide)

theorem bit_pack_one (low high index : Nat) (bound : low < 2) :
    bit (pack 1 low high) index = if index = 0 then low else bit high (index-1) := by
  cases index with
  | zero =>
    have same := FiniteRestriction.bit_selector 1 low high 0 (by decide)
    simpa [bit,Nat.mod_eq_of_lt bound] using same
  | succ index =>
    have same := FiniteRestriction.bit_target 1 low high index bound
    simpa [Nat.add_comm] using same

/-- Isolate the overwritten bit using the already proved low/high packing
coordinates. No fixed width or concrete maximum label is normalized. -/
private theorem write_pack (label axis replacement : Nat) (bound : replacement < 2) :
    write label axis replacement = pack axis (label % 2^axis)
      (pack 1 replacement (label / 2^axis / 2)) := by
  have lower : label % 2^axis < 2^axis := Nat.mod_lt _ (Nat.two_pow_pos _)
  have original : pack axis (label % 2^axis) (label / 2^axis) = label := Nat.mod_add_div _ _
  have changed := FiniteRestriction.update_pack axis (label % 2^axis) (label / 2^axis)
    0 replacement 0 lower
  rw [original] at changed
  have lowBit : bit replacement 0 = replacement := by simp [bit,Nat.mod_eq_of_lt bound]
  have highBit : bit (label / 2^axis) 0 = label / 2^axis % 2 := by simp [bit]
  simp only [Nat.add_zero,Nat.pow_zero,Nat.mul_one,lowBit,highBit] at changed
  have remaining : label / 2^axis-label / 2^axis % 2 = 2*(label / 2^axis / 2) := by
    have division := Nat.mod_add_div (label / 2^axis) 2
    omega
  calc
    write label axis replacement = pack axis (label % 2^axis)
        (label / 2^axis-label / 2^axis % 2+replacement) := changed
    _ = pack axis (label % 2^axis) (pack 1 replacement (label / 2^axis / 2)) := by
      rw [remaining]
      unfold pack
      simp only [Nat.pow_one]
      rw [Nat.add_comm (2*(label / 2^axis / 2)) replacement]

theorem bit_write (label axis replacement query : Nat) (bound : replacement < 2) :
    bit (write label axis replacement) query = if query = axis then replacement else bit label query := by
  have lower : label % 2^axis < 2^axis := Nat.mod_lt _ (Nat.two_pow_pos _)
  have original : pack axis (label % 2^axis) (label / 2^axis) = label := Nat.mod_add_div _ _
  by_cases before : query < axis
  · have actual := FiniteRestriction.bit_selector axis (label % 2^axis)
      (pack 1 replacement (label / 2^axis / 2)) query before
    rw [← write_pack label axis replacement bound] at actual
    have old := FiniteRestriction.bit_selector axis (label % 2^axis) (label / 2^axis) query before
    rw [original] at old
    rw [if_neg (Nat.ne_of_lt before)]
    exact actual.trans old.symm
  · have index : axis+(query-axis) = query := by omega
    have actual := FiniteRestriction.bit_target axis (label % 2^axis)
      (pack 1 replacement (label / 2^axis / 2)) (query-axis) lower
    rw [index,← write_pack label axis replacement bound,bit_pack_one _ _ _ bound] at actual
    have old := FiniteRestriction.bit_target axis (label % 2^axis) (label / 2^axis) (query-axis) lower
    rw [index,original] at old
    have upper : pack 1 (label / 2^axis % 2) (label / 2^axis / 2) = label / 2^axis := Nat.mod_add_div _ _
    have previous := bit_pack_one (label / 2^axis % 2) (label / 2^axis / 2)
      (query-axis) (Nat.mod_lt _ (by decide))
    rw [upper] at previous
    rw [previous] at old
    by_cases same : query = axis
    · simpa only [same,Nat.sub_self,if_pos rfl] using actual
    · have different : query-axis ≠ 0 := by omega
      rw [if_neg different] at actual old
      rw [if_neg same]
      exact actual.trans old.symm

end QleisliKernel.FiniteRestriction.BitUpdate
