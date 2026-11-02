import QleisliKernel.Qirf.RuntimeCoefficientTransport

/-! Coordinate laws for literal selected-wire scatter, including reversed and
noncontiguous caller axes. These proofs use the actual Nat gather/scatter and
leave every unselected bit unchanged. They perform no scalar arithmetic,
allocate no joined matrix and grant no source/native acceptance authority.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeScatterTransport
open QleisliKernel Finite Semantics.Finite Semantics.Exact
open QleisliKernel.FiniteRestriction (pack)

def write (label axis replacement : Nat) : Nat :=
  label-bit label axis*2^axis+replacement*2^axis

theorem bit_lt (label axis : Nat) : bit label axis < 2 := Nat.mod_lt _ (by decide)

private theorem bit_pack_one (low high index : Nat) (bound : low < 2) :
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

private def writes (pairs : List (Nat × Nat)) (label value : Nat) : Nat :=
  pairs.foldl (fun current pair => write current pair.1 (bit value pair.2)) label

private theorem writes_outside (pairs : List (Nat × Nat)) (label value query : Nat)
    (outside : query ∉ pairs.map (·.1)) : bit (writes pairs label value) query = bit label query := by
  induction pairs generalizing label with
  | nil => rfl
  | cons first rest ih =>
    have notFirst : query ≠ first.1 := by
      intro same
      apply outside
      simp [same]
    have notRest : query ∉ rest.map (·.1) := by
      intro member
      exact outside (List.mem_cons_of_mem _ member)
    change bit (writes rest (write label first.1 (bit value first.2)) value) query = _
    rw [ih _ notRest,bit_write label first.1 (bit value first.2) query (bit_lt _ _),if_neg notFirst]

private theorem writes_at (pairs : List (Nat × Nat)) (label value query position : Nat)
    (unique : (pairs.map (·.1)).Nodup) (present : (query,position) ∈ pairs) :
    bit (writes pairs label value) query = bit value position := by
  induction pairs generalizing label with
  | nil => cases present
  | cons first rest ih =>
    have distinct := List.nodup_cons.mp unique
    rcases List.mem_cons.mp present with firstHere | later
    · cases firstHere
      change bit (writes rest (write label query (bit value position)) value) query = _
      rw [writes_outside _ _ _ _ distinct.1,bit_write _ _ _ _ (bit_lt _ _),if_pos rfl]
    · exact ih _ distinct.2 later

theorem scatter_outside (label value query : Nat) (axes : List Nat) (outside : query ∉ axes) :
    bit (scatter label axes value) query = bit label query := by
  exact writes_outside axes.zipIdx label value query (by simpa only [List.zipIdx_map_fst] using outside)

theorem scatter_at (label value : Nat) (axes : List Nat) (unique : axes.Nodup)
    (index : Nat) (bound : index < axes.length) :
    bit (scatter label axes value) (axes[index]'bound) = bit value index := by
  have present : (axes[index]'bound,index) ∈ axes.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem bound)
  exact writes_at axes.zipIdx label value (axes[index]'bound) index
    (by simpa only [List.zipIdx_map_fst] using unique) present

private theorem bit_ext (left right : Nat) (same : ∀ query,bit left query = bit right query) : left = right := by
  apply Nat.eq_of_testBit_eq
  intro query
  have bits := same query
  rw [← Nat.toNat_testBit left query,← Nat.toNat_testBit right query] at bits
  cases left.testBit query <;> cases right.testBit query <;> simp_all

/-- A local overwrite and its literal selected-wire overwrite agree at every
physical bit. Reversed and noncontiguous axes require no special case. -/
theorem scatter_write (base value : Nat) (axes : List Nat) (unique : axes.Nodup)
    (index : Nat) (bound : index < axes.length) (replacement : Nat) (small : replacement < 2) :
    write (scatter base axes value) (axes[index]'bound) replacement =
      scatter base axes (write value index replacement) := by
  apply bit_ext
  intro query
  by_cases selected : query ∈ axes
  · obtain ⟨position,positionBound,same⟩ := List.getElem_of_mem selected
    subst query
    have identities : (axes[position]'positionBound) = (axes[index]'bound) ↔ position = index := by
      constructor
      · intro equal
        apply (List.getElem?_inj positionBound unique).mp
        simp only [List.getElem?_eq_getElem positionBound,List.getElem?_eq_getElem bound,equal]
      · intro equal
        subst position
        rfl
    rw [bit_write _ _ _ _ small,scatter_at base value axes unique position positionBound,
      scatter_at base (write value index replacement) axes unique position positionBound,bit_write _ _ _ _ small]
    simp only [identities]
  · have different : query ≠ axes[index]'bound := by
      intro same
      apply selected
      rw [same]
      exact List.getElem_mem bound
    rw [bit_write _ _ _ _ small,if_neg different,scatter_outside _ _ _ _ selected,
      scatter_outside _ _ _ _ selected]

def mappedAxes (selected targets : List Nat) : List Nat :=
  targets.map fun index => (selected[index]?).getD 0

private theorem scatter_writes (base value input : Nat) (selected : List Nat) (unique : selected.Nodup)
    (pairs : List (Nat × Nat)) (bounded : ∀ pair ∈ pairs,pair.1 < selected.length) :
    writes (pairs.map fun pair => ((selected[pair.1]?).getD 0,pair.2)) (scatter base selected value) input =
      scatter base selected (writes pairs value input) := by
  induction pairs generalizing value with
  | nil => rfl
  | cons first rest ih =>
    have firstBound := bounded first (List.mem_cons_self)
    have remaining : ∀ pair ∈ rest,pair.1 < selected.length :=
      fun pair member => bounded pair (List.mem_cons_of_mem _ member)
    simp only [List.map_cons,writes,List.foldl_cons,List.getElem?_eq_getElem firstBound,Option.getD_some]
    rw [scatter_write base value selected unique first.1 firstBound (bit input first.2) (bit_lt _ _)]
    exact ih _ remaining

theorem scatter_mapped (base value input : Nat) (selected : List Nat) (unique : selected.Nodup)
    (targets : List Nat) (bounded : ∀ index ∈ targets,index < selected.length) :
    scatter (scatter base selected value) (mappedAxes selected targets) input =
      scatter base selected (scatter value targets input) := by
  have fields : ∀ pair ∈ targets.zipIdx,pair.1 < selected.length := by
    intro pair member
    have present : pair.1 ∈ targets := by
      have mapped : pair.1 ∈ targets.zipIdx.map (·.1) := List.mem_map.mpr ⟨pair,member,rfl⟩
      simpa only [List.zipIdx_map_fst] using mapped
    exact bounded pair.1 present
  simpa only [scatter,mappedAxes,FiniteRestriction.zipIdx_map] using
    scatter_writes base value input selected unique targets.zipIdx fields

theorem gather_mapped (base value : Nat) (selected : List Nat) (unique : selected.Nodup)
    (targets : List Nat) (bounded : ∀ index ∈ targets,index < selected.length) :
    gather (scatter base selected value) (mappedAxes selected targets) = gather value targets := by
  unfold gather mappedAxes
  rw [FiniteRestriction.zipIdx_map,List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro pair member
  have present : pair.1 ∈ targets := by
    have mapped : pair.1 ∈ targets.zipIdx.map (·.1) := List.mem_map.mpr ⟨pair,member,rfl⟩
    simpa only [List.zipIdx_map_fst] using mapped
  have bound := bounded pair.1 present
  simp only [Function.comp_def,List.getElem?_eq_getElem bound,Option.getD_some]
  rw [scatter_at base value selected unique pair.1 bound]

end QleisliKernel.Qirf.RuntimeScatterTransport
