import Qleisli.RuntimeSparseBlockEncoding
import QleisliKernel.Qirf.RuntimeBasisAction

/-! The literal basis operation and the original source table move the same
joint amplitudes. The equality is on physical labels and applies to arbitrary
reference columns and untouched axes.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeBasisSourceAction
open QleisliKernel QleisliKernel.Qirf
open RuntimeBasisAction (Layout rowsMatch matched_entry)
open Semantics.Finite (gather)

/-- A coefficient of the canonical carrier code, without a dense matrix. -/
noncomputable def encodeDigit (layout : Layout) (joint : Nat → ℂ) (physical : Nat) : ℂ :=
  ((List.range layout.labels.length).map fun digit =>
    if layout.labels[digit]? = some physical then joint digit else 0).sum

noncomputable def logicalRow (row : List Nat) (joint : Nat → ℂ) (output : Nat) : ℂ :=
  ((List.range row.length).map fun digit => if row[digit]? = some output then joint digit else 0).sum

/-- The physical table and the original logical table agree on every
encoded column. This is a rectangular code equation on one spectator fibre. -/
theorem encode_row {input output rows table} (checked : rowsMatch input output rows table = true)
    {row : List Nat} (member : row ∈ rows)
    (bounded : ∀ label ∈ input.labels, label < 2^input.bits)
    (joint : Nat → ℂ) (physical : Nat) :
    ((List.range (2^input.bits)).map fun code =>
      if table[code]?.getD 0 = physical then encodeDigit input joint code else 0).sum =
      encodeDigit output (logicalRow row joint) physical := by
  have all := (Bool.and_eq_true_iff.mp checked).2
  have length : row.length = input.labels.length :=
    beq_iff_eq.mp (Bool.and_eq_true_iff.mp (List.all_eq_true.mp all row member)).1
  let term (column : Nat) : ℂ :=
    if (row[column]?.bind fun target => output.labels[target]?) = some physical then joint column else 0
  have original (column : Nat) (inside : column < input.labels.length) :
      ∃ code ordinal target, input.labels[column]? = some code ∧ row[column]? = some ordinal ∧
        output.labels[ordinal]? = some target ∧ table[code]? = some target := by
    have rowBound : column < row.length := length.symm ▸ inside
    have first := List.getElem?_eq_getElem inside
    have second := List.getElem?_eq_getElem rowBound
    obtain ⟨target,outCode,native⟩ := matched_entry checked member first second
    exact ⟨input.labels[column],row[column],target,first,second,outCode,native⟩
  have left :
      ((List.range (2^input.bits)).map fun code =>
        if table[code]?.getD 0 = physical then encodeDigit input joint code else 0).sum =
        ((List.range input.labels.length).map term).sum := by
    let entries := fun code column =>
      if input.labels[column]? = some code ∧ table[code]?.getD 0 = physical then joint column else 0
    calc
      _ = ((List.range (2^input.bits)).map fun code =>
          ((List.range input.labels.length).map (entries code)).sum).sum := by
        apply Qleisli.Exact.sum_map_congr
        intro code _
        by_cases target : table[code]?.getD 0 = physical
        · simp only [target,if_true,encodeDigit,entries,and_true]
        · simp [target,entries]
      _ = ((List.range input.labels.length).map fun column =>
          ((List.range (2^input.bits)).map fun code => entries code column).sum).sum :=
        Qleisli.Exact.sum_swap _ _ entries
      _ = _ := by
        apply Qleisli.Exact.sum_map_congr
        intro column inside
        obtain ⟨code,ordinal,target,inputRead,rowRead,outputRead,native⟩ := original column (List.mem_range.mp inside)
        have validCode := bounded code (List.mem_of_getElem? inputRead)
        unfold term
        rw [rowRead]
        change ((List.range (2^input.bits)).map fun index => entries index column).sum =
          (if output.labels[ordinal]? = some physical then joint column else 0)
        rw [outputRead]
        simp only [Option.some.injEq]
        calc
          _ = ((List.range (2^input.bits)).map fun index =>
              if code = index then (if target = physical then joint column else 0) else 0).sum := by
            apply Qleisli.Exact.sum_map_congr
            intro index _
            by_cases same : code = index
            · subst index
              simp [entries,inputRead,native]
            · simp [entries,inputRead,same]
          _ = _ := Qleisli.Exact.range_delta_sum _ _ _ validCode
  rw [left]
  symm
  let entries := fun digit column =>
    if output.labels[digit]? = some physical ∧ row[column]? = some digit then joint column else 0
  calc
    _ = ((List.range output.labels.length).map fun digit =>
        ((List.range row.length).map (entries digit)).sum).sum := by
      unfold encodeDigit
      apply Qleisli.Exact.sum_map_congr
      intro digit _
      by_cases selected : output.labels[digit]? = some physical
      · simp [selected,logicalRow,entries]
      · simp [selected,entries]
    _ = ((List.range row.length).map fun column =>
        ((List.range output.labels.length).map fun digit => entries digit column).sum).sum :=
      Qleisli.Exact.sum_swap _ _ entries
    _ = _ := by
      rw [length]
      apply Qleisli.Exact.sum_map_congr
      intro column inside
      obtain ⟨code,ordinal,target,inputRead,rowRead,outputRead,native⟩ := original column (List.mem_range.mp inside)
      have ordinalBound : ordinal < output.labels.length := (List.getElem?_eq_some_iff.mp outputRead).1
      unfold term
      rw [rowRead]
      change ((List.range output.labels.length).map fun digit => entries digit column).sum =
        (if output.labels[ordinal]? = some physical then joint column else 0)
      rw [outputRead]
      simp only [Option.some.injEq]
      calc
        _ = ((List.range output.labels.length).map fun digit =>
            if ordinal = digit then (if target = physical then joint column else 0) else 0).sum := by
          apply Qleisli.Exact.sum_map_congr
          intro digit _
          by_cases same : ordinal = digit
          · subst digit
            simp [entries,rowRead,outputRead]
          · simp [entries,rowRead,same]
        _ = _ := Qleisli.Exact.range_delta_sum _ _ _ ordinalBound

open RuntimeOwnerMap (Binding)
open RuntimeSemanticForest (Frame ownerLayout product)
open RuntimeSparseBlockEncoding (coefficient)
open RuntimeNamedHeadCoefficients (fibre)
open RuntimeForestCode (forestAxes sparseEntry)
open Qleisli.Semantics.Exact (scalar)

noncomputable def applyRow {Reference : Type} (row : List Nat) (outputs : Nat)
    (joint : Nat → Reference → ℂ) (logical : Nat) (reference : Reference) : ℂ :=
  logicalRow row (fun input => joint (input+row.length*(logical/outputs)) reference)
    (logical%outputs)

/-- Application of an original logical row keeps each spectator coefficient. -/
theorem fibre_applyRow {Reference : Type} (row : List Nat) (outputs spectators : Nat)
    (weight : Nat → ℂ) (joint : Nat → Reference → ℂ) (digit : Nat) (reference : Reference)
    (bound : digit < outputs) :
    fibre outputs spectators weight (applyRow row outputs joint) digit reference =
      logicalRow row (fun input => fibre row.length spectators weight joint input reference) digit := by
  have positive : 0 < outputs := Nat.lt_of_le_of_lt (Nat.zero_le digit) bound
  have remainder (high : Nat) : (digit+outputs*high)%outputs = digit := by
    simp only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt bound]
  have quotient (high : Nat) : (digit+outputs*high)/outputs = high := by
    rw [Nat.add_mul_div_left _ _ positive,Nat.div_eq_of_lt bound,Nat.zero_add]
  unfold fibre applyRow logicalRow
  simp only [remainder,quotient]
  let term := fun high input => if row[input]? = some digit then
    weight high * joint (input+row.length*high) reference else 0
  calc
    _ = ((List.range spectators).map fun high => ((List.range row.length).map (term high)).sum).sum := by
      apply Qleisli.Exact.sum_map_congr
      intro high _
      rw [← List.sum_map_mul_left]
      apply Qleisli.Exact.sum_map_congr
      intro input _
      by_cases selected : row[input]? = some digit <;> simp [term,selected]
    _ = ((List.range row.length).map fun input => ((List.range spectators).map fun high => term high input).sum).sum :=
      Qleisli.Exact.sum_swap _ _ term
    _ = _ := by
      apply Qleisli.Exact.sum_map_congr
      intro input _
      by_cases selected : row[input]? = some digit <;> simp [term,selected]

/-- Encode a single original owner against the exact spectator coefficients. -/
theorem encoded_block {owner : Binding} {spectators} (frame : Frame (owner :: spectators))
    (physicalFrame : List Nat) {Reference : Type} (joint : Nat → Reference → ℂ)
    (physical : Nat) (reference : Reference) :
    RuntimeSemanticForest.action frame physicalFrame joint physical reference =
      encodeDigit (ownerLayout owner)
        (fun digit => fibre (ownerLayout owner).labels.length (product spectators).labels.length
          (coefficient spectators physicalFrame physical) joint digit reference)
        (gather physical (owner.port.wires.map physicalFrame.idxOf)) := by
  have single : product [owner] = ownerLayout owner :=
    RuntimeForestOrderedProduct.tensor_right _
  have axes : forestAxes physicalFrame [owner] = owner.port.wires.map physicalFrame.idxOf := by
    simp [forestAxes]
  let partitioned : Frame ([owner] ++ spectators) := frame
  refine (RuntimeSparseBlockEncoding.block_action partitioned physicalFrame joint physical reference).trans ?_
  unfold encodeDigit coefficient
  rw [single,axes]
  apply Qleisli.Exact.sum_map_congr
  intro digit _
  unfold sparseEntry
  change scalar (if (ownerLayout owner).labels[digit]? == some _ then _ else _) * _ = _
  by_cases hit : (ownerLayout owner).labels[digit]? =
      some (gather physical (owner.port.wires.map physicalFrame.idxOf))
  · simp [hit,Qleisli.Exact.scalar_one_meaning]
  · simp [hit,Qleisli.Exact.scalar_zero_meaning]

#print axioms encode_row
#print axioms fibre_applyRow
#print axioms encoded_block

end Qleisli.RuntimeBasisSourceAction
