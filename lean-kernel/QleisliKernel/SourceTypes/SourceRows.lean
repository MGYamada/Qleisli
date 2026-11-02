import QleisliKernel.Finite

/-! Budgeted sharing of already authenticated relevance rows. Source queries,
operation/provider occurrences and semantic obligations remain in their original
structures. This module compares exact owner/source strings and grants no row
relevance or acceptance merely because a row was supplied.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceRows
open Finite

abbrev Row := String × String

/-- The existing byte-sensitive reservation precedes exact row deduplication. -/
def retain (rows : List Row) : WorkM (List Row) := do
  if rows.isEmpty then return []
  let fields := (rows.map fun (owner,source) => owner.utf8ByteSize+source.utf8ByteSize+1).sum
  exactWork (Exact.charge (8*(rows.length+1)*(fields+1)))
  return rows.eraseDups

theorem retain_value (raw rows : List Row) (before after : Nat)
    (ran : (retain raw).run before = (.ok rows,after)) : rows = raw.eraseDups := by
  cases raw with
  | nil => exact (pure_success [] rows before after ran).1
  | cons row rest =>
    obtain ⟨_,middle,_,tailRun⟩ := bind_success _ _ before after rows ran
    obtain ⟨_,afterCharge,_,returned⟩ := bind_success _ _ middle after rows tailRun
    exact (pure_success ((row :: rest).eraseDups) rows afterCharge after returned).1

structure Retained (raw : List Row) where
  rows : List Row
  original : ∃ before after,(retain raw).run before = (.ok rows,after)
  canonical : rows = raw.eraseDups
  members : ∀ row,row ∈ rows ↔ row ∈ raw

/-- Record the result of this invocation, without a second row comparison or
an invented execution of any source query. Raw rows remain the exact index. -/
def read (raw : List Row) : WorkM (Retained raw) := fun before =>
  match ran : (retain raw).run before with
  | (.error error,after) => (.error error,after)
  | (.ok rows,after) =>
    let canonical := retain_value raw rows before after ran
    (.ok ⟨rows,⟨before,after,ran⟩,canonical,by
      intro row
      rw [canonical]
      exact List.mem_eraseDups⟩,after)

end QleisliKernel.SourceTypes.SourceRows
