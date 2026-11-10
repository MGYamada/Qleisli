import QleisliKernel.Finite

/-! Budgeted sharing of already authenticated relevance rows. Source queries,
operation/provider occurrences and semantic obligations remain in their original
structures. This module compares exact owner/source strings and grants no row
relevance or acceptance merely because a row was supplied.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceRows
open Finite

abbrev Row := String × String

/-- Distinct module names decide row inequality before either source body is
compared. Repeated names still require an exact byte-for-byte source match. -/
def equal (row head : Row) : WorkM Bool := do
  exactWork (Exact.charge (8 * (row.1.utf8ByteSize + head.1.utf8ByteSize + 1)))
  if row.1 == head.1 then
    exactWork (Exact.charge (8 * (row.2.utf8ByteSize + head.2.utf8ByteSize + 1)))
    return row.2 == head.2
  return false

theorem equal_value (row head : Row) (before after : Nat) (answer : Bool)
    (ran : (equal row head).run before = (.ok answer,after)) : answer = (row == head) := by
  obtain ⟨_,paid,_,rest⟩ := bind_success _ _ before after answer ran
  change answer = ((row.1 == head.1) && (row.2 == head.2))
  by_cases same : (row.1 == head.1) = true
  · simp only [same,if_true,Bool.true_and] at rest ⊢
    obtain ⟨_,middle,_,returned⟩ := bind_success _ _ paid after answer rest
    exact (pure_success _ _ _ _ returned).1
  · simp only [same] at rest
    have no : (row.1 == head.1) = false := Bool.eq_false_iff.mpr same
    rw [no,Bool.false_and]
    exact (pure_success false _ _ _ rest).1

def contains (row : Row) (seen : List Row) : WorkM Bool :=
  seen.anyM (equal row)

theorem contains_value (row : Row) (seen : List Row) (before after : Nat) (answer : Bool)
    (ran : (contains row seen).run before = (.ok answer,after)) : answer = seen.any (row == ·) := by
  induction seen generalizing before with
  | nil => exact (pure_success false answer before after ran).1
  | cons head tail ih =>
    obtain ⟨found,middle,test,rest⟩ := bind_success _ _ before after answer ran
    have equal := equal_value row head before middle found test
    cases found with
    | true => simpa [List.any_cons,← equal] using (pure_success true answer middle after rest).1
    | false => simpa [List.any_cons,← equal] using ih middle rest

private def add (seen : List Row) (row : Row) : WorkM (List Row) := do
  -- The list retains references to immutable strings. Reserving one row and
  -- reversing its output cell do not scan or copy the source bytes.
  exactWork (Exact.charge 8)
  let found ← contains row seen
  return if found then seen else row :: seen

private theorem collect_value (raw seen output : List Row) (before after : Nat)
    (ran : (raw.foldlM add seen).run before = (.ok output,after)) :
    output.reverse = List.eraseDupsBy.loop (· == ·) raw seen := by
  induction raw generalizing seen before with
  | nil =>
    have equal := (pure_success seen output before after ran).1
    rw [equal]
    rfl
  | cons row rest ih =>
    obtain ⟨next,middle,step,tail⟩ := bind_success _ _ before after output ran
    obtain ⟨_,paid,_,test⟩ := bind_success _ _ before middle next step
    obtain ⟨found,last,comparison,returned⟩ := bind_success _ _ paid middle next test
    have occurrence := contains_value row seen paid last found comparison
    have nextIs := (pure_success (if found then seen else row :: seen) next last middle returned).1
    subst next
    cases found <;> simpa only [List.eraseDupsBy.loop,← occurrence] using ih _ middle tail

/-- Keep the first occurrence of each exact owner/source pair, charging for
visited rows and the byte comparisons actually made by this invocation. -/
def retain (raw : List Row) : WorkM (List Row) := do
  let seen ← raw.foldlM add []
  return seen.reverse

theorem retain_value (raw rows : List Row) (before after : Nat)
    (ran : (retain raw).run before = (.ok rows,after)) : rows = raw.eraseDups := by
  obtain ⟨seen,middle,folded,returned⟩ := bind_success _ _ before after rows ran
  exact (pure_success seen.reverse rows middle after returned).1.trans
    (collect_value raw [] seen before middle folded)

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
