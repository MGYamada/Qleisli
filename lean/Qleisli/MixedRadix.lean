import Qleisli.ExactMatrix

/-! Finite mixed-radix coordinates in an explicit identity order. Cardinality
is independent of physical width; dimension-one entries keep their positions.
These total natural-number functions and proofs grant no source, arithmetic
availability, owner permutation or acceptance authority.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.MixedRadix

def volume {α : Type} (order : List α) (cards : α → Nat) : Nat := (order.map cards).prod

def encode {α : Type} (order : List α) (cards digits : α → Nat) : Nat :=
  order.foldr (fun entry tail => digits entry+cards entry*tail) 0

def decode {α : Type} [DecidableEq α] : List α → (α → Nat) → Nat → α → Nat
  | [],_,_,_ => 0
  | entry::rest,cards,logical,wanted =>
    if entry = wanted then logical % cards entry else decode rest cards (logical / cards entry) wanted

def recode {α : Type} [DecidableEq α] (original grouped : List α) (cards : α → Nat) (logical : Nat) : Nat :=
  encode grouped cards (decode original cards logical)

theorem volume_perm {α : Type} (first second : List α) (cards : α → Nat) (perm : first.Perm second) :
    volume first cards = volume second cards := (perm.map cards).prod_eq

theorem encode_congr {α : Type} (order : List α) (cards first second : α → Nat) :
    (∀ entry ∈ order,first entry = second entry) → encode order cards first = encode order cards second := by
  induction order with
  | nil => intro _same; rfl
  | cons entry rest ih =>
    intro same
    change first entry+cards entry*encode rest cards first = second entry+cards entry*encode rest cards second
    rw [same entry (List.mem_cons_self),ih (fun value member => same value (List.mem_cons_of_mem _ member))]

theorem encode_bound {α : Type} (order : List α) (cards digits : α → Nat) :
    (∀ entry ∈ order,digits entry < cards entry) → encode order cards digits < volume order cards := by
  induction order with
  | nil => intro _bounds; exact Nat.zero_lt_one
  | cons entry rest ih =>
    intro bounds
    have tail := ih (fun value member => bounds value (List.mem_cons_of_mem _ member))
    change digits entry+cards entry*encode rest cards digits < cards entry*volume rest cards
    calc
      digits entry+cards entry*encode rest cards digits < cards entry+cards entry*encode rest cards digits :=
        Nat.add_lt_add_right (bounds entry (List.mem_cons_self)) _
      _ = cards entry*(encode rest cards digits+1) := by ring
      _ ≤ cards entry*volume rest cards := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt tail)

theorem decode_head {α : Type} [DecidableEq α] (entry : α) (rest : List α) (cards : α → Nat) (logical : Nat) :
    decode (entry::rest) cards logical entry = logical % cards entry := by
  rw [decode,if_pos rfl]

theorem decode_bound {α : Type} [DecidableEq α] (order : List α) (cards : α → Nat) :
    ∀ logical, (∀ entry ∈ order,0 < cards entry) → logical < volume order cards →
      ∀ entry ∈ order,decode order cards logical entry < cards entry := by
  induction order with
  | nil => intro logical _positive _bound entry member; cases member
  | cons head rest ih =>
    intro logical positive bound entry member
    by_cases same : head = entry
    · subst entry
      rw [decode_head]
      exact Nat.mod_lt _ (positive head (List.mem_cons_self))
    · have later : entry ∈ rest := by
        rcases List.mem_cons.mp member with equal | later
        · exact False.elim (same equal.symm)
        · exact later
      have tailBound : logical / cards head < volume rest cards := Nat.div_lt_of_lt_mul bound
      rw [decode,if_neg same]
      exact ih _ (fun value present => positive value (List.mem_cons_of_mem _ present)) tailBound entry later

private theorem radix_mod (low high card : Nat) (bound : low < card) :
    (low+card*high) % card = low := by
  simp only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt bound]

private theorem radix_div (low high card : Nat) (bound : low < card) :
    (low+card*high) / card = high := by
  rw [Nat.add_mul_div_left _ _ (Nat.lt_of_le_of_lt (Nat.zero_le low) bound),Nat.div_eq_of_lt bound,Nat.zero_add]

theorem decode_encode {α : Type} [DecidableEq α] (order : List α) (cards digits : α → Nat) :
    (∀ entry ∈ order,digits entry < cards entry) →
      ∀ wanted ∈ order,decode order cards (encode order cards digits) wanted = digits wanted := by
  induction order with
  | nil => intro _bounds wanted member; cases member
  | cons head rest ih =>
    intro bounds wanted member
    change (if head = wanted then (digits head+cards head*encode rest cards digits) % cards head else
      decode rest cards ((digits head+cards head*encode rest cards digits) / cards head) wanted) = digits wanted
    by_cases same : head = wanted
    · rw [if_pos same,radix_mod _ _ _ (bounds head (List.mem_cons_self))]
      exact congrArg digits same
    · have later : wanted ∈ rest := by
        rcases List.mem_cons.mp member with equal | later
        · exact False.elim (same equal.symm)
        · exact later
      rw [if_neg same,radix_div _ _ _ (bounds head (List.mem_cons_self))]
      exact ih (fun entry present => bounds entry (List.mem_cons_of_mem _ present)) wanted later

theorem encode_decode {α : Type} [DecidableEq α] (order : List α) (cards : α → Nat) :
    ∀ logical, order.Nodup → (∀ entry ∈ order,0 < cards entry) → logical < volume order cards →
      encode order cards (decode order cards logical) = logical := by
  induction order with
  | nil =>
    intro logical _unique _positive bound
    change logical < 1 at bound
    have zero : logical = 0 := by omega
    subst logical
    rfl
  | cons head rest ih =>
    intro logical unique positive bound
    have separate := List.nodup_cons.mp unique
    have tailBound : logical / cards head < volume rest cards := Nat.div_lt_of_lt_mul bound
    have tailEqual : encode rest cards (decode (head::rest) cards logical) =
        encode rest cards (decode rest cards (logical / cards head)) := by
      apply encode_congr
      intro entry member
      have different : head ≠ entry := by
        intro equal
        exact separate.1 (equal.symm ▸ member)
      rw [decode,if_neg different]
    change decode (head::rest) cards logical head+cards head*encode rest cards (decode (head::rest) cards logical) = logical
    rw [decode_head,tailEqual,ih _ separate.2
      (fun entry member => positive entry (List.mem_cons_of_mem _ member)) tailBound]
    exact Nat.mod_add_div _ _

theorem recode_bound {α : Type} [DecidableEq α] (original grouped : List α) (cards : α → Nat)
    (perm : original.Perm grouped) (positive : ∀ entry ∈ original,0 < cards entry)
    (logical : Nat) (bound : logical < volume original cards) :
    recode original grouped cards logical < volume grouped cards := by
  apply encode_bound
  intro entry member
  exact decode_bound original cards logical positive bound entry (perm.mem_iff.mpr member)

/-- Both directions preserve the exact dense logical domain; this is not a
physical-bit permutation and it does not require power-of-two cardinalities. -/
theorem recode_inverse {α : Type} [DecidableEq α] (original grouped : List α) (cards : α → Nat)
    (perm : original.Perm grouped) (unique : original.Nodup)
    (positive : ∀ entry ∈ original,0 < cards entry) (logical : Nat) (bound : logical < volume original cards) :
    recode grouped original cards (recode original grouped cards logical) = logical := by
  have digits : ∀ entry ∈ grouped,decode original cards logical entry < cards entry :=
    fun entry member => decode_bound original cards logical positive bound entry (perm.mem_iff.mpr member)
  change encode original cards (decode grouped cards (encode grouped cards (decode original cards logical))) = logical
  calc
    _ = encode original cards (decode original cards logical) := by
      apply encode_congr
      intro entry member
      exact decode_encode grouped cards (decode original cards logical) digits entry (perm.mem_iff.mp member)
    _ = logical := encode_decode original cards logical unique positive bound

#print axioms encode_decode
#print axioms recode_inverse

end Qleisli.MixedRadix
