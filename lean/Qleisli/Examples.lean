import Qleisli.Phi

/-! Exact kernel-checked boundary examples. No floating-point simulation. -/

namespace Qleisli.Examples

def u : Register := ⟨⟨0, .unit⟩, 0, []⟩
def q : Register := ⟨⟨1, .bit⟩, 1, [0]⟩

def mixed : Config :=
  ⟨[.pair (.classical 7) (.quantum u.port), .quantum q.port], [u, q]⟩

theorem mixed_valid : mixed.Valid := by
  constructor
  · decide
  · constructor <;> decide

theorem zero_width_is_owned :
    (wires [u]).length = 0 ∧ (own [.quantum u.port]).length = 1 := by decide

theorem duplicate_zero_width_rejected (slot token : Nat) :
    ¬ (Config.mk [.quantum ⟨slot, .unit⟩, .quantum ⟨slot, .unit⟩]
        [⟨⟨slot, .unit⟩, token, []⟩]).Valid := by
  intro h
  have unique := h.unique_holders
  simp [own, Value.own] at unique

theorem implicit_zero_width_drop_rejected (slot token : Nat) :
    ¬ (Config.mk [] [⟨⟨slot, .unit⟩, token, []⟩]).Valid := by
  intro h
  have empty := closed_classical_no_resources h rfl
  contradiction

theorem shared_token_rejected :
    ¬ Store.Valid [u, { q with token := 0 }] := by
  intro h
  have unique := h.tokens_unique
  simp [tokens, u, q] at unique

theorem wire_alias_rejected :
    ¬ Store.Valid [q, ⟨⟨2, .bit⟩, 2, [0]⟩] := by
  intro h
  have unique := h.wires_unique
  simp [wires, q] at unique

theorem wrong_width_rejected :
    ¬ Store.Valid [⟨⟨0, .unit⟩, 0, [0]⟩] := by
  intro h
  have width := h.widths ⟨⟨0, .unit⟩, 0, [0]⟩ (by simp)
  contradiction

theorem wrong_basis_rejected :
    ¬ (Config.mk [.quantum ⟨0, .bit⟩] [u]).Valid := by
  intro h
  have coverage := h.coverage
  have unequal : ¬ (own [.quantum ⟨0, .bit⟩]).Perm (ports [u]) := by decide
  exact unequal coverage

theorem split_unit_bit : Store.Valid
    [⟨⟨0, .unit⟩, 1, []⟩, ⟨⟨1, .bit⟩, 2, [0]⟩] := by
  apply (Action.split 4 0 0 1 1 2 .unit .bit [] [0]
    (by decide) (by decide) rfl rfl).preserves
  constructor <;> decide

def afterDiscard : Config := ⟨[.quantum q.port], [q]⟩

/-- Explicit discard ends the zero-width ownership; the bit frame is retained. -/
def discardUnit : Replacement mixed afterDiscard where
  consumed := [u]
  produced := []
  frame := [q]
  result := []
  suspended := [.quantum q.port]
  partition := by decide
  step := .discard u
  separate := ⟨by simp [slots], by simp [tokens], by simp [wires]⟩
  result_coverage := by decide
  frame_coverage := by decide
  output_holders := rfl
  output_store := rfl

theorem explicit_zero_width_discard_valid : afterDiscard.Valid :=
  discardUnit.preserves mixed_valid

theorem pending_mixed_pair_valid : (Config.mk
    [.pair (.pair (.classical 7) (.quantum u.port)) (.quantum q.port)] [u, q]).Valid :=
  pair_preserves mixed_valid

def shift (dt dw : Nat) : Renaming where
  slot := id
  token := (· + dt)
  wire := (· + dw)
  slot_injective := fun _ _ h => h
  token_injective := fun _ _ h => Nat.add_right_cancel h
  wire_injective := fun _ _ h => Nat.add_right_cancel h

def otherArm : Config :=
  ⟨[.pair (.classical 8) (.quantum u.port), .quantum q.port],
    [{ u with token := 2 }, { q with token := 3 }]⟩

def merged : Config :=
  ⟨[.pair (.classical 9) (.quantum u.port), .quantum q.port],
    [{ u with token := 4 }, { q with token := 5, wires := [2] }]⟩

def zeroWidthPhi : BranchPhi mixed otherArm merged where
  leftNames := shift 4 2
  rightNames := shift 2 2
  left_store := .refl _
  right_store := .refl _
  left_holders := by decide
  right_holders := by decide

theorem zero_width_result_and_bit_frame_phi (choice : Bool) :
    merged.Valid ∧ (if choice then mixed else otherArm).Valid := by
  apply zeroWidthPhi.preserves mixed_valid
  constructor
  · decide
  · constructor <;> decide

theorem phi_cannot_omit_zero_width_result :
    ¬ (Config.mk [.quantum q.port] merged.store).Valid := by
  intro h
  have length := h.coverage.length_eq
  contradiction

end Qleisli.Examples
