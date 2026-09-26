import Qleisli.Transition
import Mathlib.Data.List.Nodup

namespace Qleisli

/-- Total renamings are an abstract specification of complete phi coverage.
Injectivity is stronger than the Rust check over a finite live set. We do not
yet prove that every accepted Rust phi extends to these functions. -/
structure Renaming where
  slot : Nat → Nat
  token : Nat → Nat
  wire : Nat → Nat
  slot_injective : Function.Injective slot
  token_injective : Function.Injective token
  wire_injective : Function.Injective wire

def Renaming.port (ρ : Renaming) (p : Port) : Port := ⟨ρ.slot p.slot, p.basis⟩

def Renaming.register (ρ : Renaming) (r : Register) : Register :=
  ⟨ρ.port r.port, ρ.token r.token, r.wires.map ρ.wire⟩

def Renaming.value (ρ : Renaming) : Value → Value
  | .unit => .unit
  | .classical c => .classical c
  | .quantum p => .quantum (ρ.port p)
  | .pair a b => .pair (ρ.value a) (ρ.value b)

def Renaming.config (ρ : Renaming) (c : Config) : Config :=
  ⟨c.holders.map ρ.value, c.store.map ρ.register⟩

@[simp] theorem Renaming.own_value (ρ : Renaming) (v : Value) :
    (ρ.value v).own = v.own.map ρ.port := by
  induction v with
  | unit => rfl
  | classical => rfl
  | quantum => rfl
  | pair a b ha hb => simp [value, Value.own, ha, hb]

@[simp] theorem Renaming.own_holders (ρ : Renaming) (vs : List Value) :
    own (vs.map ρ.value) = (own vs).map ρ.port := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [ih]

theorem Renaming.store_valid (ρ : Renaming) {s : Store} (h : s.Valid) :
    Store.Valid (s.map ρ.register) where
  slots_unique := by
    simpa [slots, register, port, List.map_map] using
      List.Nodup.map ρ.slot_injective h.slots_unique
  tokens_unique := by
    simpa [tokens, register, List.map_map] using
      List.Nodup.map ρ.token_injective h.tokens_unique
  wires_unique := by
    simpa [wires, register, List.flatMap_map, List.map_flatMap] using
      List.Nodup.map ρ.wire_injective h.wires_unique
  widths r hr := by
    obtain ⟨input, member, rfl⟩ := List.mem_map.mp hr
    simpa [register, port] using h.widths input member

theorem Renaming.preserves (ρ : Renaming) {c : Config} (h : c.Valid) :
    (ρ.config c).Valid where
  coverage := by
    simpa [config, ports, register, List.map_map] using h.coverage.map ρ.port
  store_valid := ρ.store_valid h.store_valid

/-- Every output ownership occurrence has an input occurrence, even at width 0. -/
theorem Renaming.slot_coverage (ρ : Renaming) (s : Store) (out : Nat) :
    out ∈ slots (s.map ρ.register) ↔ ∃ input ∈ slots s, ρ.slot input = out := by
  have eq : slots (s.map ρ.register) = (slots s).map ρ.slot := by
    simp [slots, register, port, List.map_map]
  rw [eq, List.mem_map]

theorem Renaming.slot_count (ρ : Renaming) (s : Store) :
    (slots (s.map ρ.register)).length = (slots s).length := by
  simp [slots]

/-- A caller or pending frame may change tokens and wires while keeping its
logical slot identities and exact basis trees. -/
theorem Renaming.frame_ports (ρ : Renaming) (frame : Store)
    (fixed : ∀ r ∈ frame, ρ.slot r.port.slot = r.port.slot) :
    ports (frame.map ρ.register) = ports frame := by
  simp only [ports, List.map_map]
  apply List.map_congr_left
  intro r hr
  simp [register, port, fixed r hr]

/-- Resource-only phi agreement. Each entire arm (result plus frame) is renamed
to the common output. Classical SSA scopes and result syntax are separate
source obligations, so agreement here uses typed ownership occurrences. -/
structure BranchPhi (left right out : Config) where
  leftNames : Renaming
  rightNames : Renaming
  left_store : out.store.Perm (left.store.map leftNames.register)
  right_store : out.store.Perm (right.store.map rightNames.register)
  left_holders : (own out.holders).Perm (own left.holders |>.map leftNames.port)
  right_holders : (own out.holders).Perm (own right.holders |>.map rightNames.port)

theorem BranchPhi.left_preserves {l r out : Config} (phi : BranchPhi l r out)
    (h : l.Valid) : out.Valid where
  coverage := by
    have renamed : (own l.holders |>.map phi.leftNames.port).Perm
        (ports (l.store.map phi.leftNames.register)) := by
      simpa [ports, Renaming.register, List.map_map] using h.coverage.map phi.leftNames.port
    exact (phi.left_holders.trans renamed).trans (phi.left_store.symm.map Register.port)
  store_valid := (phi.leftNames.store_valid h.store_valid).perm phi.left_store.symm

theorem BranchPhi.right_preserves {l r out : Config} (phi : BranchPhi l r out)
    (h : r.Valid) : out.Valid where
  coverage := by
    have renamed : (own r.holders |>.map phi.rightNames.port).Perm
        (ports (r.store.map phi.rightNames.register)) := by
      simpa [ports, Renaming.register, List.map_map] using h.coverage.map phi.rightNames.port
    exact (phi.right_holders.trans renamed).trans (phi.right_store.symm.map Register.port)
  store_valid := (phi.rightNames.store_valid h.store_valid).perm phi.right_store.symm

/-- Either runtime arm reaches a valid common ownership boundary. -/
theorem BranchPhi.preserves {l r out : Config} (phi : BranchPhi l r out)
    (hl : l.Valid) (hr : r.Valid) (choice : Bool) :
    out.Valid ∧ (if choice then l else r).Valid := by
  cases choice
  · exact ⟨phi.right_preserves hr, hr⟩
  · exact ⟨phi.left_preserves hl, hl⟩

/-- Both arms must be checked from the same entry configuration. -/
inductive CheckedRun : Config → Config → Prop where
  | linear {a b : Config} (run : ResourceRun a b) : CheckedRun a b
  | seq {a b c : Config} (first : CheckedRun a b) (next : CheckedRun b c) : CheckedRun a c
  | branch {entry left right out : Config}
      (thenRun : CheckedRun entry left) (elseRun : CheckedRun entry right)
      (merge : BranchPhi left right out) : CheckedRun entry out

theorem CheckedRun.preserves {a b : Config} (run : CheckedRun a b)
    (h : a.Valid) : b.Valid := by
  induction run with
  | linear run => exact run.preserves h
  | seq _ _ ih₁ ih₂ => exact ih₂ (ih₁ h)
  | branch _ _ merge ih₁ ih₂ => exact (merge.preserves (ih₁ h) (ih₂ h) true).1

end Qleisli
