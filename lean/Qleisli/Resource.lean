import Mathlib.Data.List.Perm.Basic

/-!
# The ownership-accounting projection of finite core v0

This model does not encode quantum states or assert their factorization.
It is a projection of the paper resource rules, not the complete source calculus.
-/

namespace Qleisli

inductive Basis where
  | unit
  | bit
  | pair (left right : Basis)
  deriving DecidableEq, Repr

def Basis.width : Basis → Nat
  | .unit => 0
  | .bit => 1
  | .pair a b => a.width + b.width

/-- A typed ownership occurrence. Even a zero-width basis owns one slot. -/
structure Port where
  slot : Nat
  basis : Basis
  deriving DecidableEq, Repr

inductive Value where
  | unit
  | classical (id : Nat)
  | quantum (port : Port)
  | pair (left right : Value)
  deriving DecidableEq, Repr

def Value.own : Value → List Port
  | .unit | .classical _ => []
  | .quantum p => [p]
  | .pair a b => a.own ++ b.own

def own (values : List Value) : List Port := values.flatMap Value.own

structure Register where
  port : Port
  token : Nat
  wires : List Nat
  deriving DecidableEq, Repr

abbrev Store := List Register

def ports (store : Store) : List Port := store.map Register.port
def slots (store : Store) : List Nat := store.map (fun r => r.port.slot)
def tokens (store : Store) : List Nat := store.map Register.token
def wires (store : Store) : List Nat := store.flatMap Register.wires

structure Store.Valid (store : Store) : Prop where
  slots_unique : (slots store).Nodup
  tokens_unique : (tokens store).Nodup
  wires_unique : (wires store).Nodup
  widths : ∀ r ∈ store, r.wires.length = r.port.basis.width

/-- All holders, including suspended frames, count toward coverage. -/
structure Config where
  holders : List Value
  store : Store

structure Config.Valid (config : Config) : Prop where
  coverage : (own config.holders).Perm (ports config.store)
  store_valid : config.store.Valid

@[simp] theorem own_nil : own [] = [] := rfl
@[simp] theorem own_cons (v : Value) (vs : List Value) :
    own (v :: vs) = v.own ++ own vs := rfl
@[simp] theorem own_append (vs ws : List Value) :
    own (vs ++ ws) = own vs ++ own ws := List.flatMap_append

theorem Store.Valid.perm {s t : Store} (h : s.Perm t) (hs : s.Valid) : t.Valid where
  slots_unique := (h.map _).nodup hs.slots_unique
  tokens_unique := (h.map _).nodup hs.tokens_unique
  wires_unique := (h.flatMap_right _).nodup hs.wires_unique
  widths r hr := hs.widths r (h.mem_iff.mpr hr)

/-- The untouched frame inherits every physical register invariant. -/
theorem Store.Valid.right {s f : Store} (h : (s ++ f).Valid) : f.Valid where
  slots_unique := (List.nodup_append.mp (by
    simpa [slots] using h.slots_unique)).2.1
  tokens_unique := (List.nodup_append.mp (by
    simpa [tokens] using h.tokens_unique)).2.1
  wires_unique := (List.nodup_append.mp (by
    simpa [wires] using h.wires_unique)).2.1
  widths r hr := h.widths r (List.mem_append_right _ hr)

/-- Local freshness: distinct live slots, tokens and wires across a frame. -/
structure Separate (s f : Store) : Prop where
  slots : ∀ a ∈ Qleisli.slots s, ∀ b ∈ Qleisli.slots f, a ≠ b
  tokens : ∀ a ∈ Qleisli.tokens s, ∀ b ∈ Qleisli.tokens f, a ≠ b
  wires : ∀ a ∈ Qleisli.wires s, ∀ b ∈ Qleisli.wires f, a ≠ b

theorem Store.Valid.append {s f : Store} (hs : s.Valid) (hf : f.Valid)
    (sep : Separate s f) : (s ++ f).Valid where
  slots_unique := by simpa [slots] using
    List.nodup_append.mpr ⟨hs.slots_unique, hf.slots_unique, sep.slots⟩
  tokens_unique := by simpa [tokens] using
    List.nodup_append.mpr ⟨hs.tokens_unique, hf.tokens_unique, sep.tokens⟩
  wires_unique := by simpa [wires] using
    List.nodup_append.mpr ⟨hs.wires_unique, hf.wires_unique, sep.wires⟩
  widths r hr := (List.mem_append.mp hr).elim (hs.widths r) (hf.widths r)

theorem Config.Valid.reorder {vs ws : List Value} {s : Store}
    (h : (Config.mk vs s).Valid) (p : (own vs).Perm (own ws)) :
    (Config.mk ws s).Valid := ⟨p.symm.trans h.coverage, h.store_valid⟩

/-- Pair construction and pattern destructuring preserve the same occurrences. -/
theorem pair_ownership (a b : Value) (f : List Value) :
    own (.pair a b :: f) = own (a :: b :: f) := by
  simp [Value.own, List.append_assoc]

theorem pair_preserves {a b : Value} {f : List Value} {s : Store}
    (h : (Config.mk (a :: b :: f) s).Valid) :
    (Config.mk (.pair a b :: f) s).Valid :=
  h.reorder (by rw [pair_ownership])

/-- The first evaluated tuple field remains owned while the next is evaluated. -/
theorem pending_frame (env frame : List Value) (v : Value) :
    (own (env ++ v :: frame)).Perm (own ((v :: env) ++ frame)) := by
  simp only [own_append, own_cons]
  rw [← List.append_assoc]
  exact (List.perm_append_comm (l₁ := own env) (l₂ := v.own)).append_right _

/-- Actuals become callee locals; every suspended caller holder remains in frame. -/
theorem call_frame (caller args frame : List Value) :
    (own (caller ++ args ++ frame)).Perm (own (args ++ caller ++ frame)) := by
  simp only [own_append]
  exact List.perm_append_comm.append_right _

/-- Classical copying is allowed only after establishing an empty footprint. -/
theorem copy_classical {v : Value} {f : List Value} {s : Store}
    (hc : v.own = []) (h : (Config.mk (v :: f) s).Valid) :
    (Config.mk (v :: v :: f) s).Valid :=
  h.reorder (by simp [hc])

theorem Config.Valid.unique_holders {c : Config} (h : c.Valid) :
    ((own c.holders).map Port.slot).Nodup := by
  exact (h.coverage.map Port.slot).symm.nodup (by
    simpa [ports, slots, List.map_map] using h.store_valid.slots_unique)

/-- No implicit discard, including an owned register with no physical wires. -/
theorem closed_classical_no_resources {vs : List Value} {s : Store}
    (h : (Config.mk vs s).Valid) (hc : own vs = []) : s = [] := by
  have hp := h.coverage.length_eq
  simp [hc, ports] at hp
  exact List.length_eq_zero_iff.mp hp.symm

theorem quantum_unit_owns (slot : Nat) :
    (Value.quantum ⟨slot, .unit⟩).own = [⟨slot, .unit⟩] := rfl

end Qleisli
