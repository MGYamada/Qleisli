import Qleisli.Resource
import Mathlib.Data.Set.Basic

/-!
# Lexical scope exit and its ownership footprint

This is the lookup-level model of the frontend's scope-closing algorithm.
An absent name, a spent binding, and a live value are distinct states. The
theorems below concern this model, not all Rust executions or a complete source
semantics. Relating the entry/current snapshots and rebound set to an execution
trace, and relating finite maps and value equality to this model, remain
implementation-adequacy premises.
-/

namespace Qleisli

def Value.ownsQuantum : Value → Bool
  | .unit | .classical _ => false
  | .quantum _ => true
  | .pair a b => a.ownsQuantum || b.ownsQuantum

@[simp] theorem Value.ownsQuantum_eq_false_iff (v : Value) :
    v.ownsQuantum = false ↔ v.own = [] := by
  induction v <;> simp_all [Value.ownsQuantum, Value.own]

@[simp] theorem Value.ownsQuantum_eq_true_iff (v : Value) :
    v.ownsQuantum = true ↔ v.own ≠ [] := by
  cases h : v.ownsQuantum <;> simp_all [← Value.ownsQuantum_eq_false_iff]

namespace Scope

/-- `none` is absent, `some none` is spent, `some (some v)` is live. -/
abbrev Lookup := Option (Option Value)

abbrev Env (Name : Type) := Name → Lookup

def footprint : Lookup → List Port
  | some (some v) => v.own
  | _ => []

def domain {Name : Type} (env : Env Name) : Set Name := {n | env n ≠ none}

/-- The rejection guard checks the whole value, including mixed pairs. -/
def Leak {Name : Type} (entry current : Env Name) (rebound : Set Name) (n : Name) : Prop :=
  ∃ v, current n = some (some v) ∧ v.ownsQuantum = true ∧
    (n ∈ rebound ∨ entry n ≠ current n)

/-- Every surviving current quantum value must be an unchanged, unrebound entry. -/
def Approved {Name : Type} (entry current : Env Name) (rebound : Set Name) : Prop :=
  ∀ n v, current n = some (some v) → v.ownsQuantum = true →
    n ∉ rebound ∧ entry n = some (some v)

/-- Project one binding; membership in the rebound set is supplied as a Boolean. -/
def exitBinding (entry current : Lookup) (rebound : Bool) : Lookup :=
  match entry with
  | none => none
  | some none => some none
  | some (some v) =>
    if v.ownsQuantum then
      if rebound then some none
      else if current = some (some v) then some (some v) else some none
    else some (some v)

/-- Restore the entry domain and its classical values, retaining only unchanged
quantum bindings. This projection is committed only after `Approved` holds. -/
noncomputable def exit {Name : Type} (entry current : Env Name) (rebound : Set Name) :
    Env Name := by
  classical
  exact fun n => exitBinding (entry n) (current n) (decide (n ∈ rebound))

/-- The mathematical success/failure interface. Universal approval is a
specification predicate; the Rust implementation checks a finite current map. -/
noncomputable def close {Name : Type} (entry current : Env Name) (rebound : Set Name) :
    Option (Env Name) := by
  classical
  exact if Approved entry current rebound then some (exit entry current rebound) else none

theorem approved_iff_no_leak {Name : Type} (entry current : Env Name) (rebound : Set Name) :
    Approved entry current rebound ↔ ∀ n, ¬ Leak entry current rebound n := by
  constructor
  · intro h n ⟨v, hl, hq, bad⟩
    obtain ⟨hr, he⟩ := h n v hl hq
    rcases bad with hb | hb
    · exact hr hb
    · exact hb (he.trans hl.symm)
  · intro h n v hl hq
    constructor
    · intro hr
      exact h n ⟨v, hl, hq, Or.inl hr⟩
    · by_contra he
      apply h n
      exact ⟨v, hl, hq, Or.inr (by simpa [hl] using he)⟩

@[simp] theorem close_eq_none_iff {Name : Type} (entry current : Env Name)
    (rebound : Set Name) : close entry current rebound = none ↔ ¬ Approved entry current rebound := by
  classical
  simp [close]

theorem close_of_approved {Name : Type} {entry current : Env Name} {rebound : Set Name}
    (h : Approved entry current rebound) :
    close entry current rebound = some (exit entry current rebound) := by
  classical
  simp [close, h]

theorem close_eq_some_iff {Name : Type} (entry current : Env Name)
    (rebound : Set Name) (output : Env Name) :
    close entry current rebound = some output ↔
      Approved entry current rebound ∧ output = exit entry current rebound := by
  classical
  by_cases h : Approved entry current rebound <;> simp [close, h, eq_comm]

theorem close_rejects_leak {Name : Type} {entry current : Env Name} {rebound : Set Name}
    {n : Name} (h : Leak entry current rebound n) : close entry current rebound = none := by
  rw [close_eq_none_iff]
  intro approved
  exact (approved_iff_no_leak entry current rebound).mp approved n h

@[simp] theorem exit_absent {Name : Type} {entry current : Env Name} {rebound : Set Name}
    {n : Name} (h : entry n = none) : exit entry current rebound n = none := by
  simp [exit, exitBinding, h]

@[simp] theorem exit_spent {Name : Type} {entry current : Env Name} {rebound : Set Name}
    {n : Name} (h : entry n = some none) : exit entry current rebound n = some none := by
  simp [exit, exitBinding, h]

theorem exit_classical {Name : Type} {entry current : Env Name} {rebound : Set Name}
    {n : Name} {v : Value} (h : entry n = some (some v)) (hc : v.own = []) :
    exit entry current rebound n = some (some v) := by
  have hq := (Value.ownsQuantum_eq_false_iff v).mpr hc
  simp [exit, exitBinding, h, hq]

theorem exit_quantum_keep_iff {Name : Type} {entry current : Env Name} {rebound : Set Name}
    {n : Name} {v : Value} (h : entry n = some (some v)) (hq : v.ownsQuantum = true) :
    exit entry current rebound n = some (some v) ↔
      n ∉ rebound ∧ current n = some (some v) := by
  classical
  by_cases hr : n ∈ rebound <;> by_cases hl : current n = some (some v) <;>
    simp [exit, exitBinding, h, hq, hr, hl]

theorem approved_quantum_retained {Name : Type} {entry current : Env Name}
    {rebound : Set Name} {n : Name} {v : Value}
    (approved : Approved entry current rebound) (hl : current n = some (some v))
    (hq : v.ownsQuantum = true) : exit entry current rebound n = some (some v) := by
  obtain ⟨hr, he⟩ := approved n v hl hq
  exact (exit_quantum_keep_iff he hq).mpr ⟨hr, hl⟩

theorem exit_domain {Name : Type} (entry current : Env Name) (rebound : Set Name) :
    domain (exit entry current rebound) = domain entry := by
  classical
  ext n
  cases he : entry n with
  | none => simp [domain, exit, exitBinding, he]
  | some binding =>
    cases binding with
    | none => simp [domain, exit, exitBinding, he]
    | some v =>
      simp only [domain, Set.mem_setOf_eq, exit, exitBinding, he]
      split_ifs <;> simp

theorem introduced_quantum_rejected {Name : Type} {entry current : Env Name}
    {rebound : Set Name} {n : Name} {v : Value}
    (he : entry n = none) (hl : current n = some (some v)) (hq : v.ownsQuantum = true) :
    close entry current rebound = none := by
  rw [close_eq_none_iff]
  intro h
  have hh := (h n v hl hq).2
  simp [he] at hh

theorem rebound_quantum_rejected {Name : Type} {entry current : Env Name}
    {rebound : Set Name} {n : Name} {v : Value}
    (hr : n ∈ rebound) (hl : current n = some (some v)) (hq : v.ownsQuantum = true) :
    close entry current rebound = none := by
  rw [close_eq_none_iff]
  intro h
  exact (h n v hl hq).1 hr

/-- A zero-width quantum value still owns a slot and is subject to rejection. -/
theorem quantum_unit_is_linear (slot : Nat) :
    (Value.quantum ⟨slot, .unit⟩).ownsQuantum = true ∧
      footprint (some (some (.quantum ⟨slot, .unit⟩))) = [⟨slot, .unit⟩] := by
  simp [Value.ownsQuantum, footprint, Value.own]

theorem exit_footprint {Name : Type} {entry current : Env Name} {rebound : Set Name}
    (approved : Approved entry current rebound) (n : Name) :
    footprint (exit entry current rebound n) = footprint (current n) := by
  classical
  cases hl : current n with
  | none =>
    cases he : entry n with
    | none => simp [exit, exitBinding, footprint, he]
    | some binding =>
      cases binding with
      | none => simp [exit, exitBinding, footprint, he]
      | some v =>
        cases hq : v.ownsQuantum <;> by_cases hr : n ∈ rebound <;>
          simp_all [exit, exitBinding, footprint]
  | some binding =>
    cases binding with
    | none =>
      cases he : entry n with
      | none => simp [exit, exitBinding, footprint, he]
      | some binding =>
        cases binding with
        | none => simp [exit, exitBinding, footprint, he]
        | some v =>
          cases hq : v.ownsQuantum <;> by_cases hr : n ∈ rebound <;>
            simp_all [exit, exitBinding, footprint]
    | some v =>
      cases hq : v.ownsQuantum with
      | true =>
        obtain ⟨hr, he⟩ := approved n v hl hq
        simp [exit, exitBinding, footprint, he, hl, hq, hr]
      | false =>
        have hv := (Value.ownsQuantum_eq_false_iff v).mp hq
        cases he : entry n with
        | none => simp [exit, exitBinding, footprint, he, hv]
        | some binding =>
          cases binding with
          | none => simp [exit, exitBinding, footprint, he, hv]
          | some u =>
            cases hu : u.ownsQuantum <;> by_cases hr : n ∈ rebound <;>
              by_cases heq : v = u <;>
              simp_all [exit, exitBinding, footprint]

/-- With a complete, duplicate-free list of map names this is the whole
environment footprint. The equality itself holds for any finite name list. -/
def footprintOn {Name : Type} (env : Env Name) (names : List Name) : List Port :=
  names.flatMap (fun n => footprint (env n))

theorem exit_footprintOn {Name : Type} {entry current : Env Name} {rebound : Set Name}
    (approved : Approved entry current rebound) (names : List Name) :
    footprintOn (exit entry current rebound) names = footprintOn current names := by
  induction names with
  | nil => rfl
  | cons n names ih =>
    simp only [footprintOn, List.flatMap_cons] at *
    rw [exit_footprint approved n, ih]

/-- Successful closure preserves the entry domain and the current quantum
footprint, although classical bindings can differ between current and output. -/
theorem close_preserves {Name : Type} {entry current output : Env Name}
    {rebound : Set Name} (h : close entry current rebound = some output) :
    domain output = domain entry ∧ ∀ n, footprint (output n) = footprint (current n) := by
  obtain ⟨approved, rfl⟩ := (close_eq_some_iff entry current rebound output).mp h
  exact ⟨exit_domain entry current rebound, exit_footprint approved⟩

theorem close_footprintOn {Name : Type} {entry current output : Env Name}
    {rebound : Set Name} (h : close entry current rebound = some output) (names : List Name) :
    footprintOn output names = footprintOn current names := by
  obtain ⟨approved, rfl⟩ := (close_eq_some_iff entry current rebound output).mp h
  exact exit_footprintOn approved names

end Scope
end Qleisli
