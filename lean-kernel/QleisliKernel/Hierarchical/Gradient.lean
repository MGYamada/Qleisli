import QleisliKernel.Hierarchical.TypedRule

/-! Inspect the actual recursively shared phase-gradient definitions.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
This component must be combined with actual whole-artifact typing and semantic
proofs before issuing evidence. It accepts no matrix, cache or success flag. -/

namespace QleisliKernel.Hierarchical.Gradient
open Artifact

def highAxes (n : Nat) : List Nat := n :: List.range n
def lowAxes (n : Nat) : List Nat := (List.range n).map (· + 1) ++ [0]

structure Step where
  root : Definition
  enterIndex : Nat
  actionIndex : Nat
  leaveIndex : Nat
  phaseIndex : Nat
  tailIndex : Nat
  enter : Definition
  action : Definition
  leave : Definition
  phase : Definition
  tail : Definition
  enterOp : StructuralOp
  leaveOp : StructuralOp
  target : Nat
  numerator : Nat
  exponent : Nat
  deriving Repr

/-- Inspect fixed arities before reading the selected children. -/
def project (artifact : Artifact) (index : Nat) : Option Step := do
  let root ← artifact.definitions[index]?
  let .sequence children := root.body | none
  if children.size != 3 then none else do
    let enterIndex ← children[0]?
    let actionIndex ← children[1]?
    let leaveIndex ← children[2]?
    let enter ← artifact.definitions[enterIndex]?
    let action ← artifact.definitions[actionIndex]?
    let leave ← artifact.definitions[leaveIndex]?
    let .structural enterOp := enter.body | none
    let .tensor phaseIndex tailIndex := action.body | none
    let .structural leaveOp := leave.body | none
    let phase ← artifact.definitions[phaseIndex]?
    let tail ← artifact.definitions[tailIndex]?
    let .dyadicPhase target numerator exponent := phase.body | none
    return ⟨root,enterIndex,actionIndex,leaveIndex,phaseIndex,tailIndex,
      enter,action,leave,phase,tail,enterOp,leaveOp,target,numerator,exponent⟩

def Bound (artifact : Artifact) (index : Nat) (s : Step) : Prop :=
  artifact.definitions[index]? = some s.root ∧
  s.root.body = .sequence #[s.enterIndex,s.actionIndex,s.leaveIndex] ∧
  artifact.definitions[s.enterIndex]? = some s.enter ∧
  artifact.definitions[s.actionIndex]? = some s.action ∧
  artifact.definitions[s.leaveIndex]? = some s.leave ∧
  artifact.definitions[s.phaseIndex]? = some s.phase ∧
  artifact.definitions[s.tailIndex]? = some s.tail ∧
  s.enter.body = .structural s.enterOp ∧
  s.action.body = .tensor s.phaseIndex s.tailIndex ∧
  s.leave.body = .structural s.leaveOp ∧
  s.phase.body = .dyadicPhase s.target s.numerator s.exponent

private theorem triple (children : Array Nat) (a b c : Nat)
    (size : children.size = 3) (ha : children[0]? = some a)
    (hb : children[1]? = some b) (hc : children[2]? = some c) : children = #[a,b,c] := by
  apply Array.ext
  · simpa using size
  · intro i hi hj
    have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases cases with rfl | rfl | rfl
    · exact (Array.getElem?_eq_some_iff.mp ha).2
    · exact (Array.getElem?_eq_some_iff.mp hb).2
    · exact (Array.getElem?_eq_some_iff.mp hc).2

theorem project_bound (artifact : Artifact) (index : Nat) (s : Step)
    (projected : project artifact index = some s) : Bound artifact index s := by
  unfold project at projected
  simp only [bind,Option.bind] at projected
  repeat (split at projected <;> (try dsimp only at projected) <;> (try contradiction))
  all_goals try contradiction
  all_goals
    cases Option.some.inj projected
    simp only [bne_iff_ne,Classical.not_not] at *
    simp only [Bound]
    refine ⟨by assumption,?_,by assumption,by assumption,by assumption,
      by assumption,by assumption,by assumption,by assumption,by assumption,by assumption⟩
    calc
      _ = .sequence _ := by assumption
      _ = _ := congrArg Body.sequence (triple _ _ _ _ (by assumption)
        (by assumption) (by assumption) (by assumption))

/-- Complete register type and width; an empty register remains an owner. -/
def register (d : Definition) (width : Nat) : Bool :=
  d.effect == Effect.unitary && NodeTyping.quantumOnly d.interface &&
    d.interface.inputs == d.interface.outputs &&
    ContractTyping.onePort d.interface.inputs #[.bits width] &&
    (wires d.interface.inputs).size == width

def bit (d : Definition) (owner : Nat) : Bool :=
  d.effect == Effect.unitary && NodeTyping.quantumOnly d.interface &&
    d.interface.inputs == d.interface.outputs && (do
      let p : QuantumPort ← d.interface.inputs.quantum[0]?
      return d.interface.inputs.quantum == #[p] && p.basis == #[Layout.TypeAtom.bit] &&
        p.owner == owner && p.axes.size == 1).getD false

def base (d : Definition) : Bool :=
  register d 0 && match d.body with
  | .rewire map => map.owners == #[0] && map.axes.isEmpty && map.classical.isEmpty
  | _ => false

/-- Geometry is checked on actual local labels. Positional routing is compared
only after extracting it from the full enter/leave interfaces. -/
def shape (precision n : Nat) (s : Step) : Bool :=
  register s.root (n+1) && register s.tail n && bit s.phase s.target &&
    s.numerator == 1 && s.exponent == precision-n &&
    decide (s.enterOp = .takeBit (n+1) n) && decide (s.leaveOp = .putBit (n+1) n) &&
    s.enter.interface.inputs == s.root.interface.inputs &&
    s.enter.interface.outputs == NodeTyping.append s.phase.interface.inputs s.tail.interface.inputs &&
    s.action.interface == (⟨s.enter.interface.outputs,s.enter.interface.outputs⟩ : Interface) &&
    s.leave.interface == Structural.swapped s.enter.interface &&
    Structural.axisMap s.enter.interface == highAxes n &&
    Structural.axisMap s.leave.interface == lowAxes n

def headers (s : Step) : List Interface :=
  [s.root.interface,s.enter.interface,s.action.interface,s.leave.interface,s.phase.interface,s.tail.interface]

def headerScan (d : Definition) : Nat := 8 + d.interface.scan
def headerFields (d : Definition) : Nat :=
  16 + 8 * (TypedRule.sideFields d.interface.inputs + TypedRule.sideFields d.interface.outputs)

def scan (s : Step) : Nat :=
  64 + (headers s).foldl (fun n h => n + h.scan) 0

/-- Linear metadata comparisons plus both computed routing lookups; no dense
matrix or repeated circuit body is constructed. -/
def charge (s : Step) : Nat :=
  scan s + (headers s).foldl (fun n h =>
    n + 16 + 8*(TypedRule.sideFields h.inputs + TypedRule.sideFields h.outputs)) 0 +
    8*(1+Ports.wireCount s.enter.interface.inputs+Ports.wireCount s.enter.interface.outputs)^2 +
    8*(1+Ports.wireCount s.leave.interface.inputs+Ports.wireCount s.leave.interface.outputs)^2

inductive Matches (artifact : Artifact) (precision : Nat) : Nat → Nat → Prop where
  | empty (index : Nat) (d : Definition)
      (found : artifact.definitions[index]? = some d) (valid : base d = true) :
      Matches artifact precision 0 index
  | step (n index : Nat) (s : Step)
      (bound : Bound artifact index s) (valid : shape precision n s = true)
      (child : Matches artifact precision n s.tailIndex) :
      Matches artifact precision (n+1) index

structure Pending where
  visits : Nat
  deriving Repr

/-- Use the total natural-number recursor directly. Surface recursive
syntax generated a partial `_unsafe_rec` implementation helper in Lean 4.30;
that alternative is rejected by the compiled-declaration policy. -/
def inspectAux (artifact : Artifact) (precision width : Nat) : Nat → Nat → Except Error Pending :=
  Nat.rec (fun index remaining =>
    match artifact.definitions[index]? with
    | none => .error .invalidIr
    | some d =>
      if headerScan d > remaining then .error .limit else
      let cost := headerScan d + headerFields d
      if cost > remaining then .error .limit else
      if base d then .ok ⟨cost⟩ else .error .contract)
    (fun n recurse index remaining =>
      match project artifact index with
      | none => .error .contract
      | some s =>
        if scan s > remaining then .error .limit else
        let cost := charge s
        if cost > remaining then .error .limit else
        if !shape precision n s then .error .contract else
        match recurse s.tailIndex (remaining-cost) with
        | .error e => .error e
        | .ok child => .ok ⟨cost+child.visits⟩) width

theorem inspectAux_zero (artifact : Artifact) (precision index remaining : Nat) :
    inspectAux artifact precision 0 index remaining =
      (match artifact.definitions[index]? with
      | none => .error .invalidIr
      | some d =>
        if headerScan d > remaining then .error .limit else
        let cost := headerScan d + headerFields d
        if cost > remaining then .error .limit else
        if base d then .ok ⟨cost⟩ else .error .contract) := rfl

theorem inspectAux_succ (artifact : Artifact) (precision n index remaining : Nat) :
    inspectAux artifact precision (n+1) index remaining =
      (match project artifact index with
      | none => .error .contract
      | some s =>
        if scan s > remaining then .error .limit else
        let cost := charge s
        if cost > remaining then .error .limit else
        if !shape precision n s then .error .contract else
        match inspectAux artifact precision n s.tailIndex (remaining-cost) with
        | .error e => .error e
        | .ok child => .ok ⟨cost+child.visits⟩) := rfl

def inspect (artifact : Artifact) (precision width index remaining : Nat) : Except Error Pending :=
  if remaining > 2000000 || precision = 0 || precision > 8 || width > precision then .error .limit
  else inspectAux artifact precision width index remaining

theorem inspectAux_sound (artifact : Artifact) (precision width index remaining : Nat)
    (pending : Pending) (accepted : inspectAux artifact precision width index remaining = .ok pending) :
    pending.visits ≤ remaining ∧ Matches artifact precision width index := by
  induction width generalizing index remaining pending with
  | zero =>
    simp only [inspectAux_zero] at accepted
    split at accepted
    next absent => contradiction
    next d found =>
      split at accepted
      next exceeded => contradiction
      next scanned =>
        split at accepted
        next exceeded => contradiction
        next charged =>
          split at accepted
          next valid =>
            cases Except.ok.inj accepted
            exact ⟨Nat.le_of_not_gt charged,.empty index d found valid⟩
          next invalid => contradiction
  | succ n ih =>
    simp only [inspectAux_succ] at accepted
    split at accepted
    next absent => contradiction
    next s projected =>
      split at accepted
      next exceeded => contradiction
      next scanned =>
        split at accepted
        next exceeded => contradiction
        next charged =>
          split at accepted
          next invalid => contradiction
          next valid =>
            split at accepted
            next failed => contradiction
            next child checked =>
              cases Except.ok.inj accepted
              obtain ⟨cost,matched⟩ := ih s.tailIndex (remaining-charge s) child checked
              refine ⟨by dsimp only; omega,.step n index s (project_bound artifact index s projected)
                (by simpa using valid) matched⟩

theorem inspect_sound (artifact : Artifact) (precision width index remaining : Nat)
    (pending : Pending) (accepted : inspect artifact precision width index remaining = .ok pending) :
    pending.visits ≤ remaining ∧ remaining ≤ 2000000 ∧
    1 ≤ precision ∧ precision ≤ 8 ∧ width ≤ precision ∧ Matches artifact precision width index := by
  unfold inspect at accepted
  split at accepted
  next invalid => contradiction
  next limits =>
    have bounds : remaining ≤ 2000000 ∧ precision ≠ 0 ∧ precision ≤ 8 ∧ width ≤ precision := by
      simpa only [Bool.or_eq_true,decide_eq_true_eq,not_or,Nat.not_lt,and_assoc] using limits
    obtain ⟨cost,matched⟩ := inspectAux_sound artifact precision width index remaining pending accepted
    exact ⟨cost,bounds.1,by omega,bounds.2.2.1,bounds.2.2.2,matched⟩

theorem high_zero (n : Nat) : Layout.indexAt (highAxes n) 0 = n := by
  simp [Layout.indexAt,highAxes]

theorem high_succ (n i : Nat) (inside : i < n) : Layout.indexAt (highAxes n) (i+1) = i := by
  simp [Layout.indexAt,highAxes,inside]

theorem low_inside (n i : Nat) (inside : i < n) : Layout.indexAt (lowAxes n) i = i+1 := by
  simp [Layout.indexAt,lowAxes,List.getElem?_append,inside]

theorem low_last (n : Nat) : Layout.indexAt (lowAxes n) n = 0 := by
  simp [Layout.indexAt,lowAxes]

/-- Route the last bit to the first slot and restore it afterward. These
inverse laws concern all widths, not enumerated assignments. -/
theorem routing (n : Nat) : Layout.Permutation (n+1) (highAxes n) (lowAxes n) := by
  refine ⟨by simp [highAxes],by simp [lowAxes],?_⟩
  intro i
  have hb : Layout.indexAt (lowAxes n) i < n+1 := by
    by_cases inside : i.val < n
    · rw [low_inside n i inside]; omega
    · have last : i.val = n := by omega
      rw [last,low_last]; omega
  have hf : Layout.indexAt (highAxes n) i < n+1 := by
    cases hi : i.val with
    | zero => rw [high_zero]; omega
    | succ k => rw [high_succ n k (by omega)]; omega
  refine ⟨hf,hb,?_,?_⟩
  · by_cases inside : i.val < n
    · rw [low_inside n i inside,high_succ n i inside]
    · have last : i.val = n := by omega
      rw [last,low_last,high_zero]
  · cases hi : i.val with
    | zero => rw [high_zero,low_last]
    | succ k => rw [high_succ n k (by omega),low_inside n k (by omega)]

end QleisliKernel.Hierarchical.Gradient
