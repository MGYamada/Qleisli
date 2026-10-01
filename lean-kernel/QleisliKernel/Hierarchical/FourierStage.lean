import QleisliKernel.Hierarchical.Gradient

/-! Bind a recursive Fourier stage to its actual ordered definition children.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
This is a pending component inspection, not a Fourier acceptance rule. The H,
controlled gradient, recursive child and finite-leaf equations remain explicit
obligations. Whole-artifact typing must precede production use. -/

namespace QleisliKernel.Hierarchical.FourierStage
open Artifact

structure Step where
  root : Definition
  enterIndex : Nat
  firstIndex : Nat
  gradientIndex : Nat
  lastIndex : Nat
  leaveIndex : Nat
  hIndex : Nat
  idleLowIndex : Nat
  idleHighIndex : Nat
  childIndex : Nat
  enter : Definition
  first : Definition
  gradient : Definition
  last : Definition
  leave : Definition
  h : Definition
  idleLow : Definition
  idleHigh : Definition
  child : Definition
  enterOp : StructuralOp
  leaveOp : StructuralOp
  deriving Repr

/-- Reject nonconstant arities before traversing an untrusted child array. -/
def project (artifact : Artifact) (index : Nat) : Option Step := do
  let root ← artifact.definitions[index]?
  let .sequence children := root.body | none
  if children.size != 5 then none else do
    let enterIndex ← children[0]?
    let firstIndex ← children[1]?
    let gradientIndex ← children[2]?
    let lastIndex ← children[3]?
    let leaveIndex ← children[4]?
    let enter ← artifact.definitions[enterIndex]?
    let first ← artifact.definitions[firstIndex]?
    let gradient ← artifact.definitions[gradientIndex]?
    let last ← artifact.definitions[lastIndex]?
    let leave ← artifact.definitions[leaveIndex]?
    let .structural enterOp := enter.body | none
    let .tensor hIndex idleLowIndex := first.body | none
    let .tensor idleHighIndex childIndex := last.body | none
    let .structural leaveOp := leave.body | none
    let h ← artifact.definitions[hIndex]?
    let idleLow ← artifact.definitions[idleLowIndex]?
    let idleHigh ← artifact.definitions[idleHighIndex]?
    let child ← artifact.definitions[childIndex]?
    return ⟨root,enterIndex,firstIndex,gradientIndex,lastIndex,leaveIndex,
      hIndex,idleLowIndex,idleHighIndex,childIndex,enter,first,gradient,last,leave,
      h,idleLow,idleHigh,child,enterOp,leaveOp⟩

def Bound (artifact : Artifact) (index : Nat) (s : Step) : Prop :=
  artifact.definitions[index]? = some s.root ∧
  s.root.body = .sequence #[s.enterIndex,s.firstIndex,s.gradientIndex,s.lastIndex,s.leaveIndex] ∧
  artifact.definitions[s.enterIndex]? = some s.enter ∧
  artifact.definitions[s.firstIndex]? = some s.first ∧
  artifact.definitions[s.gradientIndex]? = some s.gradient ∧
  artifact.definitions[s.lastIndex]? = some s.last ∧
  artifact.definitions[s.leaveIndex]? = some s.leave ∧
  artifact.definitions[s.hIndex]? = some s.h ∧
  artifact.definitions[s.idleLowIndex]? = some s.idleLow ∧
  artifact.definitions[s.idleHighIndex]? = some s.idleHigh ∧
  artifact.definitions[s.childIndex]? = some s.child ∧
  s.enter.body = .structural s.enterOp ∧
  s.first.body = .tensor s.hIndex s.idleLowIndex ∧
  s.last.body = .tensor s.idleHighIndex s.childIndex ∧
  s.leave.body = .structural s.leaveOp

private theorem five (children : Array Nat) (a b c d e : Nat)
    (size : children.size = 5) (ha : children[0]? = some a)
    (hb : children[1]? = some b) (hc : children[2]? = some c)
    (hd : children[3]? = some d) (he : children[4]? = some e) :
    children = #[a,b,c,d,e] := by
  apply Array.ext
  · simpa using size
  · intro i hi hj
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl
    · exact (Array.getElem?_eq_some_iff.mp ha).2
    · exact (Array.getElem?_eq_some_iff.mp hb).2
    · exact (Array.getElem?_eq_some_iff.mp hc).2
    · exact (Array.getElem?_eq_some_iff.mp hd).2
    · exact (Array.getElem?_eq_some_iff.mp he).2

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
      by assumption,by assumption,by assumption,by assumption,by assumption,
      by assumption,by assumption,by assumption,by assumption,by assumption⟩
    calc
      _ = .sequence _ := by assumption
      _ = _ := congrArg Body.sequence (five _ _ _ _ _ _ (by assumption)
        (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))

def closedBit (d : Definition) : Bool :=
  d.effect == Effect.unitary && NodeTyping.quantumOnly d.interface &&
    d.interface.inputs == d.interface.outputs &&
    ContractTyping.onePort d.interface.inputs #[.bit] &&
    (wires d.interface.inputs).size == 1

def identity (d : Definition) : Bool := match d.body with
  | .rewire map => Rule.identityMap d.interface map
  | _ => false

/-- Tensor order, complete type trees and full local interfaces are checked.
The H and child definitions must have their own semantics established later. -/
def shape (n : Nat) (s : Step) : Bool :=
  Gradient.register s.root (n+1) && Gradient.register s.child n &&
    Gradient.register s.idleLow n && closedBit s.h && closedBit s.idleHigh &&
    identity s.idleLow && identity s.idleHigh &&
    s.idleLow.interface == s.child.interface && s.h.interface == s.idleHigh.interface &&
    decide (s.enterOp = .takeBit (n+1) n) && decide (s.leaveOp = .putBit (n+1) n) &&
    s.enter.interface.inputs == s.root.interface.inputs &&
    s.enter.interface.outputs == NodeTyping.append s.h.interface.inputs s.child.interface.inputs &&
    s.first.interface == (⟨s.enter.interface.outputs,s.enter.interface.outputs⟩ : Interface) &&
    s.gradient.interface == s.first.interface && s.last.interface == s.first.interface &&
    s.leave.interface == Structural.swapped s.enter.interface &&
    Structural.axisMap s.enter.interface == Gradient.highAxes n &&
    Structural.axisMap s.leave.interface == Gradient.lowAxes n

def headers (s : Step) : List Interface :=
  [s.root.interface,s.enter.interface,s.first.interface,s.gradient.interface,
   s.last.interface,s.leave.interface,s.h.interface,s.idleLow.interface,
   s.idleHigh.interface,s.child.interface]

def scan (s : Step) : Nat :=
  96 + (headers s).foldl (fun n h => n+h.scan) 0

/-- Precharge all full metadata comparisons and computed positional routing.
No circuit repetitions or dense matrices are expanded. -/
def charge (s : Step) : Nat :=
  scan s + (headers s).foldl (fun n h =>
    n+32+16*(TypedRule.sideFields h.inputs+TypedRule.sideFields h.outputs)) 0 +
    8*(1+Ports.wireCount s.enter.interface.inputs+Ports.wireCount s.enter.interface.outputs)^2 +
    8*(1+Ports.wireCount s.leave.interface.inputs+Ports.wireCount s.leave.interface.outputs)^2

structure Pending where
  step : Step
  visits : Nat
  deriving Repr

/-- This five-node form is the positive lower-register stage. The one-bit
base omits the controlled gradient and is deliberately a separate obligation. -/
def inspect (artifact : Artifact) (n index remaining : Nat) : Except Error Pending :=
  if remaining > Limits.maxVisits || n = 0 || n > 7 then .error .limit else
  match project artifact index with
  | none => .error .contract
  | some s =>
    if scan s > remaining then .error .limit else
    let cost := charge s
    if cost > remaining then .error .limit else
    if !shape n s then .error .contract else .ok ⟨s,cost⟩

theorem inspect_sound (artifact : Artifact) (n index remaining : Nat) (pending : Pending)
    (accepted : inspect artifact n index remaining = .ok pending) :
    pending.visits ≤ remaining ∧ remaining ≤ 2000000 ∧ 0 < n ∧ n ≤ 7 ∧
    Bound artifact index pending.step ∧ shape n pending.step = true := by
  unfold inspect at accepted
  split at accepted
  next exceeded => contradiction
  next bounded =>
    simp only [Bool.or_eq_true,decide_eq_true_eq,not_or] at bounded
    split at accepted
    next absent => contradiction
    next s projected =>
      split at accepted
      next exceeded => contradiction
      next scanned =>
        dsimp only at accepted
        split at accepted
        next exceeded => contradiction
        next charged =>
          split at accepted
          next invalid => contradiction
          next valid =>
            cases Except.ok.inj accepted
            exact ⟨Nat.le_of_not_gt charged,by simp only [Limits.maxVisits] at *; omega,by simp only [Limits.maxVisits] at *; omega,by simp only [Limits.maxVisits] at *; omega,project_bound artifact index s projected,
              by simpa using valid⟩

end QleisliKernel.Hierarchical.FourierStage
