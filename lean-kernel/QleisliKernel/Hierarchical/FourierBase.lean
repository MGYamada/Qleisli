import QleisliKernel.Hierarchical.FourierStage

/-! Actual four-node one-bit base of the shared Fourier recursion.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
Reuse the stage's geometry record: its gradient fields alias the first tensor
only as unused metadata. No gradient child is inserted into the artifact.
The Bound predicate below records the actual four children, not five. -/

namespace QleisliKernel.Hierarchical.FourierBase
open Artifact

def project (artifact : Artifact) (index : Nat) : Option FourierStage.Step := do
  let root ← artifact.definitions[index]?
  let .sequence children := root.body | none
  if children.size != 4 then none else do
    let enterIndex ← children[0]?
    let firstIndex ← children[1]?
    let lastIndex ← children[2]?
    let leaveIndex ← children[3]?
    let enter ← artifact.definitions[enterIndex]?
    let first ← artifact.definitions[firstIndex]?
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
    return ⟨root,enterIndex,firstIndex,firstIndex,lastIndex,leaveIndex,
      hIndex,idleLowIndex,idleHighIndex,childIndex,enter,first,first,last,leave,
      h,idleLow,idleHigh,child,enterOp,leaveOp⟩

def Bound (artifact : Artifact) (index : Nat) (s : FourierStage.Step) : Prop :=
  artifact.definitions[index]? = some s.root ∧
  s.root.body = .sequence #[s.enterIndex,s.firstIndex,s.lastIndex,s.leaveIndex] ∧
  artifact.definitions[s.enterIndex]? = some s.enter ∧
  artifact.definitions[s.firstIndex]? = some s.first ∧
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

private theorem four (children : Array Nat) (a b c d : Nat)
    (size : children.size = 4) (ha : children[0]? = some a)
    (hb : children[1]? = some b) (hc : children[2]? = some c)
    (hd : children[3]? = some d) : children = #[a,b,c,d] := by
  apply Array.ext
  · simpa using size
  · intro i hi hj
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · exact (Array.getElem?_eq_some_iff.mp ha).2
    · exact (Array.getElem?_eq_some_iff.mp hb).2
    · exact (Array.getElem?_eq_some_iff.mp hc).2
    · exact (Array.getElem?_eq_some_iff.mp hd).2

theorem project_bound (artifact : Artifact) (index : Nat) (s : FourierStage.Step)
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
      by assumption,by assumption,by assumption,by assumption⟩
    calc
      _ = .sequence _ := by assumption
      _ = _ := congrArg Body.sequence (four _ _ _ _ _ (by assumption)
        (by assumption) (by assumption) (by assumption) (by assumption))

def shape (s : FourierStage.Step) : Bool :=
  FourierStage.shape 0 s && FourierStage.identity s.child

def inspect (artifact : Artifact) (index remaining : Nat) : Except Error FourierStage.Pending :=
  if remaining > Limits.maxVisits then .error .limit else
  match project artifact index with
  | none => .error .contract
  | some s =>
    if FourierStage.scan s > remaining then .error .limit else
    let cost := FourierStage.charge s
    if cost > remaining then .error .limit else
    if !shape s then .error .contract else .ok ⟨s,cost⟩

theorem inspect_sound (artifact : Artifact) (index remaining : Nat) (pending : FourierStage.Pending)
    (accepted : inspect artifact index remaining = .ok pending) :
    pending.visits ≤ remaining ∧ remaining ≤ 2000000 ∧
    Bound artifact index pending.step ∧ shape pending.step = true := by
  unfold inspect at accepted
  split at accepted
  next exceeded => contradiction
  next bounded =>
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
            exact ⟨Nat.le_of_not_gt charged,Nat.le_of_not_gt bounded,
              project_bound artifact index s projected,by simpa using valid⟩

end QleisliKernel.Hierarchical.FourierBase
