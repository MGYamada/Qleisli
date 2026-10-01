import QleisliKernel.Hierarchical.FourierStage

/-! Bind the actual finite H obligation and explicit one-bit owner renaming.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
Opaque payloads are never validated by this inspector. They must be freshly
decoded and compared to the independently specified phase-fixed H matrix. -/

namespace QleisliKernel.Hierarchical.Hadamard
open Artifact

structure Request where
  root : Definition
  leafIndex : Nat
  renameIndex : Nat
  leaf : Definition
  rename : Definition
  program : ByteArray
  routing : PortMap
  deriving Repr

def project (artifact : Artifact) (index : Nat) : Option Request := do
  let root ← artifact.definitions[index]?
  let .sequence children := root.body | none
  if children.size != 2 then none else do
    let leafIndex ← children[0]?
    let renameIndex ← children[1]?
    let leaf ← artifact.definitions[leafIndex]?
    let rename ← artifact.definitions[renameIndex]?
    let .leaf program := leaf.body | none
    let .rewire routing := rename.body | none
    return ⟨root,leafIndex,renameIndex,leaf,rename,program,routing⟩

def Bound (artifact : Artifact) (index : Nat) (r : Request) : Prop :=
  artifact.definitions[index]? = some r.root ∧
  r.root.body = .sequence #[r.leafIndex,r.renameIndex] ∧
  artifact.definitions[r.leafIndex]? = some r.leaf ∧
  artifact.definitions[r.renameIndex]? = some r.rename ∧
  r.leaf.body = .leaf r.program ∧ r.rename.body = .rewire r.routing

private theorem pair (children : Array Nat) (a b : Nat)
    (size : children.size = 2) (ha : children[0]? = some a)
    (hb : children[1]? = some b) : children = #[a,b] := by
  apply Array.ext
  · simpa using size
  · intro i hi hj
    have cases : i = 0 ∨ i = 1 := by omega
    rcases cases with rfl | rfl
    · exact (Array.getElem?_eq_some_iff.mp ha).2
    · exact (Array.getElem?_eq_some_iff.mp hb).2

theorem project_bound (artifact : Artifact) (index : Nat) (r : Request)
    (projected : project artifact index = some r) : Bound artifact index r := by
  unfold project at projected
  simp only [bind,Option.bind] at projected
  repeat (split at projected <;> (try dsimp only at projected) <;> (try contradiction))
  all_goals try contradiction
  all_goals
    cases Option.some.inj projected
    simp only [bne_iff_ne,Classical.not_not] at *
    refine ⟨by assumption,?_,by assumption,by assumption,by assumption,by assumption⟩
    calc
      _ = .sequence _ := by assumption
      _ = _ := congrArg Body.sequence (pair _ _ _ (by assumption) (by assumption) (by assumption))

def shape (r : Request) : Bool :=
  FourierStage.closedBit r.root && r.leaf.effect == Effect.unitary &&
    r.rename.effect == Effect.unitary && NodeTyping.quantumOnly r.leaf.interface &&
    ContractTyping.onePort r.leaf.interface.outputs #[.bit] &&
    (wires r.leaf.interface.outputs).size == 1 &&
    r.leaf.interface.inputs == r.root.interface.inputs &&
    r.rename.interface.inputs == r.leaf.interface.outputs &&
    r.rename.interface.outputs == r.root.interface.outputs &&
    r.routing.owners == #[0] && r.routing.axes == #[0] && r.routing.classical.isEmpty

def headers (r : Request) : List Interface := [r.root.interface,r.leaf.interface,r.rename.interface]

def scan (r : Request) : Nat := 48 + (headers r).foldl (fun n h => n+h.scan) 0

def charge (r : Request) : Nat := scan r + (headers r).foldl (fun n h =>
  n+32+16*(TypedRule.sideFields h.inputs+TypedRule.sideFields h.outputs)) 0

structure Pending where
  request : Request
  visits : Nat
  deriving Repr

def inspect (artifact : Artifact) (index remaining : Nat) : Except Error Pending :=
  if remaining > Limits.maxVisits then .error .limit else
  match project artifact index with
  | none => .error .contract
  | some r =>
    if r.program.size > Limits.maxPayloadBytes || scan r > remaining then .error .limit else
    let cost := charge r
    if cost > remaining then .error .limit else
    if !shape r then .error .contract else .ok ⟨r,cost⟩

theorem inspect_sound (artifact : Artifact) (index remaining : Nat) (pending : Pending)
    (accepted : inspect artifact index remaining = .ok pending) :
    pending.visits ≤ remaining ∧ remaining ≤ 2000000 ∧
    Bound artifact index pending.request ∧ shape pending.request = true ∧
    pending.request.program.size ≤ 16777216 := by
  unfold inspect at accepted
  split at accepted
  next exceeded => contradiction
  next bounded =>
    split at accepted
    next absent => contradiction
    next r projected =>
      split at accepted
      next exceeded => contradiction
      next scanned =>
        simp only [Bool.or_eq_true,decide_eq_true_eq,not_or] at scanned
        dsimp only at accepted
        split at accepted
        next exceeded => contradiction
        next charged =>
          split at accepted
          next invalid => contradiction
          next valid =>
            cases Except.ok.inj accepted
            exact ⟨Nat.le_of_not_gt charged,Nat.le_of_not_gt bounded,
              project_bound artifact index r projected,by simpa using valid,by simpa using Nat.le_of_not_gt scanned.1⟩

end QleisliKernel.Hierarchical.Hadamard
