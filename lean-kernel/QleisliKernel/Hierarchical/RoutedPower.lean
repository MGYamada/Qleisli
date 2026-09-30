import QleisliKernel.Hierarchical.Wiring

/-! Actual controlled powers with phase-free owner-renaming shells.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
This inspector returns a component obligation, not semantic evidence. Complete
artifact typing and independent binding of the actual provider remain required.
It reads no proposed meaning, proof conclusion, provider name or success flag. -/

namespace QleisliKernel.Hierarchical.RoutedPower
open Artifact

structure Request where
  width : Nat
  exponent : Nat
  provider : Nat
  interface : Interface
  deriving Repr

structure View where
  root : Definition
  childIndex : Nat
  child : Definition
  coreIndex : Nat
  core : Definition
  provider : Definition
  routes : List Nat
  deriving Repr

/-- A bounded projection of actual bodies. The source may elide repeat one or
surround the provider/power with exactly two independently checked wire routes. -/
def project (artifact : Artifact) (index provider : Nat) : Option View := do
  let root ← artifact.definitions[index]?
  let .control childIndex true := root.body | none
  let child ← artifact.definitions[childIndex]?
  let providerDefinition ← artifact.definitions[provider]?
  if childIndex == provider then
    return ⟨root,childIndex,child,childIndex,child,providerDefinition,[]⟩
  else match child.body with
  | .sequence children =>
    if children.size != 3 then none else do
      let enter ← children[0]?
      let coreIndex ← children[1]?
      let leave ← children[2]?
      let core ← artifact.definitions[coreIndex]?
      return ⟨root,childIndex,child,coreIndex,core,providerDefinition,[enter,leave]⟩
  | _ => return ⟨root,childIndex,child,childIndex,child,providerDefinition,[]⟩

/-- The full source of each accepted projection remains in the same artifact. -/
def Bound (artifact : Artifact) (index provider : Nat) (v : View) : Prop :=
  artifact.definitions[index]? = some v.root ∧
  v.root.body = .control v.childIndex true ∧
  artifact.definitions[v.childIndex]? = some v.child ∧
  artifact.definitions[v.coreIndex]? = some v.core ∧
  artifact.definitions[provider]? = some v.provider ∧
  ((v.routes = [] ∧ v.coreIndex = v.childIndex ∧ v.core = v.child) ∨
    ∃ enter leave, v.routes = [enter,leave] ∧
      v.child.body = .sequence #[enter,v.coreIndex,leave])

theorem project_bound (artifact : Artifact) (index provider : Nat) (v : View)
    (found : project artifact index provider = some v) : Bound artifact index provider v := by
  unfold project at found
  simp only [bind,Option.bind] at found
  repeat (split at found <;> (try dsimp only at found) <;> (try contradiction))
  all_goals repeat (split at found <;> (try dsimp only at found) <;> (try contradiction))
  all_goals
    cases Option.some.inj found
    simp_all [Bound]
  refine ⟨_,_,⟨rfl,rfl⟩,?_⟩
  apply Array.ext
  · simp_all
  · intro i hi hj
    have choices : i = 0 ∨ i = 1 ∨ i = 2 := by change i < 3 at hj; omega
    rcases choices with rfl | rfl | rfl <;> simp_all


def sized (n : Nat) (d : Definition) : Bool :=
  decide (d.effect = Effect.unitary) && NodeTyping.quantumOnly d.interface &&
    (wires d.interface.inputs).size == n && (wires d.interface.outputs).size == n

def coreMatches (request : Request) (v : View) : Bool :=
  if v.coreIndex == request.provider then request.exponent == 0
  else match v.core.body with
    | .repeatOp count provider => count == 2^request.exponent && provider == request.provider
    | _ => false

def shape (request : Request) (v : View) : Bool :=
  v.root.interface == request.interface && sized (request.width+1) v.root &&
    sized request.width v.child && sized request.width v.core &&
    sized request.width v.provider && coreMatches request v

def scan (request : Request) (v : View) : Nat :=
  64 + request.interface.scan + v.root.interface.scan + v.child.interface.scan +
    v.core.interface.scan + v.provider.interface.scan

def charge (request : Request) (v : View) : Nat :=
  scan request v + 8 * (request.interface.charge + v.root.interface.charge +
    v.child.interface.charge + v.core.interface.charge + v.provider.interface.charge)

def identityRoutes (width : Nat) (v : View) (cache : Wiring.Cache) : Bool :=
  v.routes.all (fun index => (cache[index]?).bind id == some (List.range width))

structure Pending where
  view : View
  wiring : Wiring.State
  visits : Nat
  deriving Repr

/-- All fresh routing work shares the caller's remaining structural allowance.
No repeat is expanded. The provider's contents are not accepted by this entry. -/
def inspect (artifact : Artifact) (index : Nat) (request : Request)
    (wiringOrder : Array Nat) (remaining : Nat) : Except Error Pending :=
  if remaining > 2000000 || request.width = 0 || request.width > 8 ||
      request.exponent > 12 || !u32 request.provider then .error .limit else
  match project artifact index request.provider with
  | none => .error .contract
  | some view =>
    if scan request view > remaining then .error .limit else
    let cost := charge request view
    if cost > remaining then .error .limit else
    if !shape request view then .error .contract else
    match Wiring.inspect artifact wiringOrder (remaining-cost) with
    | .error error => .error error
    | .ok wiring =>
      if !identityRoutes request.width view wiring.cache then .error .contract else
      .ok ⟨view,wiring,cost+wiring.visits⟩

theorem sized_fields (n : Nat) (d : Definition) (accepted : sized n d = true) :
    d.effect = Effect.unitary ∧ NodeTyping.quantumOnly d.interface = true ∧
      (wires d.interface.inputs).size = n ∧ (wires d.interface.outputs).size = n := by
  simpa only [sized,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq,and_assoc] using accepted

theorem shape_fields (request : Request) (v : View) (accepted : shape request v = true) :
    v.root.interface = request.interface ∧ sized (request.width+1) v.root = true ∧
      sized request.width v.child = true ∧ sized request.width v.core = true ∧
      sized request.width v.provider = true ∧ coreMatches request v = true := by
  simpa only [shape,Bool.and_eq_true,beq_iff_eq,and_assoc] using accepted

theorem coreMatches_cases (request : Request) (v : View)
    (accepted : coreMatches request v = true) :
    (v.coreIndex = request.provider ∧ request.exponent = 0) ∨
      v.core.body = .repeatOp (2^request.exponent) request.provider := by
  unfold coreMatches at accepted
  split at accepted
  next direct => exact Or.inl ⟨by simpa using direct,by simpa using accepted⟩
  next repeated =>
    split at accepted
    next count provider body =>
      simp only [Bool.and_eq_true,beq_iff_eq] at accepted
      exact Or.inr (by simpa only [accepted.1,accepted.2] using body)
    next impossible => contradiction

theorem inspect_conditions (artifact : Artifact) (index : Nat) (request : Request)
    (order : Array Nat) (remaining : Nat) (pending : Pending)
    (accepted : inspect artifact index request order remaining = .ok pending) :
    Bound artifact index request.provider pending.view ∧ shape request pending.view = true ∧
      Wiring.inspect artifact order (remaining-charge request pending.view) = .ok pending.wiring ∧
      identityRoutes request.width pending.view pending.wiring.cache = true ∧
      pending.visits = charge request pending.view + pending.wiring.visits ∧
      pending.visits ≤ remaining ∧ remaining ≤ 2000000 := by
  unfold inspect at accepted
  split at accepted
  next invalid => contradiction
  next bounded =>
    split at accepted
    next absent => contradiction
    next view found =>
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
            split at accepted
            next error => contradiction
            next wiring checked =>
              split at accepted
              next invalid => contradiction
              next routes =>
                cases Except.ok.inj accepted
                have budget := (Wiring.inspect_sound artifact order _ wiring checked).2.1
                simp only [Bool.or_eq_true,decide_eq_true_eq,not_or] at bounded
                exact ⟨project_bound artifact index request.provider view found,by simpa using valid,
                  checked,by simpa using routes,rfl,by dsimp only; omega,by omega⟩

end QleisliKernel.Hierarchical.RoutedPower
