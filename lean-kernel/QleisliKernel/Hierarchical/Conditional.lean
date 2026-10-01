import QleisliKernel.Hierarchical.Finite
import QleisliKernel.Hierarchical.TypedRule
import QleisliKernel.Hierarchical.Derivation

/-! Whole-artifact derivation conditional on every bound finite obligation.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
No finite predicate, success flag or request list is executable input. A pending
result is not evidence until the same requests are independently discharged. -/

namespace QleisliKernel.Hierarchical.Conditional
open Artifact

inductive Derives (artifact : Artifact) (finite : Finite.Request → Prop) : Nat → Prop where
  | finite (index remaining : Nat) (pending : Finite.Pending)
      (inspected : Finite.inspect artifact index remaining = .ok pending)
      (discharged : finite pending.request) : Derives artifact finite index
  | rule (index : Nat) (proof : Proof)
      (found : artifact.proofs[index]? = some proof)
      (matched : Rule.Matches artifact index)
      (premises : ∀ child ∈ proof.premises.toList, Derives artifact finite child) :
      Derives artifact finite index

theorem Derives.induction_on_rules (artifact : Artifact) (finite : Finite.Request → Prop)
    (property : Nat → Prop)
    (leaves : ∀ index remaining pending, Finite.inspect artifact index remaining = .ok pending →
      finite pending.request → property index)
    (rules : ∀ index proof, artifact.proofs[index]? = some proof → Rule.Matches artifact index →
      (∀ child ∈ proof.premises.toList, property child) → property index)
    (index : Nat) (derived : Derives artifact finite index) : property index := by
  induction derived with
  | finite index remaining pending inspected discharged =>
    exact leaves index remaining pending inspected discharged
  | rule index proof found matched _ ih => exact rules index proof found matched ih

inductive Local where
  | ordinary (checked : Rule.Checked)
  | finite (pending : Finite.Pending)
  deriving Repr

def Local.visits : Local → Nat
  | .ordinary checked => checked.visits
  | .finite pending => pending.visits

def Local.requests : Local → Array Finite.Request
  | .ordinary _ => #[]
  | .finite pending => #[pending.request]

def Local.Valid (artifact : Artifact) (index : Nat) : Local → Prop
  | .ordinary _ => Rule.Matches artifact index
  | .finite pending => ∃ remaining, Finite.inspect artifact index remaining = .ok pending

private def localCheckWith (artifact : Artifact)
    (ordinary : Nat → Nat → Except Error Rule.Checked) (index remaining : Nat) : Except Error Local :=
  match artifact.proofs[index]? with
  | none => .error .invalidIr
  | some proof =>
    if proof.rule == .finite then
      match Finite.inspect artifact index remaining with
      | .error error => .error error
      | .ok pending => .ok (.finite pending)
    else
      match ordinary index remaining with
      | .error error => .error error
      | .ok checked => .ok (.ordinary checked)

private theorem localCheckWith_conditions (artifact : Artifact)
    (ordinary : Nat → Nat → Except Error Rule.Checked)
    (sound : ∀ index remaining checked, ordinary index remaining = .ok checked →
      checked.visits ≤ remaining ∧ remaining ≤ 2000000 ∧ Rule.Matches artifact index)
    (index remaining : Nat) (checked : Local)
    (accepted : localCheckWith artifact ordinary index remaining = .ok checked) :
    checked.visits ≤ remaining ∧ remaining ≤ 2000000 ∧ checked.Valid artifact index := by
  unfold localCheckWith at accepted
  split at accepted
  next absent => contradiction
  next proof hp =>
    split at accepted
    next finite =>
      split at accepted
      next error failed => contradiction
      next pending inspected =>
        cases Except.ok.inj accepted
        have h := Finite.inspect_conditions artifact index remaining pending inspected
        exact ⟨h.1,h.2.1,remaining,inspected⟩
    next ordinary =>
      split at accepted
      next error failed => contradiction
      next result checked =>
        cases Except.ok.inj accepted
        exact sound index remaining result checked

/-- Both paths inspect identical finite leaves; only ordinary-rule checking differs. -/
def localCheck (artifact : Artifact) (index remaining : Nat) : Except Error Local :=
  localCheckWith artifact (Rule.check artifact) index remaining

theorem localCheck_conditions (artifact : Artifact) (index remaining : Nat) (checked : Local)
    (accepted : localCheck artifact index remaining = .ok checked) :
    checked.visits ≤ remaining ∧ remaining ≤ 2000000 ∧ checked.Valid artifact index :=
  localCheckWith_conditions artifact (Rule.check artifact)
    (Rule.check_conditions artifact) index remaining checked accepted

def typedLocalCheck (artifact : Artifact) (_context : TypedRule.Context artifact) (index remaining : Nat) : Except Error Local :=
  localCheckWith artifact (TypedRule.check artifact) index remaining

-- Simplification also retains the existing generated congruence declaration.
theorem typedLocalCheck_conditions (artifact : Artifact) (context : TypedRule.Context artifact) (index remaining : Nat) (checked : Local)
    (accepted : typedLocalCheck artifact context index remaining = .ok checked) :
    checked.visits ≤ remaining ∧ remaining ≤ 2000000 ∧ checked.Valid artifact index :=
  localCheckWith_conditions artifact (TypedRule.check artifact)
    (TypedRule.check_conditions artifact context) index remaining checked (by simpa only [typedLocalCheck] using accepted)

structure State where
  cache : Array Bool
  requests : Array Finite.Request
  visits : Nat
  proofs : Nat := 0
  deriving Repr

/-- This premise is universal over the remaining leaf predicate. It does not
silently choose `True` or treat an opaque payload as a unitary operation. -/
def Invariant (artifact : Artifact) (state : State) : Prop :=
  ∀ finite : Finite.Request → Prop,
    (∀ request ∈ state.requests.toList, finite request) →
    ∀ index, state.cache[index]? = some true → Derives artifact finite index

def RequestsBound (artifact : Artifact) (requests : Array Finite.Request) : Prop :=
  ∀ request ∈ requests.toList, ∃ remaining pending,
    Finite.inspect artifact request.index remaining = .ok pending ∧ pending.request = request

private def stepWith (artifact : Artifact)
    (checker : Nat → Nat → Except Error Local) (state : State) (index : Nat) : Except Failure State :=
  if state.cache[index]? != some false then .error ⟨.invalidIr,some ⟨.proof,index⟩⟩ else
  match artifact.proofs[index]? with
  | none => .error ⟨.invalidIr,some ⟨.proof,index⟩⟩
  | some proof =>
    let used := state.visits + 4 + 4 * proof.premises.size
    if used > Limits.maxVisits then .error ⟨.limit,some ⟨.proof,index⟩⟩ else
    if !(proof.premises.all (fun child => state.cache[child]? == some true)) then
      .error ⟨.contract,some ⟨.proof,index⟩⟩
    else match checker index (Limits.maxVisits - used) with
      | .error error => .error ⟨error,some ⟨.proof,index⟩⟩
      | .ok checked =>
        let total := used + checked.visits
        if total > Limits.maxVisits then .error ⟨.limit,some ⟨.proof,index⟩⟩
        else .ok ⟨state.cache.setIfInBounds index true,state.requests ++ checked.requests,
          total,state.proofs+1⟩

/-- Internal successful-step facts have names; legacy public conclusions retain
exactly their original conjunction types. These are proofs, never wire input. -/
private structure StepFacts (artifact : Artifact)
    (state next : State) (index : Nat) : Prop where
  monotone : state.visits ≤ next.visits
  bounded : next.visits ≤ 2000000
  cache : next.cache = state.cache.setIfInBounds index true
  checked : ∃ (proof : Proof) (checked : Local), artifact.proofs[index]? = some proof ∧
    checked.Valid artifact index ∧ next.requests = state.requests ++ checked.requests ∧
    ∀ child ∈ proof.premises.toList, state.cache[child]? = some true

private theorem StepFacts.conditions {artifact : Artifact} {state next : State} {index : Nat}
    (facts : StepFacts artifact state next index) :
    state.visits ≤ next.visits ∧ next.visits ≤ 2000000 ∧
    next.cache = state.cache.setIfInBounds index true ∧
    ∃ (proof : Proof) (checked : Local), artifact.proofs[index]? = some proof ∧ checked.Valid artifact index ∧
      next.requests = state.requests ++ checked.requests ∧
      ∀ child ∈ proof.premises.toList, state.cache[child]? = some true :=
  ⟨facts.monotone,facts.bounded,facts.cache,facts.checked⟩

private theorem stepWith_conditions (artifact : Artifact)
    (checker : Nat → Nat → Except Error Local)
    (sound : ∀ index remaining checked, checker index remaining = .ok checked →
      checked.visits ≤ remaining ∧ remaining ≤ 2000000 ∧ checked.Valid artifact index) (state next : State) (index : Nat)
    (accepted : stepWith artifact checker state index = .ok next) :
    StepFacts artifact state next index := by
  unfold stepWith at accepted
  split at accepted
  next duplicate => contradiction
  next fresh =>
    cases hp : artifact.proofs[index]? with
    | none => simp [hp] at accepted
    | some proof =>
      simp only [hp] at accepted
      split at accepted
      next exceeded => contradiction
      next scanned =>
        split at accepted
        next missing => contradiction
        next ready =>
          cases hc : checker index (2000000 - (state.visits + 4 + 4 * proof.premises.size)) with
          | error error => simp [hc] at accepted
          | ok checked =>
            simp only [hc] at accepted
            split at accepted
            next exceeded => contradiction
            next bounded =>
              cases Except.ok.inj accepted
              refine ⟨by dsimp only; omega,Nat.le_of_not_gt bounded,rfl,proof,checked,hp,
                (sound index _ checked hc).2.2,rfl,?_⟩
              have all : proof.premises.all (fun child => state.cache[child]? == some true) = true := by
                simpa using ready
              simpa only [← Array.all_toList,List.all_eq_true,beq_iff_eq] using all

def step (artifact : Artifact) (state : State) (index : Nat) : Except Failure State :=
  stepWith artifact (localCheck artifact) state index

theorem step_conditions (artifact : Artifact) (state next : State) (index : Nat)
    (accepted : step artifact state index = .ok next) :
    state.visits ≤ next.visits ∧ next.visits ≤ 2000000 ∧
    next.cache = state.cache.setIfInBounds index true ∧
    ∃ (proof : Proof) (checked : Local), artifact.proofs[index]? = some proof ∧ checked.Valid artifact index ∧
      next.requests = state.requests ++ checked.requests ∧
      ∀ child ∈ proof.premises.toList, state.cache[child]? = some true :=
  (stepWith_conditions artifact (localCheck artifact)
    (localCheck_conditions artifact) state next index accepted).conditions

def typedStep (artifact : Artifact) (context : TypedRule.Context artifact) (state : State) (index : Nat) : Except Failure State :=
  stepWith artifact (typedLocalCheck artifact context) state index

theorem typedStep_conditions (artifact : Artifact) (context : TypedRule.Context artifact) (state next : State) (index : Nat)
    (accepted : typedStep artifact context state index = .ok next) :
    state.visits ≤ next.visits ∧ next.visits ≤ 2000000 ∧
    next.cache = state.cache.setIfInBounds index true ∧
    ∃ (proof : Proof) (checked : Local), artifact.proofs[index]? = some proof ∧ checked.Valid artifact index ∧
      next.requests = state.requests ++ checked.requests ∧
      ∀ child ∈ proof.premises.toList, state.cache[child]? = some true :=
  (stepWith_conditions artifact (typedLocalCheck artifact context)
    (typedLocalCheck_conditions artifact context) state next index (by simpa only [typedStep] using accepted)).conditions

private theorem preserve_invariant (artifact : Artifact) (state next : State) (index : Nat)
    (previous : Invariant artifact state)
    (facts : StepFacts artifact state next index) : Invariant artifact next := by
  obtain ⟨proof,checked,found,valid,requests,ready⟩ := facts.checked
  intro finite discharged
  have old : ∀ request ∈ state.requests.toList, finite request := by
    intro request member
    apply discharged request
    simp [requests,member]
  have current : Derives artifact finite index := by
    cases checked with
    | ordinary result => exact .rule index proof found valid (fun child member => previous finite old child (ready child member))
    | finite pending =>
      obtain ⟨remaining,inspected⟩ := valid
      apply Derives.finite index remaining pending inspected
      apply discharged pending.request
      simp [requests,Local.requests]
  intro child present
  by_cases same : index = child
  · subst child; exact current
  · rw [facts.cache,Array.getElem?_setIfInBounds_ne same] at present
    exact previous finite old child present

theorem step_invariant (artifact : Artifact) (state next : State) (index : Nat)
    (previous : Invariant artifact state)
    (accepted : step artifact state index = .ok next) : Invariant artifact next :=
  preserve_invariant artifact state next index previous
    (stepWith_conditions artifact (localCheck artifact)
      (localCheck_conditions artifact) state next index accepted)

theorem typedStep_invariant (artifact : Artifact) (context : TypedRule.Context artifact) (state next : State) (index : Nat)
    (previous : Invariant artifact state)
    (accepted : typedStep artifact context state index = .ok next) : Invariant artifact next :=
  preserve_invariant artifact state next index previous
    (stepWith_conditions artifact (typedLocalCheck artifact context)
      (typedLocalCheck_conditions artifact context) state next index accepted)

private theorem preserve_requests (artifact : Artifact) (state next : State) (index : Nat)
    (previous : RequestsBound artifact state.requests)
    (facts : StepFacts artifact state next index) : RequestsBound artifact next.requests := by
  obtain ⟨_,checked,_,valid,requests,_⟩ := facts.checked
  intro request member
  rw [requests,Array.toList_append] at member
  rcases List.mem_append.mp member with old | added
  · exact previous request old
  · cases checked with
    | ordinary result => simp [Local.requests] at added
    | finite pending =>
      have same : pending.request = request := by simpa [Local.requests,eq_comm] using added
      subst request
      obtain ⟨remaining,inspected⟩ := valid
      obtain ⟨_,_,_,bound,_,_⟩ := Finite.inspect_conditions artifact index remaining pending inspected
      exact ⟨remaining,pending,by simpa only [bound.1] using inspected,rfl⟩

theorem step_requests (artifact : Artifact) (state next : State) (index : Nat)
    (previous : RequestsBound artifact state.requests)
    (accepted : step artifact state index = .ok next) : RequestsBound artifact next.requests :=
  preserve_requests artifact state next index previous
    (stepWith_conditions artifact (localCheck artifact)
      (localCheck_conditions artifact) state next index accepted)

theorem typedStep_requests (artifact : Artifact) (context : TypedRule.Context artifact) (state next : State) (index : Nat)
    (previous : RequestsBound artifact state.requests)
    (accepted : typedStep artifact context state index = .ok next) : RequestsBound artifact next.requests :=
  preserve_requests artifact state next index previous
    (stepWith_conditions artifact (typedLocalCheck artifact context)
      (typedLocalCheck_conditions artifact context) state next index accepted)

def scan (artifact : Artifact) (order : List Nat) (state : State) : Except Failure State :=
  order.foldlM (step artifact) state

def typedScan (artifact : Artifact) (context : TypedRule.Context artifact) (order : List Nat) (state : State) : Except Failure State :=
  order.foldlM (typedStep artifact context) state

private theorem fold_invariants (artifact : Artifact)
    (transition : State → Nat → Except Failure State)
    (preserveInvariant : ∀ state next index, Invariant artifact state →
      transition state index = .ok next → Invariant artifact next)
    (preserveRequests : ∀ state next index, RequestsBound artifact state.requests →
      transition state index = .ok next → RequestsBound artifact next.requests)
    (order : List Nat) (state final : State)
    (previous : Invariant artifact state) (bound : RequestsBound artifact state.requests)
    (accepted : order.foldlM transition state = .ok final) :
    Invariant artifact final ∧ RequestsBound artifact final.requests := by
  induction order generalizing state with
  | nil =>
    have same : state = final := by simpa [List.foldlM,pure,Except.pure] using accepted
    subst final; exact ⟨previous,bound⟩
  | cons index rest ih =>
    cases hs : transition state index with
    | error error => simp [List.foldlM,hs,bind,Except.bind] at accepted
    | ok next =>
      have tail : rest.foldlM transition next = .ok final := by simpa [List.foldlM,hs] using accepted
      exact ih next (preserveInvariant state next index previous hs)
        (preserveRequests state next index bound hs) tail

-- Keep the legacy generated `scan.eq_1` rewrite lemma available to clients.
theorem scan_invariants (artifact : Artifact) (order : List Nat) (state final : State)
    (previous : Invariant artifact state) (bound : RequestsBound artifact state.requests)
    (accepted : scan artifact order state = .ok final) :
    Invariant artifact final ∧ RequestsBound artifact final.requests :=
  fold_invariants artifact (step artifact) (step_invariant artifact)
    (step_requests artifact) order state final previous bound (by simpa only [scan] using accepted)

theorem typedScan_invariants (artifact : Artifact) (context : TypedRule.Context artifact) (order : List Nat) (state final : State)
    (previous : Invariant artifact state) (bound : RequestsBound artifact state.requests)
    (accepted : typedScan artifact context order state = .ok final) :
    Invariant artifact final ∧ RequestsBound artifact final.requests :=
  fold_invariants artifact (typedStep artifact context) (typedStep_invariant artifact context)
    (typedStep_requests artifact context) order state final previous bound (by simpa only [typedScan] using accepted)

structure Pending where
  typed : ContractTyping.Typed
  state : State
  deriving Repr

/-- Start from empty state and retain every finite obligation. This successor
entry checks the supported composition structure, not opaque leaf semantics. -/
def checkAll (artifact : Artifact) (order : Array Nat) : Except Failure Pending :=
  match typing : ContractTyping.checkAll artifact order with
  | .error failure => .error failure
  | .ok typed =>
    let start := typed.totalVisits + 6 * (order.size + artifact.proofs.size)
    if start > Limits.maxVisits then .error ⟨.limit,none⟩ else
    match typedScan artifact (TypedRule.context_of_checkAll artifact order typed typing)
        (Derivation.proofOrder artifact order)
        ⟨Array.replicate artifact.proofs.size false,#[],start,0⟩ with
    | .error failure => .error failure
    | .ok state =>
      if state.visits > Limits.maxVisits then .error ⟨.limit,none⟩ else
      if !state.cache.all id || state.cache[artifact.entry.proof]? != some true then
        .error ⟨.contract,some ⟨.proof,artifact.entry.proof⟩⟩
      else .ok ⟨typed,state⟩

theorem empty_invariant (artifact : Artifact) (size visits : Nat) :
    Invariant artifact ⟨Array.replicate size false,#[],visits,0⟩ := by
  intro finite discharged index present
  simp [Array.getElem?_replicate] at present

theorem checkAll_conditions (artifact : Artifact) (order : Array Nat) (pending : Pending)
    (accepted : checkAll artifact order = .ok pending) :
    ContractTyping.checkAll artifact order = .ok pending.typed ∧
    pending.state.visits ≤ 2000000 ∧ Invariant artifact pending.state ∧
    RequestsBound artifact pending.state.requests ∧
    ∀ finite : Finite.Request → Prop,
      (∀ request ∈ pending.state.requests.toList, finite request) →
      Derives artifact finite artifact.entry.proof := by
  unfold checkAll at accepted
  split at accepted
  next failure ht => contradiction
  next typed ht =>
    dsimp only at accepted
    split at accepted
    next exceeded => contradiction
    next start =>
      let context := TypedRule.context_of_checkAll artifact order typed ht
      cases hs : typedScan artifact context (Derivation.proofOrder artifact order)
          ⟨Array.replicate artifact.proofs.size false,#[],typed.totalVisits + 6 * (order.size + artifact.proofs.size),0⟩ with
      | error failure => simp [hs] at accepted
      | ok state =>
        simp only [hs] at accepted
        split at accepted
        next exceeded => contradiction
        next bounded =>
          split at accepted
          next unfinished => contradiction
          next complete =>
            cases Except.ok.inj accepted
            have invariants := typedScan_invariants artifact context (Derivation.proofOrder artifact order) _ state
              (empty_invariant artifact _ _) (by intro request member; simp at member) hs
            have entry : state.cache[artifact.entry.proof]? = some true := by
              have parts := complete
              simp only [Bool.or_eq_true,Bool.not_eq_true',bne_iff_ne,not_or] at parts
              exact Decidable.byContradiction parts.2
            exact ⟨ht,Nat.le_of_not_gt bounded,invariants.1,invariants.2,
              fun finite discharged => invariants.1 finite discharged _ entry⟩

end QleisliKernel.Hierarchical.Conditional
