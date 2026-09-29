import QleisliKernel.Hierarchical.Rule

/-! Check actual proof dependencies starting with an empty internal cache.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
The theorem establishes closure of the supported derivation language. Complex
interpretation of all rules, finite reconstruction and external acceptance are
separate obligations; this module does not issue a production semantic seal. -/

namespace QleisliKernel.Hierarchical.Derivation
open Artifact

/-- A finite derivation from actual supported rules and actual premise lists.
The local rule predicate does not stand in for its premises. -/
inductive Derives (artifact : Artifact) : Nat → Prop where
  | rule (index : Nat) (proof : Proof)
      (found : artifact.proofs[index]? = some proof)
      (matched : Rule.Matches artifact index)
      (premises : ∀ child ∈ proof.premises.toList, Derives artifact child) :
      Derives artifact index

/-- Semantic interpretations can use this induction principle only after
proving each actual rule sound. It supplies no unproved matrix laws. -/
theorem Derives.induction_on_rules (artifact : Artifact) (property : Nat → Prop)
    (rules : ∀ index proof, artifact.proofs[index]? = some proof → Rule.Matches artifact index →
      (∀ child ∈ proof.premises.toList, property child) → property index)
    (index : Nat) (derivation : Derives artifact index) : property index := by
  induction derivation with
  | rule index proof found matched _ ih => exact rules index proof found matched ih

structure State where
  cache : Array Bool
  visits : Nat
  proofs : Nat := 0
  deriving Repr

def Invariant (artifact : Artifact) (state : State) : Prop :=
  ∀ index, state.cache[index]? = some true → Derives artifact index

def step (artifact : Artifact) (state : State) (index : Nat) : Except Failure State :=
  if state.cache[index]? != some false then .error ⟨.invalidIr,some ⟨.proof,index⟩⟩ else
  match artifact.proofs[index]? with
  | none => .error ⟨.invalidIr,some ⟨.proof,index⟩⟩
  | some proof =>
    let used := state.visits + 4 + 4 * proof.premises.size
    if used > 2000000 then .error ⟨.limit,some ⟨.proof,index⟩⟩ else
    if !(proof.premises.all (fun child => state.cache[child]? == some true)) then
      .error ⟨.contract,some ⟨.proof,index⟩⟩
    else match Rule.check artifact index (2000000 - used) with
      | .error error => .error ⟨error,some ⟨.proof,index⟩⟩
      | .ok checked =>
        let total := used + checked.visits
        if total > 2000000 then .error ⟨.limit,some ⟨.proof,index⟩⟩
        else .ok ⟨state.cache.setIfInBounds index true,total,state.proofs+1⟩

theorem step_conditions (artifact : Artifact) (state next : State) (index : Nat)
    (accepted : step artifact state index = .ok next) :
    state.visits ≤ next.visits ∧ next.visits ≤ 2000000 ∧
    next.cache = state.cache.setIfInBounds index true ∧
    ∃ proof, artifact.proofs[index]? = some proof ∧ Rule.Matches artifact index ∧
      ∀ child ∈ proof.premises.toList, state.cache[child]? = some true := by
  unfold step at accepted
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
          cases hc : Rule.check artifact index (2000000 - (state.visits + 4 + 4 * proof.premises.size)) with
          | error error => simp [hc] at accepted
          | ok checked =>
            simp only [hc] at accepted
            split at accepted
            next exceeded => contradiction
            next bounded =>
              cases Except.ok.inj accepted
              refine ⟨by dsimp only; omega,Nat.le_of_not_gt bounded,rfl,proof,rfl,
                (Rule.check_conditions artifact index _ checked hc).2.2,?_⟩
              have all : proof.premises.all (fun child => state.cache[child]? == some true) = true := by
                simpa using ready
              simpa only [← Array.all_toList,List.all_eq_true,beq_iff_eq] using all

theorem step_invariant (artifact : Artifact) (state next : State) (index : Nat)
    (previous : Invariant artifact state)
    (accepted : step artifact state index = .ok next) : Invariant artifact next := by
  obtain ⟨_,_,cache,proof,found,matched,ready⟩ := step_conditions artifact state next index accepted
  have current : Derives artifact index := .rule index proof found matched (fun child member => previous child (ready child member))
  intro child present
  by_cases same : index = child
  · subst child; exact current
  · rw [cache,Array.getElem?_setIfInBounds_ne same] at present
    exact previous child present

def scan (artifact : Artifact) (order : List Nat) (state : State) : Except Failure State :=
  order.foldlM (step artifact) state

theorem scan_invariant (artifact : Artifact) (order : List Nat) (state final : State)
    (previous : Invariant artifact state)
    (accepted : scan artifact order state = .ok final) : Invariant artifact final := by
  induction order generalizing state with
  | nil =>
    have same : state = final := by simpa [scan,pure,Except.pure] using accepted
    subst final; exact previous
  | cons index rest ih =>
    cases hs : step artifact state index with
    | error error => simp [scan,hs,bind,Except.bind] at accepted
    | ok next =>
      have tail : scan artifact rest next = .ok final := by simpa [scan,hs] using accepted
      exact ih next (step_invariant artifact state next index previous hs) tail

def proofOrder (artifact : Artifact) (order : Array Nat) : List Nat :=
  order.toList.filterMap (fun flat => if offset artifact .proof ≤ flat then some (flat - offset artifact .proof) else none)

structure Checked where
  typed : ContractTyping.Typed
  state : State
  deriving Repr

/-- No cache or receipt is accepted as input. Each actual proof must succeed;
unsupported finite/schema/encoded equations reject instead of being deferred. -/
def checkAll (artifact : Artifact) (order : Array Nat) : Except Failure Checked :=
  match ContractTyping.checkAll artifact order with
  | .error failure => .error failure
  | .ok typed =>
    let start := typed.totalVisits + 6 * (order.size + artifact.proofs.size)
    if start > 2000000 then .error ⟨.limit,none⟩ else
    match scan artifact (proofOrder artifact order) ⟨Array.replicate artifact.proofs.size false,start,0⟩ with
    | .error failure => .error failure
    | .ok state =>
      if state.visits > 2000000 then .error ⟨.limit,none⟩ else
      if !state.cache.all id || state.cache[artifact.entry.proof]? != some true then
        .error ⟨.contract,some ⟨.proof,artifact.entry.proof⟩⟩
      else .ok ⟨typed,state⟩

theorem empty_invariant (artifact : Artifact) (size visits : Nat) :
    Invariant artifact ⟨Array.replicate size false,visits,0⟩ := by
  intro index present
  simp [Array.getElem?_replicate] at present

theorem checkAll_conditions (artifact : Artifact) (order : Array Nat) (checked : Checked)
    (accepted : checkAll artifact order = .ok checked) :
    ContractTyping.checkAll artifact order = .ok checked.typed ∧
    checked.state.visits ≤ 2000000 ∧ Invariant artifact checked.state ∧
    Derives artifact artifact.entry.proof := by
  unfold checkAll at accepted
  cases ht : ContractTyping.checkAll artifact order with
  | error failure => simp [ht] at accepted
  | ok typed =>
    simp only [ht] at accepted
    split at accepted
    next exceeded => contradiction
    next start =>
      cases hs : scan artifact (proofOrder artifact order)
          ⟨Array.replicate artifact.proofs.size false,typed.totalVisits + 6 * (order.size + artifact.proofs.size),0⟩ with
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
            have invariant := scan_invariant artifact (proofOrder artifact order) _ state
              (empty_invariant artifact _ _) hs
            have entry : state.cache[artifact.entry.proof]? = some true := by
              have parts := complete
              simp only [Bool.or_eq_true,Bool.not_eq_true',bne_iff_ne,not_or] at parts
              exact Decidable.byContradiction parts.2
            exact ⟨rfl,Nat.le_of_not_gt bounded,invariant,invariant _ entry⟩

structure PowerChecked where
  derivation : Checked
  projection : Power.Pending
  visits : Nat
  deriving Repr

/-- Require a complete supported derivation as well as the independent power
request. This closes the opaque/false-provider route of projection alone. -/
def powerEntry (artifact : Artifact) (order : Array Nat) (exponent provider : Nat) : Except Failure PowerChecked :=
  match checkAll artifact order with
  | .error failure => .error failure
  | .ok derivation =>
    match Power.inspect artifact artifact.entry.proof exponent provider (2000000 - derivation.state.visits) with
    | .error kind => .error ⟨kind,some ⟨.proof,artifact.entry.proof⟩⟩
    | .ok projection =>
      let total := derivation.state.visits + projection.visits
      if total > 2000000 then .error ⟨.limit,none⟩ else
      if derivation.state.cache[projection.providerProofIndex]? != some true then
        .error ⟨.contract,some ⟨.proof,projection.providerProofIndex⟩⟩
      else .ok ⟨derivation,projection,total⟩

theorem powerEntry_provider (artifact : Artifact) (order : Array Nat) (exponent provider : Nat)
    (checked : PowerChecked)
    (accepted : powerEntry artifact order exponent provider = .ok checked) :
    Derives artifact checked.projection.providerProofIndex ∧ checked.visits ≤ 2000000 ∧
    Power.inspect artifact artifact.entry.proof exponent provider (2000000 - checked.derivation.state.visits) = .ok checked.projection := by
  unfold powerEntry at accepted
  cases hd : checkAll artifact order with
  | error failure => simp [hd] at accepted
  | ok derivation =>
    simp only [hd] at accepted
    cases hp : Power.inspect artifact artifact.entry.proof exponent provider (2000000 - derivation.state.visits) with
    | error failure => simp [hp] at accepted
    | ok projection =>
      simp only [hp] at accepted
      split at accepted
      next exceeded => contradiction
      next bounded =>
        split at accepted
        next missing => contradiction
        next present =>
          cases Except.ok.inj accepted
          have invariant := (checkAll_conditions artifact order derivation hd).2.2.1
          exact ⟨invariant _ (by simpa using present),Nat.le_of_not_gt bounded,hp⟩

end QleisliKernel.Hierarchical.Derivation
