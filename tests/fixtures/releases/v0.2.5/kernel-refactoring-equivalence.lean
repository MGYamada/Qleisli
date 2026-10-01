import QleisliKernel

/-! Universal equality with the literal pre-refactor conditional-checker bodies.
The reference expressions are from source 7bfcd36916199b05d5ab11851d38d53375ccf71e.
Equality covers rejection, remaining charges, complete states and request order,
including malformed inputs; no finite payload is assumed semantically valid.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

namespace QleisliKernel.Hierarchical.RefactoringBaseline
open Artifact Conditional

def localCheck (artifact : Artifact) (index remaining : Nat) : Except Error Local :=
  match artifact.proofs[index]? with
  | none => .error .invalidIr
  | some proof =>
    if proof.rule == .finite then
      match Finite.inspect artifact index remaining with
      | .error error => .error error
      | .ok pending => .ok (.finite pending)
    else
      match Rule.check artifact index remaining with
      | .error error => .error error
      | .ok checked => .ok (.ordinary checked)

def typedLocalCheck (artifact : Artifact) (_context : TypedRule.Context artifact) (index remaining : Nat) : Except Error Local :=
  match artifact.proofs[index]? with
  | none => .error .invalidIr
  | some proof =>
    if proof.rule == .finite then
      match Finite.inspect artifact index remaining with
      | .error error => .error error
      | .ok pending => .ok (.finite pending)
    else
      match TypedRule.check artifact index remaining with
      | .error error => .error error
      | .ok checked => .ok (.ordinary checked)

def step (artifact : Artifact) (state : Conditional.State) (index : Nat) : Except Failure Conditional.State :=
  if state.cache[index]? != some false then .error ⟨.invalidIr,some ⟨.proof,index⟩⟩ else
  match artifact.proofs[index]? with
  | none => .error ⟨.invalidIr,some ⟨.proof,index⟩⟩
  | some proof =>
    let used := state.visits + 4 + 4 * proof.premises.size
    if used > 2000000 then .error ⟨.limit,some ⟨.proof,index⟩⟩ else
    if !(proof.premises.all (fun child => state.cache[child]? == some true)) then
      .error ⟨.contract,some ⟨.proof,index⟩⟩
    else match localCheck artifact index (2000000 - used) with
      | .error error => .error ⟨error,some ⟨.proof,index⟩⟩
      | .ok checked =>
        let total := used + checked.visits
        if total > 2000000 then .error ⟨.limit,some ⟨.proof,index⟩⟩
        else .ok ⟨state.cache.setIfInBounds index true,state.requests ++ checked.requests,
          total,state.proofs+1⟩

def typedStep (artifact : Artifact) (context : TypedRule.Context artifact) (state : Conditional.State) (index : Nat) : Except Failure Conditional.State :=
  if state.cache[index]? != some false then .error ⟨.invalidIr,some ⟨.proof,index⟩⟩ else
  match artifact.proofs[index]? with
  | none => .error ⟨.invalidIr,some ⟨.proof,index⟩⟩
  | some proof =>
    let used := state.visits + 4 + 4 * proof.premises.size
    if used > 2000000 then .error ⟨.limit,some ⟨.proof,index⟩⟩ else
    if !(proof.premises.all (fun child => state.cache[child]? == some true)) then
      .error ⟨.contract,some ⟨.proof,index⟩⟩
    else match typedLocalCheck artifact context index (2000000 - used) with
      | .error error => .error ⟨error,some ⟨.proof,index⟩⟩
      | .ok checked =>
        let total := used + checked.visits
        if total > 2000000 then .error ⟨.limit,some ⟨.proof,index⟩⟩
        else .ok ⟨state.cache.setIfInBounds index true,state.requests ++ checked.requests,
          total,state.proofs+1⟩

def scan (artifact : Artifact) (order : List Nat) (state : Conditional.State) : Except Failure Conditional.State :=
  order.foldlM (step artifact) state

def typedScan (artifact : Artifact) (context : TypedRule.Context artifact) (order : List Nat) (state : Conditional.State) : Except Failure Conditional.State :=
  order.foldlM (typedStep artifact context) state

def checkAll (artifact : Artifact) (order : Array Nat) : Except Failure Pending :=
  match typing : ContractTyping.checkAll artifact order with
  | .error failure => .error failure
  | .ok typed =>
    let start := typed.totalVisits + 6 * (order.size + artifact.proofs.size)
    if start > 2000000 then .error ⟨.limit,none⟩ else
    match typedScan artifact (TypedRule.context_of_checkAll artifact order typed typing)
        (Derivation.proofOrder artifact order)
        ⟨Array.replicate artifact.proofs.size false,#[],start,0⟩ with
    | .error failure => .error failure
    | .ok state =>
      if state.visits > 2000000 then .error ⟨.limit,none⟩ else
      if !state.cache.all id || state.cache[artifact.entry.proof]? != some true then
        .error ⟨.contract,some ⟨.proof,artifact.entry.proof⟩⟩
      else .ok ⟨typed,state⟩

theorem localCheck_unchanged : localCheck = Conditional.localCheck := rfl
theorem typedLocalCheck_unchanged : typedLocalCheck = Conditional.typedLocalCheck := rfl
theorem step_unchanged : step = Conditional.step := rfl
theorem typedStep_unchanged : typedStep = Conditional.typedStep := rfl
theorem scan_unchanged : scan = Conditional.scan := rfl
theorem typedScan_unchanged : typedScan = Conditional.typedScan := rfl
theorem checkAll_unchanged : checkAll = Conditional.checkAll := rfl

end QleisliKernel.Hierarchical.RefactoringBaseline

-- Legacy generated rewrite/congruence names also remain usable.
#check QleisliKernel.Hierarchical.Conditional.scan.eq_1
#check QleisliKernel.Hierarchical.Conditional.typedScan.eq_1
#check QleisliKernel.Hierarchical.Conditional.typedLocalCheck.congr_simp
#check QleisliKernel.Hierarchical.Conditional.typedStep.congr_simp

-- Shared names retain every numerical capacity and equality-field charge.
example : QleisliKernel.Hierarchical.Limits.maxVisits = 2000000 := rfl
example : QleisliKernel.Hierarchical.Limits.maxNodes = 100000 := rfl
example : QleisliKernel.Hierarchical.Limits.maxReferences = 1000000 := rfl
example : QleisliKernel.Hierarchical.Limits.maxDepth = 256 := rfl
example : QleisliKernel.Hierarchical.Limits.maxPayloadBytes = 16777216 := rfl
example (side : QleisliKernel.Hierarchical.Artifact.Side) :
    QleisliKernel.Hierarchical.Artifact.sideFields side =
      1 + side.quantum.foldl (fun n p => n + 3 + 2*p.basis.size + p.axes.size) 0 +
        side.classical.foldl (fun n p => n + 2 + 2*p.basis.size) 0 := rfl
example : QleisliKernel.Hierarchical.TypedRule.sideFields =
    QleisliKernel.Hierarchical.Artifact.sideFields := rfl

-- CI latency probe: comment-only proof edit; equivalence obligations unchanged.
