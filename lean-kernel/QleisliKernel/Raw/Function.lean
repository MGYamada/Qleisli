import QleisliKernel.Raw.ProtectedEvaluation
import QleisliKernel.Semantics.Function

/-! Fresh reconstruction and binding of complete original function attachments.
The finite function profile follows the published capacities; general raw
structural checking retains twelve-bit owners. Source attachments are identity
data, not a claim of source-to-IR preservation.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Raw.Function
open Semantics.Exact Semantics.Finite Semantics.Raw Semantics.Function Finite

def identityBytes (identity : Identity) : Nat :=
  identity.implementation.utf8ByteSize + identity.specification.utf8ByteSize +
    (identity.sources.map fun (name,source) => name.utf8ByteSize + source.utf8ByteSize).sum

def identityValid (identity : Identity) : Bool :=
  !identity.implementation.isEmpty && !identity.specification.isEmpty &&
    identity.implementation.utf8ByteSize ≤ 4096 && identity.specification.utf8ByteSize ≤ 4096 &&
    identity.sources.length ≤ 128 && (identity.sources.map Prod.fst).eraseDups.length == identity.sources.length &&
    identity.sources.all (fun entry => entry.1.utf8ByteSize ≤ 4096) && identityBytes identity ≤ 1048576

def stepBounded (step : Step) : Bool :=
  step.controls.length ≤ 6 && match step.action with
    | .monomial axes permutation phases => axes.length ≤ 6 && permutation.length ≤ 64 && phases.length ≤ 64
    | .contract axes _ _ => axes.length ≤ 6
    | _ => true

def operationBounded : Op → Bool
  | .init0 _ _ => false
  | .applyUnitary _ _ steps => steps.length ≤ 1024 && steps.all stepBounded
  | .certifiedCompute _ _ ancilla function uses logical =>
    ancilla.length ≤ 6 && function.length ≤ 64 && uses.length ≤ 1024 && logical.length ≤ 1024 &&
      (uses ++ logical).all stepBounded
  | .quantumIf _ _ _ _ zero one => zero.length + one.length ≤ 1024
  | .liftBasis _ _ wires table => wires.length ≤ 6 && table.length ≤ 64
  | .computeUseUncompute _ _ targets ancilla function uses =>
    targets.length ≤ 6 && ancilla.length ≤ 6 && function.length ≤ 64 && uses.length ≤ 1024 &&
      uses.all (fun use => match use with
        | .protectedGate _ _ => true
        | .targetGate controls _ _ | .phase controls _ => controls.length ≤ 12)
  | _ => true

def suppliedSteps : Op → List Step
  | .applyUnitary _ _ steps => steps
  | .certifiedCompute _ _ _ _ uses logical => uses ++ logical
  | _ => []

def preflight (signature : Basis) (program : Program) : Bool :=
  unary signature program && program.operations.length ≤ 1024 && program.operations.all operationBounded &&
    (program.operations.map (fun op => (suppliedSteps op).length + match op with
      | .quantumIf _ _ _ _ zero one => zero.length + one.length | _ => 0)).sum ≤ 1024

/-- Count dependency expansion without recursively constructing an expanded DAG.
The original event extraction remains independently defined in Semantics. -/
def countStep (dependencies : List Nat) (count : Nat) (step : Step) : WorkM Nat := do
  let cost ← lift (readOption (stepCost dependencies step))
  let next := count + cost
  guard (next ≤ 1000000) .limit
  return next

def countEvent (dependencies : List Nat) (counts : Nat × Nat) (event : Event) : WorkM (Nat × Nat) := do
  let steps ← lift (readOption (Semantics.Function.extracted event))
  let raw := counts.1 + steps.length
  guard (raw ≤ 1024) .limit
  let expanded ← steps.foldlM (countStep dependencies) counts.2
  return (raw,expanded)

def boundedExpansion (dependencies : List Nat) (events : List Event) : WorkM Nat := do
  let result ← events.foldlM (countEvent dependencies) (0,0)
  guard (result.1 ≤ 1024 && result.2 ≤ 1000000) .limit
  return max result.2 1

private theorem readOption_reference {α : Type} (value : Option α) (result : α)
    (ok : readOption value = .ok result) : value = some result := by
  cases value <;> simp_all [readOption]

theorem countStep_reference (dependencies : List Nat) (count result : Nat) (step : Step)
    (work left : Nat) (ok : (countStep dependencies count step).run work = (.ok result,left)) :
    Semantics.Function.countStep dependencies count step = some result := by
  obtain ⟨cost,w₁,hc,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,_,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst result
  simp [Semantics.Function.countStep,readOption_reference _ _ (lift_success _ _ _ _ hc).1]

private theorem fold_reference {α β : Type} (checked : α → β → WorkM α) (reference : α → β → Option α)
    (localSound : ∀ a b result work left,
      (checked a b).run work = (.ok result,left) → reference a b = some result)
    (items : List β) (initial result : α) (work left : Nat)
    (ok : (items.foldlM checked initial).run work = (.ok result,left)) :
    items.foldlM reference initial = some result := by
  induction items generalizing initial work with
  | nil =>
    simp only [List.foldlM_nil] at ok
    rw [(pure_success _ _ _ _ ok).1]
    rfl
  | cons item items ih =>
    simp only [List.foldlM_cons] at ok
    obtain ⟨next,middle,hn,hr⟩ := bind_success _ _ _ _ _ ok
    simp [List.foldlM_cons,localSound initial item next work middle hn,ih next middle hr]

theorem countEvent_reference (dependencies : List Nat) (counts result : Nat × Nat) (event : Event)
    (work left : Nat) (ok : (countEvent dependencies counts event).run work = (.ok result,left)) :
    Semantics.Function.countEvent dependencies counts event = some result := by
  obtain ⟨steps,w₁,hs,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨expanded,w₃,he,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst result
  have extracted := readOption_reference _ _ (lift_success _ _ _ _ hs).1
  have counted := fold_reference _ _ (fun a b result work left ok =>
    countStep_reference dependencies a result b work left ok) _ _ _ _ _ he
  simp [Semantics.Function.countEvent,extracted,counted]

theorem boundedExpansion_reference (dependencies : List Nat) (events : List Event) (result work left : Nat)
    (ok : (boundedExpansion dependencies events).run work = (.ok result,left)) :
    Semantics.Function.expansion dependencies events = some result ∧ result ≤ 1000000 := by
  obtain ⟨counts,w₁,hc,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,hg,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst result
  have counted := fold_reference _ _ (fun a b result work left ok =>
    countEvent_reference dependencies a result b work left ok) _ _ _ _ _ hc
  have limits := (guard_success _ _ _ _ hg).1
  simp only [Bool.and_eq_true,decide_eq_true_eq] at limits
  exact ⟨by simp [Semantics.Function.expansion,counted],Nat.max_le.mpr ⟨limits.2,by decide⟩⟩

def depth (previous : List Receipt) (input : Input) : Nat :=
  1 + ((programReferences input.body.implementation ++ programReferences input.body.specification).map
    (fun index => (previous[index]?.map (·.depth)).getD 0)).foldl max 0

def checkEntry (previous : List Receipt) (input : Input) (required : Binding) : WorkM Receipt := do
  guard (input == required) .request
  guard (identityValid input.identity) .limit
  exactWork (Exact.charge (identityBytes input.identity))
  guard (preflight input.body.signature input.body.implementation && preflight input.body.signature input.body.specification) .limit
  let height := depth previous input
  guard (height ≤ 32) .limit
  let dependencies := previous.map Receipt.dependency
  let implementation ← lift (prepare (dependencies.map (·.signature)) input.body.implementation)
  let specification ← lift (prepare (dependencies.map (·.signature)) input.body.specification)
  let expanded ← boundedExpansion (previous.map (·.expandedSteps)) implementation.events
  let _ ← boundedExpansion (previous.map (·.expandedSteps)) specification.events
  let actual ← ProtectedEvaluation.reconstruct dependencies input.body.implementation
  let specified ← ProtectedEvaluation.reconstruct dependencies input.body.specification
  guard (actual == specified) .equation
  wholeSpace actual
  return ⟨input,actual,height,expanded⟩

def checkAll (inputs : List Input) (required : List Binding) : WorkM (List Receipt) := do
  guard (inputs.length == required.length && inputs.length ≤ 65536) .limit
  (inputs.zip required).foldlM (fun previous (input,binding) => do
    let checked ← checkEntry previous input binding
    return previous ++ [checked]) []

def inspect (inputs : List Input) (bindings : List Binding) (program : Program) (required : Matrix) : WorkM Matrix := do
  let receipts ← checkAll inputs bindings
  let required ← matrixRead required
  let actual ← ProtectedEvaluation.reconstruct (receipts.map Receipt.dependency) program
  guard (actual == required) .request
  return actual

theorem checkEntry_conditions (previous : List Receipt) (input : Input) (required : Binding)
    (receipt : Receipt) (work left : Nat)
    (ok : (checkEntry previous input required).run work = (.ok receipt,left)) :
    input = required ∧ identityValid input.identity = true ∧
    preflight input.body.signature input.body.implementation = true ∧
    preflight input.body.signature input.body.specification = true ∧
    receipt.input = input ∧ receipt.depth = depth previous input ∧ receipt.depth ≤ 32 ∧
    ∃ implementation specification a b c d e f g h i j,
      prepare ((previous.map Receipt.dependency).map (·.signature)) input.body.implementation = .ok implementation ∧
      prepare ((previous.map Receipt.dependency).map (·.signature)) input.body.specification = .ok specification ∧
      (boundedExpansion (previous.map (·.expandedSteps)) implementation.events).run a = (.ok receipt.expandedSteps,b) ∧
      (boundedExpansion (previous.map (·.expandedSteps)) specification.events).run c = (.ok d,e) ∧
      (ProtectedEvaluation.reconstruct (previous.map Receipt.dependency) input.body.implementation).run f = (.ok receipt.meaning,g) ∧
      (ProtectedEvaluation.reconstruct (previous.map Receipt.dependency) input.body.specification).run h = (.ok receipt.meaning,i) ∧
      (wholeSpace receipt.meaning).run j = (.ok (),left) := by
  obtain ⟨_,w₁,hb,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,hi,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₃,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₄,hp,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₅,hd,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨implementation,w₆,him,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨specification,w₇,hsp,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨expanded,w₈,he,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨specifiedCount,w₉,hse,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨actual,w₁₀,ha,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨specified,w₁₁,hs,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₁₂,hg,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₁₃,hw,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  have leftEq := (pure_success _ _ _ _ h).2
  have eq := beq_iff_eq.mp (guard_success _ _ _ _ hg).1
  have binding := beq_iff_eq.mp (guard_success _ _ _ _ hb).1
  have pre := (guard_success _ _ _ _ hp).1
  simp only [Bool.and_eq_true] at pre
  have height := (guard_success _ _ _ _ hd).1
  subst receipt
  subst specified
  subst left
  exact ⟨binding,(guard_success _ _ _ _ hi).1,pre.1,pre.2,rfl,rfl,of_decide_eq_true height,
    implementation,specification,w₇,w₈,w₈,specifiedCount,w₉,w₉,w₁₀,w₁₀,w₁₁,w₁₂,
    (lift_success _ _ _ _ him).1,(lift_success _ _ _ _ hsp).1,he,hse,ha,hs,hw⟩

/-- A complete fresh prefix trace starts from no receipts. Each node exposes
its own actual body check, rather than assuming the dependency matrices sound. -/
inductive CheckedChain : List Receipt → List (Input × Binding) → List Receipt → Prop
  | nil (before) : CheckedChain before [] before
  | cons (before input binding rest receipt final work left)
      (checked : (checkEntry before input binding).run work = (.ok receipt,left))
      (remaining : CheckedChain (before ++ [receipt]) rest final) :
      CheckedChain before ((input,binding)::rest) final

theorem fold_checked (pairs : List (Input × Binding)) (before final : List Receipt) (work left : Nat)
    (ok : (pairs.foldlM (fun previous (input,binding) => do
      let checked ← checkEntry previous input binding
      return previous ++ [checked]) before).run work = (.ok final,left)) :
    CheckedChain before pairs final := by
  induction pairs generalizing before work with
  | nil =>
    simp only [List.foldlM_nil] at ok
    rw [(pure_success _ _ _ _ ok).1]
    exact .nil _
  | cons pair pairs ih =>
    simp only [List.foldlM_cons] at ok
    obtain ⟨next,w₁,hn,hr⟩ := bind_success _ _ _ _ _ ok
    obtain ⟨receipt,w₂,hc,h⟩ := bind_success _ _ _ _ _ hn
    have same := (pure_success _ _ _ _ h).1
    subst next
    exact .cons _ _ _ _ _ _ work w₂ hc (ih _ w₁ hr)

theorem checkAll_fresh (inputs : List Input) (bindings : List Binding) (receipts : List Receipt)
    (work left : Nat) (ok : (checkAll inputs bindings).run work = (.ok receipts,left)) :
    inputs.length = bindings.length ∧ CheckedChain [] (inputs.zip bindings) receipts := by
  obtain ⟨_,middle,hg,h⟩ := bind_success _ _ _ _ _ ok
  have limits := (guard_success _ _ _ _ hg).1
  simp only [Bool.and_eq_true,beq_iff_eq] at limits
  exact ⟨limits.1,fold_checked _ _ _ _ _ h⟩

theorem CheckedChain.bindings (before final : List Receipt) (pairs : List (Input × Binding))
    (chain : CheckedChain before pairs final) : pairs.map Prod.fst = pairs.map Prod.snd := by
  induction chain with
  | nil => rfl
  | cons before input binding rest receipt final work left checked remaining ih =>
    simp only [List.map_cons,(checkEntry_conditions _ _ _ _ _ _ checked).1,ih]

theorem CheckedChain.inputs (before final : List Receipt) (pairs : List (Input × Binding))
    (chain : CheckedChain before pairs final) :
    final.map (·.input) = before.map (·.input) ++ pairs.map Prod.fst := by
  induction chain with
  | nil => simp
  | cons before input binding rest receipt final work left checked remaining ih =>
    have same := (checkEntry_conditions _ _ _ _ _ _ checked).2.2.2.2.1
    simpa [same,List.map_append,List.append_assoc] using ih

theorem inspect_fresh (inputs : List Input) (bindings : List Binding) (program : Program)
    (required actual : Matrix) (work left : Nat)
    (ok : (inspect inputs bindings program required).run work = (.ok actual,left)) :
    actual = required ∧ ∃ receipts a b c d,
      (checkAll inputs bindings).run a = (.ok receipts,b) ∧
      (ProtectedEvaluation.reconstruct (receipts.map Receipt.dependency) program).run c = (.ok actual,d) := by
  obtain ⟨receipts,w₁,hc,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨read,w₂,hr,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨result,w₃,ha,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₄,hg,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  have req := (matrixRead_value _ _ _ _ hr).1
  have eq := beq_iff_eq.mp (guard_success _ _ _ _ hg).1
  subst_vars
  exact ⟨rfl,receipts,work,w₁,w₂,w₃,hc,ha⟩

end QleisliKernel.Raw.Function
