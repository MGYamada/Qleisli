import QleisliKernel.Raw.Instrument
import QleisliKernel.ObservationBinding
import QleisliKernel.Semantics.ObservingFunction

/-! Fresh full-body function graphs with closed classical branches. All arms
are checked before closed selection; phase and every binding byte matter.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Raw.BranchFunction
open Semantics.Exact Semantics.Finite Semantics.Observation Semantics.ObservingFunction Finite

def same (a b : Input) : Bool :=
  a.signature == b.signature && ObservationBinding.program a.implementation b.implementation &&
    ObservationBinding.program a.specification b.specification && a.identity == b.identity

theorem same_sound (a b : Input) (ok : same a b = true) : a = b := by
  simp only [same,Bool.and_eq_true,beq_iff_eq] at ok
  rcases ok with ⟨⟨⟨signature,implementation⟩,specification⟩,identity⟩
  have hi := ObservationBinding.program_sound _ _ implementation
  have hs := ObservationBinding.program_sound _ _ specification
  cases a; cases b; simp_all

/-- Original vectors and both arm totals have the existing finite capacities. -/
def preflightOps (fuel : Nat) : List Op → Option (Nat × Nat) :=
  Nat.rec (fun _ => none) (fun _ recurse ops => do
    let counts ← ops.foldlM (fun (count,steps) op => do
      let added ← match op with
      | .pure operation => do
        if !Raw.Function.operationBounded operation then none else
          some (0,(Raw.Function.suppliedSteps operation).length + match operation with
            | .quantumIf _ _ _ _ zero one => zero.length + one.length | _ => 0)
      | .measure _ _ | .reset _ _ _ | .discard _ => none
      | .branch _ left right quantum classical => do
        if !(quantum.length ≤ 1024 && classical.length ≤ 1024 &&
            quantum.all (fun phi => phi.wires.length ≤ 6)) then none else do
          let a ← recurse left
          let b ← recurse right
          some (a.1+b.1,a.2+b.2)
      | _ => some (0,0)
      let next := (count+1+added.1,steps+added.2)
      if next.1 ≤ 1024 && next.2 ≤ 1024 then some next else none) (0,0)
    return counts) fuel

def preflight (signature : Basis) (program : Program) : Bool :=
  basisValid signature && program.effect == .unitary && program.inputs.length == 1 &&
    program.outputs.length == 1 && program.classicalInputs.isEmpty && program.classicalOutputs.isEmpty &&
    ((program.inputs[0]?).map (fun port => port.bits == width signature && port.wires.length == width signature)).getD false &&
    (preflightOps 33 program.operations).isSome

def selected (fuel : Nat) : List Event → Instrument.Values → WorkM (Instrument.Values × List Semantics.Raw.Event) :=
  Nat.rec (fun _ _ => throw .limit) (fun _ recurse events initial =>
    events.foldlM (fun (values,steps) event => do
      exactWork (Exact.charge 1)
      match event with
      | .pure event => pure (values,steps ++ [event])
      | .erase _ _ _ => throw .request
      | .classical expr output => do
        let value ← Instrument.expression values expr
        pure (values ++ [(output,value)],steps)
      | .branch condition left right phis => do
        let choice ← Instrument.lookup values condition
        let (values,added) ← recurse (if choice then left else right) values
        let merged ← Instrument.mergeClassical choice phis ⟨values,[],⟨0,0,[]⟩⟩
        pure (merged.values,steps ++ added)) (initial,[])) fuel

/-- Frame permutations rename subsequent axes; charge a physical route only
for the final composite permutation, matching original function extraction. -/
def expansion (dependencies : List Nat) (bits : Nat) (events : List Semantics.Raw.Event) : WorkM Nat := do
  let (raw,expanded,route) ← events.foldlM (fun (raw,expanded,route) event => do
    match event with
    | .reorder _ axes => pure (raw,expanded,axes.map (fun axis => route[axis]?.getD 0))
    | _ => do
      let steps ← lift (readOption (Semantics.Function.extracted event))
      let raw := raw + steps.length
      guard (raw ≤ 1024) .limit
      let expanded ← steps.foldlM (Raw.Function.countStep dependencies) expanded
      pure (raw,expanded,route)) (0,0,List.range bits)
  let permutation := if route == List.range bits then 0 else 1
  guard (raw+permutation ≤ 1024 && expanded+permutation ≤ 1000000) .limit
  return max (expanded+permutation) 1

def depth (before : List Receipt) (input : Input) : Nat :=
  1 + ((references 65 input.implementation.operations ++ references 65 input.specification.operations).map
    (fun index => (before[index]?.map (·.depth)).getD 0)).foldl max 0

def reconstruct (dependencies : List Dependency) (program : Program) : WorkM Matrix := do
  let checked ← Observation.verify dependencies program
  guard (checked.prepared.inputBits ≤ 6 && checked.state.quantum.frame.length ≤ 6) .limit
  let initial ← lift (arithmetic (Exact.Matrix.identity (2^checked.prepared.inputBits)))
  let histories ← Instrument.runEvents dependencies 65 checked.prepared.events ⟨[],[],initial⟩
  let history ← lift (readOption histories[0]?)
  guard (histories.length == 1 && history.hidden.isEmpty &&
    history.operator.rows == 2^checked.state.quantum.frame.length &&
    history.operator.cols == 2^checked.prepared.inputBits)
  return history.operator

def checkEntry (before : List Receipt) (input : Input) (binding : Binding) : WorkM Receipt := do
  guard (same input binding) .request
  guard (Raw.Function.identityValid input.identity) .limit
  exactWork (Exact.charge (Raw.Function.identityBytes input.identity))
  guard (preflight input.signature input.implementation && preflight input.signature input.specification) .limit
  let height := depth before input
  guard (height ≤ 32) .limit
  let dependencies := before.map Receipt.dependency
  let impl ← lift (readOption (Semantics.Observation.read input.implementation))
  let spec ← lift (readOption (Semantics.Observation.read input.specification))
  let (_,implementation) ← selected 65 impl.events []
  let (_,specification) ← selected 65 spec.events []
  let expanded ← expansion (before.map (·.expandedSteps)) impl.inputBits implementation
  let _ ← expansion (before.map (·.expandedSteps)) spec.inputBits specification
  let actual ← reconstruct dependencies input.implementation
  let specified ← reconstruct dependencies input.specification
  guard (actual == specified) .equation
  wholeSpace actual
  return ⟨input,actual,height,expanded⟩

def checkAll (inputs : List Input) (bindings : List Binding) : WorkM (List Receipt) := do
  guard (inputs.length == bindings.length && inputs.length ≤ 65536) .limit
  (inputs.zip bindings).foldlM (fun before (input,binding) => do
    let receipt ← checkEntry before input binding
    pure (before ++ [receipt])) []

theorem reconstruct_execution (dependencies : List Dependency) (program : Program) (actual : Matrix)
    (work left : Nat) (ok : (reconstruct dependencies program).run work = (.ok actual,left)) :
    ∃ checked initial history a b c d,
      (Observation.verify dependencies program).run a = (.ok checked,b) ∧
      Exact.Matrix.identity (2^checked.prepared.inputBits) = .ok initial ∧
      (Instrument.runEvents dependencies 65 checked.prepared.events ⟨[],[],initial⟩).run c = (.ok [history],d) ∧
      history.operator = actual ∧ history.hidden = [] := by
  obtain ⟨checked,w₁,hc,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨initial,w₃,hi,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨histories,w₄,he,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨history,w₅,hh,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₆,hg,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst actual
  have guards := (guard_success _ _ _ _ hg).1
  simp only [Bool.and_eq_true,beq_iff_eq,List.isEmpty_iff] at guards
  have lookup := (lift_success _ _ _ _ hh).1
  have list : histories = [history] := by
    cases histories with
    | nil => cases lookup
    | cons x xs =>
      have hx : x = history := by simpa [readOption] using lookup
      have empty : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using guards.1.1.1)
      simp [hx,empty]
  rw [list] at he
  exact ⟨checked,initial,history,work,w₁,w₃,w₄,hc,
    arithmetic_success _ _ (lift_success _ _ _ _ hi).1,he,rfl,guards.1.1.2⟩

theorem expansion_bound (dependencies : List Nat) (bits : Nat) (events : List Semantics.Raw.Event)
    (actual work left : Nat) (ok : (expansion dependencies bits events).run work = (.ok actual,left)) :
    actual ≤ 1000000 := by
  obtain ⟨counts,middle,_,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,after,hg,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst actual
  have limits := (guard_success _ _ _ _ hg).1
  simp only [Bool.and_eq_true,decide_eq_true_eq] at limits
  exact Nat.max_le.mpr ⟨limits.2,by decide⟩

theorem checkEntry_conditions (before : List Receipt) (input : Input) (binding : Binding)
    (receipt : Receipt) (work left : Nat)
    (ok : (checkEntry before input binding).run work = (.ok receipt,left)) :
    input = binding ∧ receipt.input = input ∧
    preflight input.signature input.implementation = true ∧ preflight input.signature input.specification = true ∧
    Raw.Function.identityValid input.identity = true ∧ receipt.depth = depth before input ∧
    receipt.depth ≤ 32 ∧ receipt.expandedSteps ≤ 1000000 ∧
    ∃ a b c d e f,
      (reconstruct (before.map Receipt.dependency) input.implementation).run a = (.ok receipt.meaning,b) ∧
      (reconstruct (before.map Receipt.dependency) input.specification).run c = (.ok receipt.meaning,d) ∧
      (wholeSpace receipt.meaning).run e = (.ok (),f) := by
  obtain ⟨_,w₁,hb,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,hi,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₃,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₄,hp,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₅,hd,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨impl,w₆,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨spec,w₇,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨implementation,w₈,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨specification,w₉,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨expanded,w₁₀,he,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₁₁,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨actual,w₁₂,ha,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨specified,w₁₃,hs,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₁₄,hg,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₁₅,hw,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  have eq := beq_iff_eq.mp (guard_success _ _ _ _ hg).1
  have pre := (guard_success _ _ _ _ hp).1
  simp only [Bool.and_eq_true] at pre
  subst receipt
  subst specified
  exact ⟨same_sound _ _ (guard_success _ _ _ _ hb).1,rfl,pre.1,pre.2,
    (guard_success _ _ _ _ hi).1,rfl,of_decide_eq_true (guard_success _ _ _ _ hd).1,
    expansion_bound _ _ _ _ _ _ he,w₁₁,w₁₂,w₁₂,w₁₃,w₁₄,w₁₅,ha,hs,hw⟩

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
  have guard := (guard_success _ _ _ _ hg).1
  simp only [Bool.and_eq_true,beq_iff_eq] at guard
  exact ⟨guard.1,fold_checked _ _ _ _ _ h⟩

theorem CheckedChain.inputs {before pairs final} (chain : CheckedChain before pairs final) :
    final.map (·.input) = before.map (·.input) ++ pairs.map Prod.fst := by
  induction chain with
  | nil => simp
  | cons before input binding rest receipt final work left checked remaining ih =>
    have same := (checkEntry_conditions _ _ _ _ _ _ checked).2.1
    simpa [same,List.map_append,List.append_assoc] using ih

theorem CheckedChain.bindings {before pairs final} (chain : CheckedChain before pairs final) :
    pairs.map Prod.fst = pairs.map Prod.snd := by
  induction chain with
  | nil => rfl
  | cons before input binding rest receipt final work left checked remaining ih =>
    simp [(checkEntry_conditions _ _ _ _ _ _ checked).1,ih]

end QleisliKernel.Raw.BranchFunction
