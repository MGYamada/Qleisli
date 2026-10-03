import QleisliKernel.Raw.Observation
import QleisliKernel.Raw.Ownership

/-! Actual observing verification establishes independent linear ResourceSafe
for every original operation and both arms, with no Rust/checker premise in
that judgment. Effect/instrument soundness and quantitative costs are separate.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Raw.Observation
open Semantics.Raw Semantics.Observation Semantics.Finite Finite
open Raw.Ownership (view)

private theorem classical_quantum (state next : State) (id : Nat)
    (ok : insertClassical state id = .ok next) : next.quantum = state.quantum := by
  obtain ⟨_,_,h⟩ := except_bind_success _ _ _ ok
  have same := Except.ok.inj h
  subst next
  rfl

private theorem classical_fold_quantum {A : Type} (items : List A) (id : A → Nat) (state next : State)
    (ok : items.foldlM (fun state item => insertClassical state (id item)) state = .ok next) :
    next.quantum = state.quantum := by
  induction items generalizing state with
  | nil => have same := Except.ok.inj ok; subst next; rfl
  | cons item items ih =>
    simp only [List.foldlM_cons] at ok
    obtain ⟨middle,hi,rest⟩ := except_bind_success _ _ _ ok
    exact (ih middle rest).trans (classical_quantum _ _ _ hi)

private theorem consume_ownership (state next : State) (input : Nat) (port : Port)
    (ok : consume state input = .ok (port,next)) :
    Semantics.Ownership.Erase (view state.quantum) input port (view next.quantum) := by
  obtain ⟨⟨found,after⟩,hf,h⟩ := except_bind_success _ _ _ ok
  have same := Except.ok.inj h
  cases same
  have taken := Raw.Ownership.take_state _ _ _ _ hf
  exact ⟨List.mem_of_find?_eq_some taken.1,beq_iff_eq.mp (List.find?_some (p := fun p : Port => p.token == input) taken.1),by rw [taken.2]; rfl⟩

private theorem phi_ownership (left right : Raw.State) (phis : List QuantumPhi)
    (ok : phiValid left right phis = true) : Semantics.Ownership.Phi (view left) (view right) phis := by
  simp only [phiValid,Bool.and_eq_true,List.all_eq_true,List.contains_iff_mem,beq_iff_eq] at ok
  rcases ok with ⟨⟨⟨⟨⟨⟨ld,rd⟩,lc⟩,rc⟩,lv⟩,rv⟩,shape⟩
  refine ⟨Raw.Ownership.unique_nodup _ ld,Raw.Ownership.unique_nodup _ rd,lc,rc,lv,rv,?_⟩
  intro phi member
  have good := shape phi member
  cases hl : left.live.find? (fun port => port.token == phi.thenToken) with
  | none => simp [hl] at good
  | some a =>
    cases hr : right.live.find? (fun port => port.token == phi.elseToken) with
    | none => simp [hl,hr] at good
    | some b =>
      simp only [hl,hr,Bool.and_eq_true,beq_iff_eq] at good
      exact ⟨a,b,List.mem_of_find?_eq_some hl,List.mem_of_find?_eq_some hr,
        beq_iff_eq.mp (List.find?_some (p := fun p : Port => p.token == phi.thenToken) hl),beq_iff_eq.mp (List.find?_some (p := fun p : Port => p.token == phi.elseToken) hr),good⟩

/-- Every successful original instruction has a resource derivation. Nested
arms use the induction hypothesis for the actual smaller-depth checker. -/
theorem checkStep_ownership (dependencies : List Dependency)
    (recurse : State → List Semantics.Observation.Op → WorkM State)
    (sound : ∀ state ops next work left, (recurse state ops).run work = (.ok next,left) →
      Semantics.Ownership.Run (view state.quantum) ops (view next.quantum))
    (state next : State) (op : Semantics.Observation.Op) (work left : Nat)
    (ok : (checkStep dependencies recurse state op).run work = (.ok next,left)) :
    Semantics.Ownership.Valid (view state.quantum) ∧
    Semantics.Ownership.Step (view state.quantum) op (view next.quantum) ∧
    Semantics.Ownership.Valid (view next.quantum) := by
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,_,hi,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨result,a,hbody,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,hf,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst next
  have final := (guard_success _ _ _ _ hf).1
  simp only [Bool.and_eq_true] at final
  refine ⟨Raw.Ownership.valid _ (guard_success _ _ _ _ hi).1,?_,Raw.Ownership.valid _ final.1⟩
  cases op with
  | pure operation =>
    obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ hbody
    obtain ⟨transition,_,ht,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
    have same := (pure_success _ _ _ _ h).1
    subst result
    exact .pure _ _ _ (Raw.Ownership.pure _ _ _ _ (lift_success _ _ _ _ ht).1)
  | measure input output =>
    obtain ⟨⟨port,consumed⟩,_,hc,h⟩ := bind_success _ _ _ _ _ hbody
    obtain ⟨_,_,hb,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨next,_,hn,h⟩ := bind_success _ _ _ _ _ h
    have same := (pure_success _ _ _ _ h).1
    subst result
    have quantum := classical_quantum _ _ _ (lift_success _ _ _ _ hn).1
    have erased := consume_ownership _ _ _ _ (lift_success _ _ _ _ hc).1
    exact .measure _ _ _ _ _ (quantum ▸ erased) (beq_iff_eq.mp (guard_success _ _ _ _ hb).1)
  | reset input output wire =>
    obtain ⟨⟨port,consumed⟩,_,hc,h⟩ := bind_success _ _ _ _ _ hbody
    obtain ⟨_,_,hb,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨quantum,_,hq,h⟩ := bind_success _ _ _ _ _ h
    have same := (pure_success _ _ _ _ h).1
    subst result
    exact .reset _ _ _ _ _ _ _ (consume_ownership _ _ _ _ (lift_success _ _ _ _ hc).1)
      (beq_iff_eq.mp (guard_success _ _ _ _ hb).1) (Raw.Ownership.input _ _ _ (lift_success _ _ _ _ hq).1)
  | discard input =>
    obtain ⟨⟨port,consumed⟩,_,hc,h⟩ := bind_success _ _ _ _ _ hbody
    have same := (pure_success _ _ _ _ h).1
    subst result
    have erased := consume_ownership state consumed input port (lift_success _ _ _ _ hc).1
    exact .discard _ _ _ _ erased
  | constant value output =>
    have quantum := classical_quantum _ _ _ (lift_success _ _ _ _ hbody).1
    rw [quantum]
    exact .constant _ _ _
  | not input output =>
    obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ hbody
    have quantum := classical_quantum _ _ _ (lift_success _ _ _ _ h).1
    rw [quantum]
    exact .not _ _ _
  | xor l r output | and l r output =>
    obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ hbody
    have quantum := classical_quantum _ _ _ (lift_success _ _ _ _ h).1
    rw [quantum]
    first | exact .xor _ _ _ _ | exact .and _ _ _ _
  | branch condition thenOps elseOps quantum classical =>
    obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ hbody
    obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨thenState,b,ht,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨elseState,c,he,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨_,_,hp,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨merged,_,hm,h⟩ := bind_success _ _ _ _ _ h
    have outputs := classical_fold_quantum _ (fun phi : ClassicalPhi => phi.output) _ _ (lift_success _ _ _ _ h).1
    have leftRun := sound _ _ _ _ _ ht
    have rightRun := sound _ _ _ _ _ he
    have merge : Semantics.Ownership.Inputs
        (Semantics.Ownership.mergeBase (view elseState.quantum)) (Semantics.Ownership.phiPorts quantum)
        (view merged) := by
      apply Raw.Ownership.inputs _
        {elseState.quantum with live := [],frame := [],iso := thenState.quantum.iso || elseState.quantum.iso} merged
      simpa only [Semantics.Ownership.phiPorts,List.foldlM_map] using (lift_success _ _ _ _ hm).1
    rw [outputs]
    exact .branch _ _ _ _ _ _ _ _ _ leftRun rightRun (phi_ownership _ _ _ (guard_success _ _ _ _ hp).1) merge

private theorem fold_ownership (dependencies : List Dependency)
    (recurse : State → List Semantics.Observation.Op → WorkM State)
    (sound : ∀ state ops next work left, (recurse state ops).run work = (.ok next,left) →
      Semantics.Ownership.Run (view state.quantum) ops (view next.quantum))
    (ops : List Semantics.Observation.Op) (state next : State) (work left : Nat)
    (valid : Semantics.Ownership.Valid (view next.quantum))
    (ok : (ops.foldlM (checkStep dependencies recurse) state).run work = (.ok next,left)) :
    Semantics.Ownership.Run (view state.quantum) ops (view next.quantum) := by
  induction ops generalizing state work with
  | nil =>
    have same := (pure_success _ _ _ _ ok).1
    subst next
    exact .nil _ valid
  | cons op ops ih =>
    simp only [List.foldlM_cons] at ok
    obtain ⟨middle,b,head,rest⟩ := bind_success _ _ _ _ _ ok
    have step := checkStep_ownership _ _ sound _ _ _ _ _ head
    exact .cons _ _ _ _ _ step.1 step.2.1 (ih middle b rest)

theorem checkOps_ownership (dependencies : List Dependency) (fuel : Nat)
    (state next : State) (ops : List Semantics.Observation.Op) (work left : Nat)
    (ok : (checkOps dependencies fuel state ops).run work = (.ok next,left)) :
    Semantics.Ownership.Run (view state.quantum) ops (view next.quantum) := by
  induction fuel generalizing state next ops work left with
  | zero => cases ok
  | succ fuel ih =>
    obtain ⟨result,b,hops,h⟩ := bind_success _ _ _ _ _ ok
    obtain ⟨_,_,hg,h⟩ := bind_success _ _ _ _ _ h
    have same := (pure_success _ _ _ _ h).1
    subst next
    have good := (guard_success _ _ _ _ hg).1
    simp only [Bool.and_eq_true] at good
    exact fold_ownership _ _ (fun state ops next work left ok => ih state next ops work left ok)
      ops state result work b (Raw.Ownership.valid _ good.1) hops

theorem returned_ownership (program : Semantics.Observation.Program) (state : State)
    (ok : outputValid program state = true) : Semantics.Ownership.Returned (view state.quantum) program.outputs := by
  have good : Raw.outputValid ⟨program.inputs,[],program.outputs,program.effect⟩ state.quantum = true := by
    simp only [outputValid,Bool.and_eq_true] at ok
    exact ok.1.1.1
  have coverage := Raw.output_coverage _ _ good
  simp only [Raw.outputValid,Bool.and_eq_true,beq_iff_eq] at good
  exact ⟨Raw.Ownership.unique_nodup _ good.1.1.1.1,good.1.1.1.2,coverage.1,coverage.2.1⟩

/-- All nineteen ordinary raw constructors, all nested arms and every ownership
boundary follow the independent rules. No finite algorithm request is required. -/
theorem verify_resourceSafe (dependencies : List Dependency) (program : Semantics.Observation.Program)
    (checked : Checked) (work left : Nat)
    (ok : (verify dependencies program).run work = (.ok checked,left)) :
    Semantics.Ownership.ResourceSafe program := by
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨quantum,_,hq,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨initial,a,hi,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨state,b,hops,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,hout,_⟩ := bind_success _ _ _ _ _ h
  have initialQuantum := classical_fold_quantum _ id _ _ (lift_success _ _ _ _ hi).1
  have inputs := Raw.Ownership.inputs _ _ _ (lift_success _ _ _ _ hq).1
  refine ⟨view initial.quantum,view state.quantum,?_,checkOps_ownership _ _ _ _ _ _ _ hops,
    returned_ownership _ _ (guard_success _ _ _ _ hout).1⟩
  simpa only [initialQuantum] using inputs

/-- Refactoring preserves the former literal action at every fuel, input and
work budget, including failures and their remaining work. -/
theorem checkOps_projection (dependencies : List Dependency) (fuel : Nat) :
    checkOps dependencies fuel =
  Nat.rec (fun _ _ => throw .limit) (fun _ recurse initial operations => do
    let result ← operations.foldlM (fun state op => do
      exactWork (Exact.charge 1)
      guard (Raw.stateValid state.quantum)
      let next ← match op with
      | .pure operation => do
        exactWork (Exact.charge (Raw.rawFields ⟨[],[operation],[],.unitary⟩))
        let next ← lift (Raw.step (dependencies.map (·.signature)) state.quantum operation)
        let _ ← next.events.foldlM (fun _ event => Raw.Pure.eventCheck dependencies event) ()
        pure {state with quantum := next.state}
      | .measure input output => do
        let (port,next) ← lift (consume state input)
        guard (port.bits == 1)
        let next ← lift (insertClassical next output)
        pure {next with observe := true}
      | .reset input output wire => do
        let (port,next) ← lift (consume state input)
        guard (port.bits == 1)
        let quantum ← lift (Raw.input next.quantum ⟨output,[wire],1⟩)
        pure {next with quantum,observe := true}
      | .discard input => do
        let (_,next) ← lift (consume state input)
        pure {next with observe := true}
      | .constant _ output => lift (insertClassical state output)
      | .not input output => do
        guard (visible state input)
        lift (insertClassical state output)
      | .xor left right output | .and left right output => do
        guard (visible state left && visible state right)
        lift (insertClassical state output)
      | .branch condition thenOps elseOps quantum classical => do
        exactWork (Exact.charge (4*quantum.length + (quantum.map (fun phi => phi.wires.length)).sum + 3*classical.length))
        guard (visible state condition)
        let leftEntry := enter state
        let left ← recurse leftEntry thenOps
        let left := leave state.scope leftEntry.scope left
        let rightEntry := enter (restore state left)
        let right ← recurse rightEntry elseOps
        let right := leave state.scope rightEntry.scope right
        guard (phiValid left.quantum right.quantum quantum)
        -- All phi operands are resolved before ANY phi output is inserted.
        guard (classical.all fun phi => visibleArm right leftEntry.scope phi.thenId &&
          visibleArm right rightEntry.scope phi.elseId)
        let base : Raw.State := {right.quantum with
          live := [],frame := [],iso := left.quantum.iso || right.quantum.iso}
        let merged ← lift (quantum.foldlM (fun q phi => Raw.input q ⟨phi.output,phi.wires,phi.wires.length⟩) base)
        let next := {right with quantum := merged,observe := left.observe || right.observe}
        lift (classical.foldlM (fun next phi => insertClassical next phi.output) next)
      guard (Raw.stateValid next.quantum && history state next)
      pure next) initial
    guard (Raw.stateValid result.quantum && history initial result)
    return result) fuel := by
  unfold checkOps
  congr 1
  funext depth recurse initial operations
  apply congrArg (fun action : WorkM State => action >>= fun result => do
    guard (Raw.stateValid result.quantum && history initial result)
    pure result)
  apply congrArg (fun step : State → Semantics.Observation.Op → WorkM State => operations.foldlM step initial)
  funext state op
  cases op <;> simp only [checkStep,checkAction,bind_assoc,pure_bind]

end QleisliKernel.Raw.Observation
